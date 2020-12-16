/*
 * polytracker_tracing.h
 *
 *  Created on: Jul 3, 2020
 *      Author: Evan Sultanik
 */
#ifndef POLYTRACKER_INCLUDE_POLYTRACKER_TRACING_H_
#define POLYTRACKER_INCLUDE_POLYTRACKER_TRACING_H_

#include <atomic>
#include <functional>
#include <list>
#include <stack>
#include <string.h>
#include <string>
#include <thread>
#include <unordered_map>
#include <unordered_set>
#include <vector>

#include "dfsan/dfsan_types.h"
#include "polytracker/basic_block_types.h"

namespace polytracker {

extern std::atomic<size_t> numTraceEvents;

struct TraceEvent {
  TraceEvent *previous;
  TraceEvent *next;
  const size_t eventIndex;
  TraceEvent();
  virtual ~TraceEvent() = default;
};

struct BasicBlockTrace {
  const char *fname;
  BBIndex index;
  size_t entryCount;

  bool operator==(const BasicBlockTrace &other) const {
    return (fname == other.fname /* these are globals, so it should be fine
                                  * to skip a string compare and just compare
                                  * pointers */
            && index == other.index && entryCount == other.entryCount);
  }

  bool operator<(const BasicBlockTrace &rhs) const {
    auto fnameCmp = strcmp(fname, rhs.fname);
    if (fnameCmp == 0) {
      // these BBs are in the same function
      if (index == rhs.index) {
        // they are the same BB, so compare their entry counter
        return entryCount < rhs.entryCount;
      } else {
        return index < rhs.index;
      }
    } else {
      return fnameCmp < 0;
    }
  }

  std::string str() const;
};

template <typename BB> struct BasicBlockTraceHasher {
  std::size_t operator()(BB bb) const {
    using std::hash;
    using std::size_t;
    using std::string;

    return (hash<uint64_t>()(bb.index) << 1) ^
           (hash<decltype(BasicBlockTrace::entryCount)>()(bb.entryCount) << 1);
  }
};

struct BasicBlockTraceComparator {
  std::size_t
  operator()(std::reference_wrapper<const BasicBlockTrace> lhs,
             std::reference_wrapper<const BasicBlockTrace> rhs) const {
    return lhs.get() < rhs.get();
  }
};

class FunctionCall;

struct BasicBlockEntry : public TraceEvent {
  const char *fname;
  BBIndex index;
  const size_t entryCount;
  BasicBlockType type;
  FunctionCall *function;

  BasicBlockEntry(const char *fname, BBIndex index, size_t entryCount,
                  BasicBlockType type)
      : fname(fname), index(index), entryCount(entryCount), type(type),
        function(nullptr) {}
  BasicBlockEntry(const char *fname, BBIndex index, BasicBlockType type)
      : BasicBlockEntry(fname, index, 1, type) {}

  operator BasicBlockTrace() const { return bb(); }

  BasicBlockTrace bb() const {
    return BasicBlockTrace{fname, index, entryCount};
  }

  std::string str() const { return BasicBlockTrace(*this).str(); }
};

struct FunctionReturn;
class Trace;

enum class CachedBool : uint_fast8_t {
  FALSE = 0,
  TRUE = 1,
  UNKNOWN = 128,
};

class FunctionCall : public TraceEvent {
  mutable CachedBool mConsumesBytes;

public:
  const char *fname;
  FunctionReturn *ret;

  FunctionCall(const char *fname)
      : mConsumesBytes(CachedBool::UNKNOWN), fname(fname), ret(nullptr) {}

  const BasicBlockEntry *getCaller() const {
    for (auto event = previous; event; event = event->previous) {
      if (auto bb = dynamic_cast<const BasicBlockEntry *>(event)) {
        return bb;
      }
    }
    return nullptr;
  }

  bool consumesBytes(const Trace &trace) const;
};

struct FunctionReturn : public TraceEvent {
  FunctionCall *call;
  BasicBlockEntry *returningTo;

  FunctionReturn(FunctionCall *call) : call(call), returningTo(nullptr) {
    if (call) {
      call->ret = this;
    }
  }
};

//Powers of 2 with 0 being unknown
enum ByteAccessType {
  UNKNOWN_ACCESS = 0,
  INPUT_ACCESS = 1,
  CMP_ACCESS = 2
};

//Bitfield where each bit represents some ByteAccessType
typedef uint8_t byte_access;

struct FunctionEvent : public TraceEvent {
  BBIndex index;
  //Continuation
  bool is_cont;
  FunctionEvent(BBIndex& index, bool cont) : index(index), is_cont(cont){}
};

class TraceEventStack;

class TraceEventStackFrame {
  FunctionCall *call;
  TraceEvent *head;
  // This keeps track of the last occurrence of each BB in this stack frame
  std::unordered_map<BBIndex, BasicBlockEntry *> lastOccurrences;

  friend class TraceEventStack;

  void push(TraceEvent *event) {
    head = event;
    if (auto bb = dynamic_cast<BasicBlockEntry *>(event)) {
      lastOccurrences[bb->index] = bb;
      bb->function = call;
    }
  }

public:
  TraceEventStackFrame(FunctionCall *call) : call(call), head(nullptr) {}
  TraceEventStackFrame() : TraceEventStackFrame(nullptr) {}
  operator bool() const { return head != nullptr; }
  bool empty() const { return head != nullptr; }
  constexpr FunctionCall *functionCall() const { return call; }
  constexpr TraceEvent *peek() const { return head; }
  BasicBlockEntry *lastOccurrence(BBIndex bb) const {
    auto bbe = lastOccurrences.find(bb);
    if (bbe == lastOccurrences.cend()) {
      return nullptr;
    } else {
      return bbe->second;
    }
  }
};

class TraceEventStack {
  std::stack<TraceEventStackFrame> stack;
  TraceEvent *mFirstEvent;
  TraceEvent *mLastEvent;
  size_t mNumEvents;

public:
  TraceEventStack() : mFirstEvent(nullptr), mLastEvent(nullptr), mNumEvents(0) {
    stack.emplace();
  }
  ~TraceEventStack() {
    auto event = mLastEvent;
    while (event) {
      auto toDelete = event;
      event = event->previous;
      delete toDelete;
    }
  }
  /* disallow copying to avoid the memory management headache
   * and avoid the runtime overhead of using shared pointers */
  TraceEventStack(const TraceEventStack &) = delete;
  operator bool() const { return peek(); }
  /**
   * This object will assume ownership of the memory pointed to by event.
   */
  inline void push(TraceEvent *event) {
    if (mLastEvent) {
      event->previous = mLastEvent;
      mLastEvent->next = event;
    } else {
      mFirstEvent = event;
    }
    mLastEvent = event;
    ++mNumEvents;
    stack.top().push(event);
  }
  inline void newFrame(FunctionCall *call) { stack.emplace(call); }
  template <typename T,
            typename std::enable_if<std::is_base_of<TraceEvent, T>::value>::type
                * = nullptr,
            typename... Ts>
  T *emplace(Ts &&... args) {
    auto t = new T(std::forward<Ts>(args)...);
    push(t);
    return t;
  }
  constexpr const TraceEventStackFrame &peek() const { return stack.top(); }
  bool pop() {
    if (stack.size() > 1) {
      stack.pop();
      return true;
    } else {
      return false;
    }
  }
  constexpr const TraceEvent *const firstEvent() const { return mFirstEvent; }
  constexpr const TraceEvent *const lastEvent() const { return mLastEvent; }
  constexpr size_t numEvents() const { return mNumEvents; }
};

class Trace {
  /* lastUsages maps canonical byte offsets to the last basic block trace
   * in which they were used */
  std::unordered_map<dfsan_label, const BasicBlockEntry *> lastUsages;
  std::unordered_map<const BasicBlockEntry *, std::list<dfsan_label>>
      lastUsagesByBB;
  static const std::list<dfsan_label> EMPTY_LIST;

public:
  //For function events, we can store runtime control flow and function events as a vector
  //To prevent creationg objects for functions that already exist, we re use func events 
  std::vector<FunctionEvent> functionEvents;
  //Maps index --> Labels --> access types. 
  std::unordered_map<uint32_t, std::unordered_map<dfsan_label, byte_access>> func_taint_labels;
  //BB Tracing
  std::unordered_map<std::thread::id, TraceEventStack> eventStacks;
  
  TraceEventStack &getStack(std::thread::id thread) {
    return eventStacks[std::this_thread::get_id()];
  }
  TraceEventStack *currentStack() {
    return &eventStacks[std::this_thread::get_id()];
  }
  const TraceEventStack *currentStack() const {
    auto stackIter = eventStacks.find(std::this_thread::get_id());
    if (stackIter != eventStacks.end()) {
      return &stackIter->second;
    } else {
      return nullptr;
    }
  }
  TraceEvent *lastEvent() const {
    if (auto stack = currentStack()) {
      return stack->peek().peek();
    } else {
      return nullptr;
    }
  }
  TraceEvent *secondToLastEvent() const {
    if (auto last = lastEvent()) {
      return last->previous;
    } else {
      return nullptr;
    }
  }
  /**
   * Returns the current basic block for the calling thread
   */
  const BasicBlockEntry *currentBB() const {
    for (auto event = lastEvent(); event; event = event->previous) {
      if (auto bbe = dynamic_cast<BasicBlockEntry *>(event)) {
        return bbe;
      } else if (dynamic_cast<FunctionCall *>(event)) {
        return nullptr;
      }
    }
    return nullptr;
  }
  void setLastUsage(dfsan_label canonicalByte, const BasicBlockEntry *bb) {
    const auto oldValue = lastUsages.find(canonicalByte);
    if (oldValue != lastUsages.cend()) {
      // We are updating the last usage,
      // so remove the old value from the reverse map
      lastUsagesByBB[oldValue->second].remove_if(
          [canonicalByte](dfsan_label b) { return b == canonicalByte; });
    }
    lastUsages[canonicalByte] = bb;
    lastUsagesByBB[bb].push_back(canonicalByte);
  }
  const BasicBlockEntry *getLastUsage(dfsan_label label) const {
    auto luIter = lastUsages.find(label);
    if (luIter != lastUsages.cend()) {
      return luIter->second;
    } else {
      return nullptr;
    }
  }
  decltype(lastUsages) taints() const { return lastUsages; }
  const std::list<dfsan_label> &taints(const BasicBlockEntry *bb) const {
    const auto ret = lastUsagesByBB.find(bb);
    if (ret == lastUsagesByBB.cend()) {
      return EMPTY_LIST;
    } else {
      return ret->second;
    }
  }
   FunctionEvent * currentFunc() {
    for (int i = functionEvents.size() - 1; i >= 0; i--) {
      if (auto func_event = dynamic_cast<FunctionEvent*>(&functionEvents[i])) {
        return func_event;
      }
    }
    return nullptr;
   }
  bool funcAddTaintLabel(const dfsan_label& some_label, ByteAccessType access) {
    if (auto func_event = currentFunc()) {
      auto& label_map = func_taint_labels[func_event->index.functionIndex()];
      label_map[some_label] |= access;
      return true;
    }
    return false;
  }
  bool getCallerFunc(int pos, BBIndex& index) {
    if (pos == 0) {
      return false;
    }
    if (FunctionEvent* func_event = dynamic_cast<FunctionEvent*>(&functionEvents[pos - 1])) {
      index = func_event->index;
      return true;
    }
    //Edge case for entrypoint.
    return false;
  }

};

} /* namespace polytracker */

#endif /* POLYTRACKER_INCLUDE_POLYTRACKER_TRACING_H_ */
