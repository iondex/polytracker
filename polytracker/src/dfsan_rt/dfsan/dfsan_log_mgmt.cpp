#include "dfsan/dfsan_log_mgmt.h"

#include <fstream>
#include <iomanip>
#include <iostream>
#include <set>
#include <stack>
#include <tuple>

#include "sanitizer_common/sanitizer_atomic.h"
#include "sanitizer_common/sanitizer_common.h"
#include "sanitizer_common/sanitizer_file.h"
#include "sanitizer_common/sanitizer_flag_parser.h"
#include "sanitizer_common/sanitizer_flags.h"
#include "sanitizer_common/sanitizer_libc.h"

using polytracker::BasicBlockEntry;
using polytracker::FunctionCall;
using polytracker::TraceEvent;

using namespace __dfsan;

// MAPPING MANAGER
taintMappingManager::taintMappingManager(char* shad_mem_ptr, char* forest_ptr) {
  shad_mem = shad_mem_ptr;
  forest_mem = forest_ptr;
}

taintMappingManager::~taintMappingManager() {}

// NOTE we might not need locks here, but just for now im adding them
taint_node_t* taintMappingManager::getTaintNode(dfsan_label label) {
  taint_mapping_lock.lock();
  taint_node_t* ret_node =
      (taint_node_t*)(forest_mem + (label * sizeof(taint_node_t)));
  taint_mapping_lock.unlock();
  return ret_node;
}

dfsan_label taintMappingManager::getTaintLabel(taint_node_t* node) {
  taint_mapping_lock.lock();
  dfsan_label ret_label = ((char*)node - forest_mem) / sizeof(taint_node_t);
  taint_mapping_lock.unlock();
  return ret_label;
}

void taintManager::logCompare(dfsan_label some_label) {
  if (some_label == 0) {
    return;
  }
  taint_prop_lock.lock();
  taint_node_t* curr_node = getTaintNode(some_label);
  std::thread::id this_id = std::this_thread::get_id();
  std::vector<std::string> func_stack = thread_stack_map[this_id];
  (function_to_cmp_bytes)[func_stack[func_stack.size() - 1]].insert(curr_node);
  (function_to_bytes)[func_stack[func_stack.size() - 1]].insert(curr_node);
  if (auto bb = trace.currentBB()) {
    // we are recording a full trace, and we know the current basic block
    if (curr_node->p1 == nullptr && curr_node->p2 == nullptr) {
      // this is a canonical label
      trace.setLastUsage(some_label, *bb);
    }
  }
  taint_prop_lock.unlock();
}

void taintManager::logOperation(dfsan_label some_label) {
  if (some_label == 0) {
    return;
  }
  taint_prop_lock.lock();
  taint_node_t* new_node = getTaintNode(some_label);
  std::thread::id this_id = std::this_thread::get_id();
  std::vector<std::string> func_stack = thread_stack_map[this_id];
  (function_to_bytes)[func_stack[func_stack.size() - 1]].insert(new_node);
  if (auto bb = trace.currentBB()) {
    // we are recording a full trace, and we know the current basic block
    if (new_node->p1 == nullptr && new_node->p2 == nullptr) {
      // this is a canonical label
      trace.setLastUsage(some_label, *bb);
    }
  }
  taint_prop_lock.unlock();
}

int taintManager::logFunctionEntry(char* fname) {
  taint_prop_lock.lock();
  std::string func_name = std::string(fname);
  std::string new_str = std::string(fname);
  std::thread::id this_id = std::this_thread::get_id();
  if (thread_stack_map[this_id].size() > 0) {
    std::string caller = (thread_stack_map)[this_id].back();
    (runtime_cfg)[new_str].insert(caller);
  } else {
    // This indicates the cfg entrypoint
    std::string caller = "";
    (runtime_cfg)[new_str].insert(caller);
  }
  (thread_stack_map)[this_id].push_back(new_str);
  if (recordTrace()) {
    trace.getStack(this_id).emplace<FunctionCall>();
  }
  taint_prop_lock.unlock();
  return thread_stack_map[this_id].size() - 1;
}

void taintManager::logFunctionExit() {
  taint_prop_lock.lock();
  std::thread::id this_id = std::this_thread::get_id();
  (thread_stack_map)[this_id].pop_back();
  if (recordTrace()) {
    auto& stack = trace.getStack(this_id);
    bool foundFunction = false;
    for (TraceEvent* event = stack.peek();
        event != nullptr;
        event = event->previous) {
      if (auto func = dynamic_cast<FunctionCall*>(event)) {
        foundFunction = true;
        stack.pop();
        break;
      }
      stack.pop();
    }
    if (!foundFunction) {
      std::cout
          << "Error finding matching function call in the event trace stack!"
          << std::endl;
    }
  }
  taint_prop_lock.unlock();
}

/**
 * This function will be called on the entry of every basic block.
 * It will only be called if taintManager::recordTrace() is true,
 * which will only be set if the POLYTRACE environment variable is set.
 */
void taintManager::logBBEntry(char *fname, BBIndex bbIndex) {
  taint_prop_lock.lock();
  auto currentBB = trace.currentBB();
  auto event = trace.currentStack()->emplace<BasicBlockEntry>(fname, bbIndex);
  if (currentBB) {
    trace.cfg.addChild(*currentBB, *event);
  } else {
    if (auto fCall = dynamic_cast<FunctionCall*>(trace.secondToLastEvent())) {
      // currentBB is the first basic block in a function call
      if (auto callingBB = dynamic_cast<BasicBlockEntry*>(fCall->previous)) {
        // we know the basic block that called fCall
        trace.cfg.addChild(*callingBB, *event);
      }
    }
  }
  taint_prop_lock.unlock();
}

void taintManager::logBBExit() {}

void taintManager::resetFrame(int* index) {
  taint_prop_lock.lock();
  if (index == nullptr) {
    std::cout
        << "Pointer to array index is null! Instrumentation error, aborting!"
        << std::endl;
    abort();
  }
  std::thread::id this_id = std::this_thread::get_id();
  // Get the function before we reset the frame (should be the one that called
  // longjmp)
  std::string caller_func = thread_stack_map[this_id].back();
  // Reset the frame
  thread_stack_map[this_id].resize(*index + 1);
  // Get the current function
  std::string curr_func = thread_stack_map[this_id].back();
  // Insert the function that called longjmp in cfg
  runtime_cfg[curr_func].insert(caller_func);
  taint_prop_lock.unlock();
}

void taintManager::addJsonVersion() {
  output_json["version"] = POLYTRACKER_VERSION;
}

void taintManager::addJsonRuntimeCFG() {
  std::unordered_map<std::string, std::unordered_set<std::string>>::iterator
      cfg_it;
  for (cfg_it = runtime_cfg.begin(); cfg_it != runtime_cfg.end(); cfg_it++) {
    json j_set(cfg_it->second);
    output_json["runtime_cfg"][cfg_it->first] = j_set;
  }
}

json escapeChar(int c) {
  std::stringstream s;
  s << '"';
  if (c >= 32 && c <= 126 && c != '"' && c != '\\') {
    s << (char)c;
  } else if (c != EOF) {
    s << "\\u" << std::hex << std::setw(4) << std::setfill('0') << c;
  }
  s << '"';
  return json::parse(s.str());
}

void taintManager::addJsonRuntimeTrace() {
  if (!recordTrace()) { return; }
  output_json["trace"]["method_map_fmt"] =
      "method_call_id, method_name, children";
  size_t id = 0;
  for (auto& bb : trace.cfg.bbs()) {
    json entry(std::make_tuple(id, bb.str(), trace.cfg.childIds(id)));
    output_json["trace"]["method_map"][std::to_string(id)] = entry;
    ++id;
  }
  output_json["trace"]["comparisons_fmt"] = "idx, char, method_call_id";
  std::vector<std::tuple<size_t, std::string, size_t>> cmps;
  /* FIXME: this is somewhat of a hack. The Mimid code's JSON input format
   * requires the character from each canonical byte of the input file, not
   * just its offset. Therefore, we open the file passed as POLYPATH and read
   * the bytes from it here.
   *
   * TODO: Find a better way to do this without re-opening the file!
   *
   * FIXME: This assumes that there is a single key in this->canonical_mapping
   * that corresponds to POLYPATH. If/when we support multiple taint sources,
   * this code will have to be updated!
   */
  if (canonical_mapping.size() < 1) {
    std::cout << "Unexpected number of taint sources: " <<
        canonical_mapping.size() << std::endl;
    exit(1);
  } else if (canonical_mapping.size() > 1) {
    std::cout << "Warning: More than one taint source found! The resulting "
        << "runtime trace will likely be incorrect!" << std::endl;
  }
  const std::string polyPath = canonical_mapping.begin()->first;
  auto polyPathFile = fopen(polyPath.c_str(), "rb");
  if (polyPathFile == nullptr) {
    std::cout << "Unable to open file \"" << polyPath << "\" for generating "
        << "the runtime trace!" << std::endl;
    exit(1);
  }
  for (const auto& taint : trace.taints()) {
    const auto& label = taint.first;
    const auto& lastBB = taint.second;
    if (fseek(polyPathFile, label - 1, SEEK_SET) == 0) {
      auto c = fgetc(polyPathFile);
      if (c != EOF) {
        cmps.emplace_back(label, escapeChar(c), trace.cfg.id(lastBB));
      }
    }
  }
  fclose(polyPathFile);
  output_json["trace"]["comparisons"] = cmps;
}

void taintManager::setOutputFilename(std::string out) { outfile = out; }

void taintManager::setTrace(bool doTrace) { this->doTrace = doTrace; }

void taintManager::outputRawTaintForest() {
  std::string forest_fname = outfile + "_forest.bin";
  FILE* forest_file = fopen(forest_fname.c_str(), "w");
  if (forest_file == NULL) {
    std::cout << "Failed to dump forest to file: " << forest_fname << std::endl;
    exit(1);
  }
  // Output file offset 0 will have data for node 1 etc etc
  taint_node_t* curr = nullptr;
  for (int i = 0; i < next_label; i++) {
    curr = getTaintNode(i);
    dfsan_label node_p1 = getTaintLabel(curr->p1);
    dfsan_label node_p2 = getTaintLabel(curr->p2);
    fwrite(&(node_p1), sizeof(dfsan_label), 1, forest_file);
    fwrite(&(node_p2), sizeof(dfsan_label), 1, forest_file);
  }
  fclose(forest_file);
}

void taintManager::addTaintSources() {
  auto name_target_map = getTargets();
  for (auto it = name_target_map.begin(); it != name_target_map.end(); it++) {
    targetInfo* targ_info = it->second;
    output_json["taint_sources"][it->first]["start_byte"] =
        targ_info->byte_start;
    output_json["taint_sources"][it->first]["end_byte"] = targ_info->byte_end;
    auto target_metadata = getMetadata(targ_info);
    if (!target_metadata.is_null()) {
      output_json["taint_sources"][it->first]["metadata"] = target_metadata;
    }
  }
}

void taintManager::addCanonicalMapping() {
  for (auto it = canonical_mapping.begin(); it != canonical_mapping.end();
       it++) {
    auto map_list = it->second;
    json canonical_map(map_list);
    output_json["canonical_mapping"][it->first] = canonical_map;
  }
}

void taintManager::addTaintedBlocks() {
  for (auto it = taint_bytes_processed.begin();
       it != taint_bytes_processed.end(); it++) {
    json tainted_chunks(it->second);
    output_json["tainted_input_blocks"][it->first] = tainted_chunks;
  }
}

void taintManager::outputRawTaintSets() {
  string_node_map::iterator it;
  // NOTE: Whenever the output JSON format changes, make sure to:
  //       (1) Up the version number in /polytracker/include/polytracker/polytracker.h; and
  //       (2) Add support for parsing the changes in /polytracker/polytracker.py
  addJsonVersion();
  addJsonRuntimeCFG();
  addJsonRuntimeTrace();
  addTaintSources();
  addCanonicalMapping();
  addTaintedBlocks();
  for (it = function_to_bytes.begin(); it != function_to_bytes.end(); it++) {
    auto set = it->second;
    std::set<dfsan_label> label_set;
    for (auto it = set.begin(); it != set.end(); it++) {
      label_set.insert(getTaintLabel(*it));
    }
    // Take label set and create a json based on source.
    json byte_set(label_set);
    output_json["tainted_functions"][it->first]["input_bytes"] = byte_set;
    if (function_to_cmp_bytes.find(it->first) != function_to_cmp_bytes.end()) {
      auto cmp_set = it->second;
      std::set<dfsan_label> cmp_label_set;
      for (auto it = cmp_set.begin(); it != cmp_set.end(); it++) {
        cmp_label_set.insert(getTaintLabel(*it));
      }
      json cmp_byte_set(cmp_label_set);
      output_json["tainted_functions"][it->first]["cmp_bytes"] = cmp_byte_set;
    }
  }
  std::string output_string = outfile + "_process_set.json";
  std::ofstream o(output_string);
  o << std::setw(4) << output_json;
  o.close();
}

void taintManager::output() {
  taint_prop_lock.lock();
  outputRawTaintForest();
  outputRawTaintSets();
  taint_prop_lock.unlock();
}

// PROPAGATION MANAGER
taintManager::taintManager(decay_val init_decay, char* shad_mem,
                           char* forest_ptr)
    : taintMappingManager(shad_mem, forest_ptr), taint_node_ttl(init_decay) {
  next_label = 1;
  doTrace = false;
}

taintManager::~taintManager() {}

dfsan_label taintManager::createReturnLabel(int file_byte_offset,
                                            std::string name) {
  taint_prop_lock.lock();
  dfsan_label ret_label = createCanonicalLabel(file_byte_offset, name);
  taint_bytes_processed[name].push_back(
      std::pair<int, int>(file_byte_offset, file_byte_offset));
  taint_prop_lock.unlock();
  return ret_label;
}

dfsan_label taintManager::createCanonicalLabel(int file_byte_offset,
                                               std::string name) {
  dfsan_label new_label = next_label;
  next_label += 1;
  checkMaxLabel(new_label);
  taint_node_t* new_node = getTaintNode(new_label);
  new_node->p1 = NULL;
  new_node->p2 = NULL;
  new_node->decay = taint_node_ttl;
  canonical_mapping[name].push_back(
      std::pair<dfsan_label, int>(new_label, file_byte_offset));
  return new_label;
}

bool taintManager::taintData(int fd, char* mem, int offset, int len) {
  taint_prop_lock.lock();
  if (!isTracking(fd)) {
    taint_prop_lock.unlock();
    return false;
  }
  targetInfo* targ_info = getTargetInfo(fd);
  taintTargetRange(mem, offset, len, targ_info->byte_start, targ_info->byte_end,
                   targ_info->target_name);
  taint_prop_lock.unlock();
  return true;
}

bool taintManager::taintData(FILE* fd, char* mem, int offset, int len) {
  taint_prop_lock.lock();
  if (!isTracking(fd)) {
    taint_prop_lock.unlock();
    return false;
  }
  targetInfo* targ_info = getTargetInfo(fd);
  taintTargetRange(mem, offset, len, targ_info->byte_start, targ_info->byte_end,
                   targ_info->target_name);
  taint_prop_lock.unlock();
  return true;
}
/*
 * This function is responsible for marking memory locations as tainted, and is
 * called when taint is processed by functions like read, pread, mmap, recv,
 * etc.
 *
 * Mem is a pointer to the data we want to taint
 * Offset tells us at what point in the stream/file we are in (before we read)
 * Len tells us how much we just read in
 * byte_start and byte_end are target specific options that allow us to only
 * taint specific regions like (0-100) etc etc
 *
 * If a byte is supposed to be tainted we make a new taint label for it, these
 * labels are assigned sequentially.
 *
 * Then, we keep track of what canonical labels map to what original file
 * offsets.
 *
 * Then we update the shadow memory region with the new label
 */
void taintManager::taintTargetRange(char* mem, int offset, int len,
                                    int byte_start, int byte_end,
                                    std::string name) {
  int curr_byte_num = offset;
  int taint_offset_start = -1, taint_offset_end = -1;
  bool processed_bytes = false;
  for (char* curr_byte = (char*)mem; curr_byte_num < offset + len;
       curr_byte_num++, curr_byte++) {
    // If byte end is < 0, then we don't care about ranges.
    if (byte_end < 0 ||
        (curr_byte_num >= byte_start && curr_byte_num <= byte_end)) {
      dfsan_label new_label = createCanonicalLabel(curr_byte_num, name);
      dfsan_set_label(new_label, curr_byte, TAINT_GRANULARITY);
      if (taint_offset_start == -1) {
        taint_offset_start = curr_byte_num;
        taint_offset_end = curr_byte_num;
      } else if (curr_byte_num > taint_offset_end) {
        taint_offset_end = curr_byte_num;
      }
      processed_bytes = true;
    }
  }
  if (processed_bytes) {
    taint_bytes_processed[name].push_back(
        std::pair<int, int>(taint_offset_start, taint_offset_end));
  }
}

dfsan_label taintManager::_unionLabel(dfsan_label l1, dfsan_label l2,
                                      decay_val init_decay) {
  dfsan_label ret_label = next_label;
  next_label += 1;
  checkMaxLabel(ret_label);
  taint_node_t* new_node = getTaintNode(ret_label);
  new_node->p1 = getTaintNode(l1);
  new_node->p2 = getTaintNode(l2);
  new_node->decay = init_decay;
  return ret_label;
}

dfsan_label taintManager::createUnionLabel(dfsan_label l1, dfsan_label l2) {
  taint_prop_lock.lock();
  // If sanitizer debug is on, this checks that l1 != l2
  DCHECK_NE(l1, l2);
  if (l1 == 0) {
    taint_prop_lock.unlock();
    return l2;
  }
  if (l2 == 0) {
    taint_prop_lock.unlock();
    return l1;
  }
  if (l1 > l2) {
    Swap(l1, l2);
  }
  // Quick union table check
  if ((union_table[l1]).find(l2) != (union_table[l1]).end()) {
    auto val = union_table[l1].find(l2);
    taint_prop_lock.unlock();
    return val->second;
  }
  // Check for max decay
  taint_node_t* p1 = getTaintNode(l1);
  taint_node_t* p2 = getTaintNode(l2);
  // This calculates the average of the two decays, and then decreases it by a
  // factor of 2.
  decay_val max_decay = (p1->decay + p2->decay) / 4;
  if (max_decay == 0) {
    taint_prop_lock.unlock();
    return 0;
  }
  dfsan_label label = _unionLabel(l1, l2, max_decay);
  (union_table[l1])[l2] = label;
  taint_prop_lock.unlock();
  return label;
}

void taintManager::checkMaxLabel(dfsan_label label) {
  if (label == MAX_LABELS) {
    std::cout << "ERROR: MAX LABEL REACHED, ABORTING!" << std::endl;
    // Cant exit due to our exit handlers
    abort();
  }
}

dfsan_label taintManager::getLastLabel() {
  taint_prop_lock.lock();
  dfsan_label last_label = next_label - 1;
  taint_prop_lock.unlock();
  return last_label;
}
