
#include "polytracker/taint.h"
#include "dfsan/dfsan.h"
#include "dfsan/dfsan_types.h"
#include "polytracker/logging.h"
#include "sanitizer_common/sanitizer_common.h"
#include <iostream>
#include <map>
#include <mutex>
#include <thread>
#include <unordered_map>
#include <vector>

extern decay_val taint_node_ttl;
#define TAINT_GRANULARITY 1

// This is the current taint label, 0 is the null label, start at 1.
std::atomic<dfsan_label> next_label{1};
// These structures do book keeping for shared execution state, like reading
// input chunks, the canonical mapping, and union table.
std::unordered_map<std::string, std::vector<std::pair<int, int>>>
    tainted_input_chunks;
std::unordered_map<std::string, std::unordered_map<dfsan_label, uint32_t>>
    canonical_mapping;
std::unordered_map<dfsan_label, std::unordered_map<dfsan_label, dfsan_label>>
    union_table;
std::mutex canonical_mapping_lock;
std::mutex tainted_input_chunks_lock;
std::mutex union_table_lock;

// FIXME We probably want strings here
std::unordered_map<int, std::string> fd_name_map;
std::unordered_map<std::string, std::pair<int, int>> track_target_name_map;
std::unordered_map<int, std::pair<int, int>> track_target_fd_map;
std::mutex track_target_map_lock;

auto getInitialSources()
    -> std::unordered_map<std::string, std::pair<int, int>> & {
  return track_target_name_map;
}

void checkMaxLabel(dfsan_label label) {
  if (label == MAX_LABELS) {
    std::cout << "ERROR: MAX LABEL REACHED, ABORTING!" << std::endl;
    // Cant exit due to our exit handlers
    abort();
  }
}

[[nodiscard]] bool isTrackingSource(const std::string &fd) {
  const std::lock_guard<std::mutex> guard(track_target_map_lock);
  if (track_target_name_map.find(fd) != track_target_name_map.end()) {
    return true;
  }
  return false;
}

[[nodiscard]] bool isTrackingSource(const int &fd) {
  const std::lock_guard<std::mutex> guard(track_target_map_lock);
  if (track_target_fd_map.find(fd) != track_target_fd_map.end()) {
    return true;
  }
  return false;
}

void closeSource(const std::string &fd) {
  const std::lock_guard<std::mutex> guard(track_target_map_lock);
  if (track_target_name_map.find(fd) != track_target_name_map.end()) {
    track_target_name_map.erase(fd);
  }
}

void closeSource(const int &fd) {
  const std::lock_guard<std::mutex> guard(track_target_map_lock);
  if (track_target_fd_map.find(fd) != track_target_fd_map.end()) {
    track_target_fd_map.erase(fd);
  }
}

// This will be called by polytracker to add new taint source info.
void addInitialTaintSource(std::string &fd, const int start, const int end,
                           std::string &name) {
  const std::lock_guard<std::mutex> guard(track_target_map_lock);
  track_target_name_map[fd] = std::make_pair(start, end);
}

void addInitialTaintSource(int fd, const int start, const int end,
                           std::string &name) {
  const std::lock_guard<std::mutex> guard(track_target_map_lock);
  track_target_fd_map[fd] = std::make_pair(start, end);
  track_target_name_map[name] = std::make_pair(start, end);
}

void addDerivedSource(std::string &track_path, const int &new_fd) {
  const std::lock_guard<std::mutex> guard(track_target_map_lock);
  track_target_fd_map[new_fd] = track_target_name_map[track_path];
  fd_name_map[new_fd] = track_path;
}

auto getSourceName(const int &fd) -> std::string & {
  const std::lock_guard<std::mutex> guard(track_target_map_lock);
  if (fd_name_map.find(fd) == fd_name_map.end()) {
    std::cerr << "Error: source name for fd " << fd << "not found" << std::endl;
    // Kill the run, somethings gone pretty wrong
    abort();
  }
  return fd_name_map[fd];
}

[[nodiscard]] inline auto getTargetTaintRange(const std::string &fd)
    -> std::pair<int, int> & {
  const std::lock_guard<std::mutex> guard(track_target_map_lock);
  return track_target_name_map[fd];
}
[[nodiscard]] inline auto getTargetTaintRange(const int &fd)
    -> std::pair<int, int> & {
  const std::lock_guard<std::mutex> guard(track_target_map_lock);
  return track_target_fd_map[fd];
}

[[nodiscard]] static inline dfsan_label
createCanonicalLabel(const int file_byte_offset, std::string &name) {
  dfsan_label new_label = next_label.fetch_add(1);
  checkMaxLabel(new_label);
  taint_node_t *new_node = getTaintNode(new_label);
  new_node->p1 = NULL;
  new_node->p2 = NULL;
  new_node->decay = taint_node_ttl;
  const std::lock_guard<std::mutex> guard(canonical_mapping_lock);
  canonical_mapping[name][new_label] = file_byte_offset;
  return new_label;
}

[[nodiscard]] dfsan_label createReturnLabel(const int file_byte_offset,
                                            std::string &name) {
  dfsan_label ret_label = createCanonicalLabel(file_byte_offset, name);
  const std::lock_guard<std::mutex> guard(tainted_input_chunks_lock);
  tainted_input_chunks[name].emplace_back(file_byte_offset, file_byte_offset);
  return ret_label;
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
void taintTargetRange(const char *mem, int offset, int len, int byte_start,
                      int byte_end, std::string &name) {
  int curr_byte_num = offset;
  int taint_offset_start = -1, taint_offset_end = -1;
  bool processed_bytes = false;
  // Iterate through the memory region marked as tatinted by [base + start, base
  // + end]
  for (char *curr_byte = (char *)mem; curr_byte_num < offset + len;
       curr_byte_num++, curr_byte++) {
    // If byte end is < 0, then we don't care about ranges.
    if (byte_end < 0 ||
        (curr_byte_num >= byte_start && curr_byte_num <= byte_end)) {
      dfsan_label new_label = createCanonicalLabel(curr_byte_num, name);
      dfsan_set_label(new_label, curr_byte, TAINT_GRANULARITY);

      // Log that we tainted data within this function from a taint source etc.
      logOperation(new_label);
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
    const std::lock_guard<std::mutex> guard(tainted_input_chunks_lock);
    tainted_input_chunks[name].emplace_back(taint_offset_start,
                                            taint_offset_end);
  }
}

[[nodiscard]] static inline dfsan_label
unionLabels(const dfsan_label &l1, const dfsan_label &l2,
            const decay_val &init_decay) {
  dfsan_label ret_label = next_label.fetch_add(1);
  checkMaxLabel(ret_label);
  taint_node_t *new_node = getTaintNode(ret_label);
  new_node->p1 = getTaintNode(l1);
  new_node->p2 = getTaintNode(l2);
  new_node->decay = init_decay;
  return ret_label;
}

[[nodiscard]] dfsan_label createUnionLabel(dfsan_label l1, dfsan_label l2) {
  // If sanitizer debug is on, this checks that l1 != l2
  DCHECK_NE(l1, l2);
  if (l1 == 0) {
    return l2;
  }
  if (l2 == 0) {
    return l1;
  }
  if (l1 > l2) {
    Swap(l1, l2);
  }
  const std::lock_guard<std::mutex> guard(union_table_lock);
  // Quick union table check
  if ((union_table[l1]).find(l2) != (union_table[l1]).end()) {
    auto val = union_table[l1].find(l2);
    return val->second;
  }
  // This calculates the average of the two decays, and then decreases it by a
  // factor of 2.
  const decay_val max_decay =
      (getTaintNode(l1)->decay + getTaintNode(l2)->decay) / 4;
  if (max_decay == 0) {
    return 0;
  }
  dfsan_label label = unionLabels(l1, l2, max_decay);
  (union_table[l1])[l2] = label;
  return label;
}

[[nodiscard]] bool taintData(const int &fd, const char *mem, int offset,
                             int len) {
  if (!isTrackingSource(fd)) {
    return false;
  }
  std::pair<int, int> &targ_info = getTargetTaintRange(fd);
  std::string &name = getSourceName(fd);
  taintTargetRange(mem, offset, len, targ_info.first, targ_info.second, name);
  return true;
}
