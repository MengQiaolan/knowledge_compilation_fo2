#include <algorithm>
#include <cctype>
#include <bit>
#include <chrono>
#include <cstddef>
#include <cstdint>
#include <cstdlib>
#include <deque>
#include <filesystem>
#include <fstream>
#include <functional>
#include <iomanip>
#include <iostream>
#include <map>
#include <memory>
#include <optional>
#include <sstream>
#include <stdexcept>
#include <string>
#include <tuple>
#include <unordered_map>
#include <unordered_set>
#include <utility>
#include <vector>

#include <minisat/core/Solver.h>
#include "spec_loader.hpp"

namespace fs = std::filesystem;

template <class T>
inline void hash_combine(std::size_t& seed, const T& value) {
    std::hash<T> hasher;
    seed ^= hasher(value) + 0x9e3779b9 + (seed << 6U) + (seed >> 2U);
}

template <class T>
inline void release_container(T& c) {
    T empty;
    c.swap(empty);
}

static inline std::string replace_all(std::string s, const std::string& from, const std::string& to) {
    if (from.empty()) {
        return s;
    }
    std::size_t pos = 0;
    while ((pos = s.find(from, pos)) != std::string::npos) {
        s.replace(pos, from.size(), to);
        pos += to.size();
    }
    return s;
}

struct VectorIntHash {
    std::size_t operator()(const std::vector<int>& v) const noexcept {
        std::size_t seed = 0;
        hash_combine(seed, v.size());
        for (int x : v) {
            hash_combine(seed, x);
        }
        return seed;
    }
};

static inline int unary_pair_slot(int left_u_idx, int right_u_idx, int unary_count) {
    return left_u_idx * unary_count + right_u_idx;
}

static inline int entity_pair_slot(int i, int j, int domain_size) {
    if (i >= j) {
        throw std::runtime_error("entity_pair_slot expects i < j");
    }
    return i * (2 * domain_size - i - 1) / 2 + (j - i - 1);
}

static inline int uvar_slot(int x, int u_idx, int unary_count) {
    return x * unary_count + u_idx;
}

struct GroundUnaryKey {
    int templ_sid = -1;
    int x_idx = -1;

    bool operator==(const GroundUnaryKey& other) const noexcept {
        return templ_sid == other.templ_sid && x_idx == other.x_idx;
    }
};

struct GroundUnaryKeyHash {
    std::size_t operator()(const GroundUnaryKey& k) const noexcept {
        std::size_t seed = 0;
        hash_combine(seed, k.templ_sid);
        hash_combine(seed, k.x_idx);
        return seed;
    }
};

struct GroundBinaryKey {
    int templ_sid = -1;
    int x_idx = -1;
    int y_idx = -1;

    bool operator==(const GroundBinaryKey& other) const noexcept {
        return templ_sid == other.templ_sid && x_idx == other.x_idx && y_idx == other.y_idx;
    }
};

struct GroundBinaryKeyHash {
    std::size_t operator()(const GroundBinaryKey& k) const noexcept {
        std::size_t seed = 0;
        hash_combine(seed, k.templ_sid);
        hash_combine(seed, k.x_idx);
        hash_combine(seed, k.y_idx);
        return seed;
    }
};

class GroundAtomCache {
public:
    explicit GroundAtomCache(fo2::InternTable& interner) : interner_(interner) {}

    int unary_atom_sid(int templ_sid, int x_idx) {
        GroundUnaryKey key{templ_sid, x_idx};
        auto it = unary_cache_.find(key);
        if (it != unary_cache_.end()) {
            return it->second;
        }
        std::string grounded = replace_all(interner_.str(templ_sid), "x", "e" + std::to_string(x_idx + 1));
        int sid = interner_.intern(std::move(grounded));
        unary_cache_.emplace(key, sid);
        return sid;
    }

    int binary_atom_sid(int templ_sid, int x_idx, int y_idx) {
        GroundBinaryKey key{templ_sid, x_idx, y_idx};
        auto it = binary_cache_.find(key);
        if (it != binary_cache_.end()) {
            return it->second;
        }
        std::string grounded = replace_all(interner_.str(templ_sid), "x", "e" + std::to_string(x_idx + 1));
        grounded = replace_all(std::move(grounded), "y", "e" + std::to_string(y_idx + 1));
        int sid = interner_.intern(std::move(grounded));
        binary_cache_.emplace(key, sid);
        return sid;
    }

private:
    fo2::InternTable& interner_;
    std::unordered_map<GroundUnaryKey, int, GroundUnaryKeyHash> unary_cache_;
    std::unordered_map<GroundBinaryKey, int, GroundBinaryKeyHash> binary_cache_;
};

enum AuxRole : int {
    kAuxTarget = 0,
    kAuxDone = 1,
    kAuxTodo = 2,
};

[[maybe_unused]] static const char* aux_role_to_cstr(int role) {
    if (role == kAuxTarget) {
        return "target";
    }
    if (role == kAuxDone) {
        return "done";
    }
    if (role == kAuxTodo) {
        return "todo";
    }
    return "unknown";
}

[[maybe_unused]] static std::optional<int> aux_role_from_string(const std::string& s) {
    if (s == "target") {
        return kAuxTarget;
    }
    if (s == "done") {
        return kAuxDone;
    }
    if (s == "todo") {
        return kAuxTodo;
    }
    return std::nullopt;
}

#include "circuit_postprocess.cpp"
#include "sat.cpp"
struct SubcircuitMainKey {
    int pair_suffix_id = -1;
    int sat_state_id = -1;

    bool operator==(const SubcircuitMainKey& other) const noexcept {
        return pair_suffix_id == other.pair_suffix_id && sat_state_id == other.sat_state_id;
    }
};

struct SubcircuitMainKeyHash {
    std::size_t operator()(const SubcircuitMainKey& k) const noexcept {
        std::size_t seed = 0;
        hash_combine(seed, k.pair_suffix_id);
        hash_combine(seed, k.sat_state_id);
        return seed;
    }
};

struct AuxIndexKey {
    int base_idx = -1;
    int role = -1;
    int sat_mask = 0;

    bool operator==(const AuxIndexKey& other) const noexcept {
        return base_idx == other.base_idx && role == other.role && sat_mask == other.sat_mask;
    }
};

struct AuxIndexKeyHash {
    std::size_t operator()(const AuxIndexKey& k) const noexcept {
        std::size_t seed = 0;
        hash_combine(seed, k.base_idx);
        hash_combine(seed, k.role);
        hash_combine(seed, k.sat_mask);
        return seed;
    }
};

struct AuxUnaryParsed {
    int base_u_idx = -1;
    int role = -1;
    int sat_mask = 0;
};

[[maybe_unused]] static std::optional<AuxUnaryParsed> parse_aux_unary_name(
    int aux_name_sid,
    const fo2::TypeSystemId& spec,
    const std::unordered_map<std::string, int>& base_name_to_idx,
    const fo2::InternTable& interner
);

struct GroupedBTypesKey {
    int candidate_set_id = 0;
    int si = 0;
    int sj = 0;

    bool operator==(const GroupedBTypesKey& other) const noexcept {
        return candidate_set_id == other.candidate_set_id && si == other.si && sj == other.sj;
    }
};

struct GroupedBTypesKeyHash {
    std::size_t operator()(const GroupedBTypesKey& k) const noexcept {
        std::size_t seed = 0;
        hash_combine(seed, k.candidate_set_id);
        hash_combine(seed, k.si);
        hash_combine(seed, k.sj);
        return seed;
    }
};
