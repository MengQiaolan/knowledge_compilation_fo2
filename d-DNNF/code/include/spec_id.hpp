#pragma once

#include <filesystem>
#include <optional>
#include <stdexcept>
#include <string>
#include <unordered_map>
#include <unordered_set>
#include <utility>
#include <vector>

namespace fo2 {

class InternTable {
public:
    int intern(const std::string& s) {
        auto it = to_id_.find(s);
        if (it != to_id_.end()) {
            return it->second;
        }
        int id = static_cast<int>(to_str_.size());
        to_str_.push_back(s);
        to_id_.emplace(to_str_.back(), id);
        return id;
    }

    int intern(std::string&& s) {
        auto it = to_id_.find(s);
        if (it != to_id_.end()) {
            return it->second;
        }
        int id = static_cast<int>(to_str_.size());
        to_str_.push_back(std::move(s));
        to_id_.emplace(to_str_.back(), id);
        return id;
    }

    const std::string& str(int id) const {
        if (id < 0 || id >= static_cast<int>(to_str_.size())) {
            throw std::runtime_error("invalid intern string id: " + std::to_string(id));
        }
        return to_str_[static_cast<std::size_t>(id)];
    }

    std::size_t size() const { return to_str_.size(); }

private:
    std::unordered_map<std::string, int> to_id_;
    std::vector<std::string> to_str_;
};

using AtomTemplateLit = std::pair<int, bool>;

struct UnaryTypeId {
    int name_sid = -1;
    std::vector<AtomTemplateLit> literals;
    std::vector<int> satisfies_self;
    std::optional<int> sat_bound;
};

struct BinaryTypeId {
    int name_sid = -1;
    std::vector<AtomTemplateLit> literals;
    std::vector<int> satisfies_from_left;
    std::vector<int> satisfies_from_right;
};

class TypeSystemId {
public:
    std::vector<UnaryTypeId> unary_types;
    std::vector<BinaryTypeId> binary_types;

    std::vector<int> unary_name_sids;
    std::vector<int> binary_name_sids;

    std::unordered_map<int, int> unary_sid_to_idx;
    std::unordered_map<int, int> binary_sid_to_idx;

    std::vector<int> existential_constraint_sids;

    // Flattened table: pair_binary_choices[left * U + right] -> candidate binary indices
    std::vector<std::vector<int>> pair_binary_choices;

    int unary_count() const { return static_cast<int>(unary_types.size()); }
    int binary_count() const { return static_cast<int>(binary_types.size()); }
    int existential_count() const { return static_cast<int>(existential_constraint_sids.size()); }

    const std::vector<int>& pair_choice_names(int left_u_idx, int right_u_idx) const {
        int u = unary_count();
        int idx = left_u_idx * u + right_u_idx;
        if (idx < 0 || idx >= static_cast<int>(pair_binary_choices.size())) {
            throw std::runtime_error("pair_choice_names index out of range");
        }
        return pair_binary_choices[static_cast<std::size_t>(idx)];
    }

    void validate() const {
        const int u = unary_count();
        const int b = binary_count();

        if (static_cast<int>(unary_name_sids.size()) != u) {
            throw std::runtime_error("unary_name_sids size mismatch");
        }
        if (static_cast<int>(binary_name_sids.size()) != b) {
            throw std::runtime_error("binary_name_sids size mismatch");
        }
        if (static_cast<int>(pair_binary_choices.size()) != u * u) {
            throw std::runtime_error("pair_binary_choices size mismatch");
        }

        std::unordered_set<int> seen_constraints;
        for (int sid : existential_constraint_sids) {
            if (!seen_constraints.insert(sid).second) {
                throw std::runtime_error("existential_constraints must be unique");
            }
        }

        for (int i = 0; i < u; ++i) {
            const auto& ut = unary_types[static_cast<std::size_t>(i)];
            if (ut.name_sid != unary_name_sids[static_cast<std::size_t>(i)]) {
                throw std::runtime_error("unary name sid mismatch");
            }
            if (ut.sat_bound.has_value() && *ut.sat_bound < 0) {
                throw std::runtime_error("invalid sat_bound");
            }
            for (int cidx : ut.satisfies_self) {
                if (cidx < 0 || cidx >= existential_count()) {
                    throw std::runtime_error("unary satisfies_self constraint index out of range");
                }
            }
        }

        for (int i = 0; i < b; ++i) {
            const auto& bt = binary_types[static_cast<std::size_t>(i)];
            if (bt.name_sid != binary_name_sids[static_cast<std::size_t>(i)]) {
                throw std::runtime_error("binary name sid mismatch");
            }
            for (int cidx : bt.satisfies_from_left) {
                if (cidx < 0 || cidx >= existential_count()) {
                    throw std::runtime_error("binary left constraint index out of range");
                }
            }
            for (int cidx : bt.satisfies_from_right) {
                if (cidx < 0 || cidx >= existential_count()) {
                    throw std::runtime_error("binary right constraint index out of range");
                }
            }
        }

        for (int left = 0; left < u; ++left) {
            for (int right = 0; right < u; ++right) {
                const auto& cand = pair_choice_names(left, right);
                for (int bidx : cand) {
                    if (bidx < 0 || bidx >= b) {
                        throw std::runtime_error("pair candidate binary index out of range");
                    }
                }
            }
        }
    }
};

}  // namespace fo2
