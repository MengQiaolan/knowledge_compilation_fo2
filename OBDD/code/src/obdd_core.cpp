#include "obdd_core.hpp"

#include "compiler_common.hpp"

static bool contains_int_obdd(const std::vector<int>& xs, int value) {
    return std::find(xs.begin(), xs.end(), value) != xs.end();
}

static std::vector<int> canonicalize_ints_obdd(std::vector<int> values) {
    std::sort(values.begin(), values.end());
    values.erase(std::unique(values.begin(), values.end()), values.end());
    return values;
}

static std::string trim_ascii_obdd(std::string s) {
    std::size_t begin = 0;
    while (begin < s.size() && std::isspace(static_cast<unsigned char>(s[begin])) != 0) {
        ++begin;
    }
    std::size_t end = s.size();
    while (end > begin && std::isspace(static_cast<unsigned char>(s[end - 1])) != 0) {
        --end;
    }
    return s.substr(begin, end - begin);
}

static std::string join_strings_obdd(const std::vector<std::string>& items, const std::string& sep) {
    std::ostringstream oss;
    for (std::size_t i = 0; i < items.size(); ++i) {
        if (i != 0) {
            oss << sep;
        }
        oss << items[i];
    }
    return oss.str();
}

static std::string json_escape_obdd(const std::string& s) {
    std::ostringstream oss;
    for (char ch : s) {
        switch (ch) {
            case '\"': oss << "\\\""; break;
            case '\\': oss << "\\\\"; break;
            case '\b': oss << "\\b"; break;
            case '\f': oss << "\\f"; break;
            case '\n': oss << "\\n"; break;
            case '\r': oss << "\\r"; break;
            case '\t': oss << "\\t"; break;
            default:
                if (static_cast<unsigned char>(ch) < 0x20U) {
                    oss << "\\u" << std::hex << std::setw(4) << std::setfill('0')
                        << static_cast<int>(static_cast<unsigned char>(ch)) << std::dec;
                } else {
                    oss << ch;
                }
                break;
        }
    }
    return oss.str();
}

#define contains_int contains_int_obdd
#define canonicalize_ints canonicalize_ints_obdd
#define trim_ascii trim_ascii_obdd
#define join_strings join_strings_obdd
#define json_escape json_escape_obdd
#include "compiler_independence.hpp"
#undef json_escape
#undef join_strings
#undef trim_ascii
#undef canonicalize_ints
#undef contains_int

class BigUInt {
public:
    BigUInt() = default;
    explicit BigUInt(std::uint64_t v) { set(v); }

    BigUInt& operator=(std::uint64_t v) {
        set(v);
        return *this;
    }

    BigUInt& operator+=(const BigUInt& rhs) {
        const std::size_t n = std::max(limbs_.size(), rhs.limbs_.size());
        limbs_.resize(n, 0U);
        std::uint64_t carry = 0;
        for (std::size_t i = 0; i < n; ++i) {
            std::uint64_t a = limbs_[i];
            std::uint64_t b = (i < rhs.limbs_.size()) ? rhs.limbs_[i] : 0U;
            std::uint64_t sum = a + b + carry;
            limbs_[i] = static_cast<std::uint32_t>(sum & 0xFFFFFFFFULL);
            carry = sum >> 32U;
        }
        if (carry != 0) {
            limbs_.push_back(static_cast<std::uint32_t>(carry));
        }
        return *this;
    }

    BigUInt& operator<<=(int bits) {
        if (bits <= 0 || is_zero()) {
            return *this;
        }
        int word_shift = bits / 32;
        int bit_shift = bits % 32;
        if (word_shift > 0) {
            limbs_.insert(limbs_.begin(), static_cast<std::size_t>(word_shift), 0U);
        }
        if (bit_shift > 0) {
            std::uint64_t carry = 0;
            for (std::size_t i = 0; i < limbs_.size(); ++i) {
                std::uint64_t cur = (static_cast<std::uint64_t>(limbs_[i]) << bit_shift) | carry;
                limbs_[i] = static_cast<std::uint32_t>(cur & 0xFFFFFFFFULL);
                carry = cur >> 32U;
            }
            if (carry != 0) {
                limbs_.push_back(static_cast<std::uint32_t>(carry));
            }
        }
        return *this;
    }

    friend BigUInt operator+(BigUInt lhs, const BigUInt& rhs) {
        lhs += rhs;
        return lhs;
    }

    friend std::ostream& operator<<(std::ostream& os, const BigUInt& v) {
        os << v.to_string();
        return os;
    }

private:
    bool is_zero() const { return limbs_.empty(); }

    void set(std::uint64_t v) {
        limbs_.clear();
        if (v == 0) {
            return;
        }
        limbs_.push_back(static_cast<std::uint32_t>(v & 0xFFFFFFFFULL));
        std::uint32_t hi = static_cast<std::uint32_t>(v >> 32U);
        if (hi != 0U) {
            limbs_.push_back(hi);
        }
    }

    std::string to_string() const {
        if (limbs_.empty()) {
            return "0";
        }
        static constexpr std::uint32_t kBase10 = 1000000000U;
        std::vector<std::uint32_t> tmp = limbs_;
        std::vector<std::uint32_t> parts;
        while (!tmp.empty()) {
            std::uint64_t rem = 0;
            for (std::size_t idx = tmp.size(); idx-- > 0;) {
                std::uint64_t cur = (rem << 32U) + tmp[idx];
                tmp[idx] = static_cast<std::uint32_t>(cur / kBase10);
                rem = cur % kBase10;
            }
            parts.push_back(static_cast<std::uint32_t>(rem));
            while (!tmp.empty() && tmp.back() == 0U) {
                tmp.pop_back();
            }
        }
        std::ostringstream oss;
        oss << parts.back();
        for (std::size_t i = parts.size() - 1; i-- > 0;) {
            oss << std::setw(9) << std::setfill('0') << parts[i];
        }
        return oss.str();
    }

    std::vector<std::uint32_t> limbs_;
};

struct ObddNode {
    int var = -1;
    int low = 0;
    int high = 0;
};

struct ObddNodeKey {
    int var = -1;
    int low = 0;
    int high = 0;

    bool operator==(const ObddNodeKey& other) const noexcept {
        return var == other.var && low == other.low && high == other.high;
    }
};

struct ObddNodeKeyHash {
    std::size_t operator()(const ObddNodeKey& k) const noexcept {
        std::size_t seed = 0;
        hash_combine(seed, k.var);
        hash_combine(seed, k.low);
        hash_combine(seed, k.high);
        return seed;
    }
};

struct ApplyKey {
    int op = 0;
    int left = 0;
    int right = 0;

    bool operator==(const ApplyKey& other) const noexcept {
        return op == other.op && left == other.left && right == other.right;
    }
};

struct ApplyKeyHash {
    std::size_t operator()(const ApplyKey& k) const noexcept {
        std::size_t seed = 0;
        hash_combine(seed, k.op);
        hash_combine(seed, k.left);
        hash_combine(seed, k.right);
        return seed;
    }
};

struct LitVecHash {
    std::size_t operator()(const std::vector<std::pair<int, bool>>& xs) const noexcept {
        std::size_t seed = 0;
        hash_combine(seed, xs.size());
        for (const auto& p : xs) {
            hash_combine(seed, p.first);
            hash_combine(seed, p.second);
        }
        return seed;
    }
};

class ObddManager {
public:
    static constexpr int kFalse = 0;
    static constexpr int kTrue = 1;

    explicit ObddManager(std::vector<std::string> atom_names)
        : atom_names_(std::move(atom_names)) {
        nodes_.resize(2);
    }

    const std::vector<std::string>& atom_names() const { return atom_names_; }

    int mk(int var, int low, int high) {
        if (low == high) {
            return low;
        }
        ObddNodeKey key{var, low, high};
        auto it = unique_.find(key);
        if (it != unique_.end()) {
            return it->second;
        }
        int id = static_cast<int>(nodes_.size());
        nodes_.push_back(ObddNode{var, low, high});
        unique_.emplace(key, id);
        return id;
    }

    int cube(std::vector<std::pair<int, bool>> literals) {
        std::sort(literals.begin(), literals.end());
        std::vector<std::pair<int, bool>> normalized;
        normalized.reserve(literals.size());
        for (const auto& lit : literals) {
            if (!normalized.empty() && normalized.back().first == lit.first) {
                if (normalized.back().second != lit.second) {
                    return kFalse;
                }
                continue;
            }
            normalized.push_back(lit);
        }

        auto it = cube_cache_.find(normalized);
        if (it != cube_cache_.end()) {
            return it->second;
        }

        int node = kTrue;
        for (std::size_t idx = normalized.size(); idx-- > 0;) {
            int var = normalized[idx].first;
            bool positive = normalized[idx].second;
            node = positive ? mk(var, kFalse, node) : mk(var, node, kFalse);
        }
        cube_cache_.emplace(std::move(normalized), node);
        return node;
    }

    int apply_and(int left, int right) { return apply(0, left, right); }
    int apply_or(int left, int right) { return apply(1, left, right); }

    BigUInt model_count(int root) {
        count_cache_.clear();
        return count_from(root, 0);
    }

    std::vector<int> reachable_nonterminals(int root) const {
        std::vector<int> order;
        std::unordered_set<int> seen;
        std::function<void(int)> dfs = [&](int node_id) {
            if (node_id <= 1 || seen.find(node_id) != seen.end()) {
                return;
            }
            seen.insert(node_id);
            order.push_back(node_id);
            const auto& node = nodes_.at(static_cast<std::size_t>(node_id));
            dfs(node.low);
            dfs(node.high);
        };
        dfs(root);
        return order;
    }

    std::size_t reachable_nonterminal_count(int root) const {
        return reachable_nonterminals(root).size();
    }

    void write_dot(int root, const fs::path& path) const {
        auto escape = [](const std::string& s) {
            std::string out;
            out.reserve(s.size() + 8);
            for (char c : s) {
                if (c == '\\') {
                    out += "\\\\";
                } else if (c == '"') {
                    out += "\\\"";
                } else {
                    out.push_back(c);
                }
            }
            return out;
        };

        std::ofstream out(path);
        if (!out) {
            throw std::runtime_error("Failed to open DOT output file: " + path.string());
        }

        std::vector<int> reachable = reachable_nonterminals(root);
        std::unordered_set<int> reachable_set(reachable.begin(), reachable.end());

        out << "digraph OBDD {\n";
        out << "  rankdir=TB;\n";
        out << "  t0 [label=\"FALSE\", shape=box];\n";
        out << "  t1 [label=\"TRUE\", shape=box];\n";
        for (int node_id : reachable) {
            const auto& node = nodes_.at(static_cast<std::size_t>(node_id));
            out << "  n" << node_id << " [label=\"" << escape(atom_names_.at(static_cast<std::size_t>(node.var)))
                << "\", shape=circle];\n";
        }
        if (root <= 1) {
            out << "  root [label=\"root\", shape=point];\n";
            out << "  root -> t" << root << ";\n";
        }
        for (int node_id : reachable) {
            const auto& node = nodes_.at(static_cast<std::size_t>(node_id));
            for (const auto& edge : {std::pair<const char*, int>{"0", node.low}, std::pair<const char*, int>{"1", node.high}}) {
                int child = edge.second;
                if (child <= 1 || reachable_set.find(child) != reachable_set.end()) {
                    out << "  n" << node_id << " -> " << (child <= 1 ? "t" : "n") << child
                        << " [label=\"" << edge.first << "\"];\n";
                }
            }
        }
        out << "}\n";
    }

private:
    int var_of(int node_id) const {
        if (node_id <= 1) {
            return static_cast<int>(atom_names_.size());
        }
        return nodes_.at(static_cast<std::size_t>(node_id)).var;
    }

    std::pair<int, int> cofactor(int node_id, int var) const {
        if (node_id <= 1 || var_of(node_id) != var) {
            return {node_id, node_id};
        }
        const auto& node = nodes_.at(static_cast<std::size_t>(node_id));
        return {node.low, node.high};
    }

    int apply(int op, int left, int right) {
        if (left > right) {
            std::swap(left, right);
        }
        ApplyKey key{op, left, right};
        auto it = apply_cache_.find(key);
        if (it != apply_cache_.end()) {
            return it->second;
        }

        if (op == 0) {
            if (left == kFalse || right == kFalse) return kFalse;
            if (left == kTrue) return right;
            if (right == kTrue) return left;
        } else {
            if (left == kTrue || right == kTrue) return kTrue;
            if (left == kFalse) return right;
            if (right == kFalse) return left;
        }

        int top = std::min(var_of(left), var_of(right));
        auto [llow, lhigh] = cofactor(left, top);
        auto [rlow, rhigh] = cofactor(right, top);
        int low = apply(op, llow, rlow);
        int high = apply(op, lhigh, rhigh);
        int out = mk(top, low, high);
        apply_cache_.emplace(key, out);
        return out;
    }

    BigUInt count_from(int node_id, int level) {
        std::uint64_t key = (static_cast<std::uint64_t>(static_cast<std::uint32_t>(node_id)) << 32U) |
                            static_cast<std::uint32_t>(level);
        auto it = count_cache_.find(key);
        if (it != count_cache_.end()) {
            return it->second;
        }
        if (node_id == kFalse) {
            return BigUInt(0);
        }
        if (node_id == kTrue) {
            BigUInt out(1);
            out <<= static_cast<int>(atom_names_.size()) - level;
            return out;
        }
        const auto& node = nodes_.at(static_cast<std::size_t>(node_id));
        BigUInt out = count_from(node.low, node.var + 1) + count_from(node.high, node.var + 1);
        out <<= (node.var - level);
        count_cache_.emplace(key, out);
        return out;
    }

    std::vector<std::string> atom_names_;
    std::vector<ObddNode> nodes_;
    std::unordered_map<ObddNodeKey, int, ObddNodeKeyHash> unique_;
    std::unordered_map<ApplyKey, int, ApplyKeyHash> apply_cache_;
    std::unordered_map<std::vector<std::pair<int, bool>>, int, LitVecHash> cube_cache_;
    std::unordered_map<std::uint64_t, BigUInt> count_cache_;
};

class AtomOrder {
public:
    AtomOrder(const fo2::TypeSystemId& spec, int domain_size, fo2::InternTable& interner)
        : spec_(spec), n_(domain_size), interner_(interner) {
        collect_templates();
        for (int x = 0; x < n_; ++x) {
            for (int templ_sid : unary_templates_) {
                add_atom(ground_unary_name(templ_sid, x));
            }
        }
        for (const auto& p : pairs()) {
            for (int templ_sid : binary_templates_) {
                add_atom(ground_binary_name(templ_sid, p.first, p.second));
            }
        }
    }

    const std::vector<std::string>& atom_names() const { return atom_names_; }

    std::vector<std::pair<int, int>> pairs() const {
        std::vector<std::pair<int, int>> out;
        for (int i = 0; i < n_ - 1; ++i) {
            for (int j = i + 1; j < n_; ++j) {
                out.emplace_back(i, j);
            }
        }
        return out;
    }

    std::vector<std::pair<int, bool>> unary_cube(int x, int uidx) const {
        std::vector<std::pair<int, bool>> out;
        for (const auto& lit : spec_.unary_types.at(static_cast<std::size_t>(uidx)).literals) {
            out.emplace_back(index_of(ground_unary_name(lit.first, x)), lit.second);
        }
        return out;
    }

    std::vector<std::pair<int, bool>> binary_cube(
        const fo2::TypeSystemId& spec,
        int x,
        int y,
        int bidx
    ) const {
        std::vector<std::pair<int, bool>> out;
        for (const auto& lit : spec.binary_types.at(static_cast<std::size_t>(bidx)).literals) {
            out.emplace_back(index_of(ground_binary_name(lit.first, x, y)), lit.second);
        }
        return out;
    }

private:
    void collect_templates() {
        std::unordered_set<int> seen_unary;
        for (const auto& u : spec_.unary_types) {
            for (const auto& lit : u.literals) {
                if (seen_unary.insert(lit.first).second) {
                    unary_templates_.push_back(lit.first);
                }
            }
        }

        std::unordered_set<int> seen_binary;
        for (const auto& b : spec_.binary_types) {
            for (const auto& lit : b.literals) {
                if (seen_binary.insert(lit.first).second) {
                    binary_templates_.push_back(lit.first);
                }
            }
        }
    }

    void add_atom(std::string atom) {
        if (atom_index_.find(atom) != atom_index_.end()) {
            return;
        }
        int idx = static_cast<int>(atom_names_.size());
        atom_names_.push_back(atom);
        atom_index_.emplace(std::move(atom), idx);
    }

    int index_of(const std::string& atom) const {
        auto it = atom_index_.find(atom);
        if (it == atom_index_.end()) {
            throw std::runtime_error("atom is absent from global OBDD order: " + atom);
        }
        return it->second;
    }

    std::string ground_unary_name(int templ_sid, int x) const {
        return replace_all(interner_.str(templ_sid), "x", "e" + std::to_string(x + 1));
    }

    std::string ground_binary_name(int templ_sid, int x, int y) const {
        std::string grounded = replace_all(interner_.str(templ_sid), "x", "e" + std::to_string(x + 1));
        grounded = replace_all(std::move(grounded), "y", "e" + std::to_string(y + 1));
        return grounded;
    }

    const fo2::TypeSystemId& spec_;
    int n_;
    fo2::InternTable& interner_;
    std::vector<int> unary_templates_;
    std::vector<int> binary_templates_;
    std::vector<std::string> atom_names_;
    std::unordered_map<std::string, int> atom_index_;
};

struct BinaryGroupCubeKey {
    int x = 0;
    int y = 0;
    int candidate_set_id = 0;

    bool operator==(const BinaryGroupCubeKey& other) const noexcept {
        return x == other.x && y == other.y && candidate_set_id == other.candidate_set_id;
    }
};

struct BinaryGroupCubeKeyHash {
    std::size_t operator()(const BinaryGroupCubeKey& k) const noexcept {
        std::size_t seed = 0;
        hash_combine(seed, k.x);
        hash_combine(seed, k.y);
        hash_combine(seed, k.candidate_set_id);
        return seed;
    }
};

class ObddStage2Engine {
public:
    ObddStage2Engine(
        const fo2::TypeSystemId& spec,
        const fo2::TypeSystemId* aux_spec,
        int domain_size,
        const std::vector<std::pair<int, int>>& pair_order,
        const AtomOrder& atom_order,
        ObddManager& manager,
        fo2::InternTable& interner
    )
        : spec_(spec),
          aux_spec_(aux_spec),
          n_(domain_size),
          pair_order_(pair_order),
          atom_order_(atom_order),
          manager_(manager),
          interner_(interner),
          aux_config_checker_(aux_spec == nullptr ? nullptr : std::make_unique<AuxConfigSATChecker>(*aux_spec)) {
        all_sat_mask_ = (1 << spec_.existential_count()) - 1;
        unary_sat_mask_.reserve(static_cast<std::size_t>(spec_.unary_count()));
        for (const auto& u : spec_.unary_types) {
            unary_sat_mask_.push_back(mask_of(u.satisfies_self));
        }
        binary_sat_mask_.reserve(static_cast<std::size_t>(spec_.binary_count()));
        for (const auto& b : spec_.binary_types) {
            binary_sat_mask_.push_back({mask_of(b.satisfies_from_left), mask_of(b.satisfies_from_right)});
        }
        prepare_type_signatures();
        if (aux_spec_ != nullptr) {
            build_aux_index();
            prepare_three_block_layout();
        }
    }

    int compile_from_unary(const std::vector<int>& unary_assign) {
        std::vector<int> sat_masks;
        sat_masks.reserve(unary_assign.size());
        for (int u : unary_assign) {
            sat_masks.push_back(unary_sat_mask_.at(static_cast<std::size_t>(u)));
        }
        const auto& suffixes = pair_signature_suffixes(unary_assign);
        if (aux_spec_ == nullptr) {
            return stage_ii_no_aux(0, unary_assign, sat_masks, suffixes);
        }
        std::vector<int> aux_config = init_aux_config(unary_assign, sat_masks);
        return stage_ii_with_aux(0, 0, unary_assign, sat_masks, suffixes, aux_config);
    }

private:
    static int mask_of(const std::vector<int>& indices) {
        int mask = 0;
        for (int idx : indices) {
            mask |= (1 << idx);
        }
        return mask;
    }

    void prepare_type_signatures() {
        const int ucount = spec_.unary_count();
        btype_candidate_set_.assign(static_cast<std::size_t>(ucount * ucount), -1);
        for (int left = 0; left < ucount; ++left) {
            for (int right = 0; right < ucount; ++right) {
                int set_id = candidate_registry_.id_of(spec_.pair_choice_names(left, right));
                btype_candidate_set_[static_cast<std::size_t>(unary_pair_slot(left, right, ucount))] = set_id;
            }
        }
    }

    int candidate_set_id_of(int left_u, int right_u) const {
        return btype_candidate_set_.at(static_cast<std::size_t>(unary_pair_slot(left_u, right_u, spec_.unary_count())));
    }

    const std::vector<std::vector<int>>& pair_signature_suffixes(const std::vector<int>& unary_assign) {
        auto it = pair_signature_suffix_cache_.find(unary_assign);
        if (it != pair_signature_suffix_cache_.end()) {
            return it->second;
        }
        std::vector<int> seq;
        seq.reserve(pair_order_.size());
        for (const auto& p : pair_order_) {
            seq.push_back(candidate_set_id_of(unary_assign[static_cast<std::size_t>(p.first)], unary_assign[static_cast<std::size_t>(p.second)]));
        }
        std::vector<std::vector<int>> suffixes(seq.size() + 1);
        for (std::size_t k = 0; k <= seq.size(); ++k) {
            suffixes[k].assign(seq.begin() + static_cast<std::ptrdiff_t>(k), seq.end());
        }
        auto inserted = pair_signature_suffix_cache_.emplace(unary_assign, std::move(suffixes));
        return inserted.first->second;
    }

    int stage_ii_no_aux(
        int pair_idx,
        const std::vector<int>& unary_assign,
        std::vector<int>& sat_masks,
        const std::vector<std::vector<int>>& suffixes
    ) {
        if (pair_idx == static_cast<int>(pair_order_.size())) {
            return std::all_of(sat_masks.begin(), sat_masks.end(), [&](int m) { return m == all_sat_mask_; })
                ? ObddManager::kTrue
                : ObddManager::kFalse;
        }

        int pair_suffix_id = pair_suffix_registry_.id_of(suffixes[static_cast<std::size_t>(pair_idx)]);
        int sat_state_id = sat_state_registry_.id_of(sat_masks);
        SubcircuitMainKey key{pair_suffix_id, sat_state_id};
        auto cached = subcircuit_cache_.find(key);
        if (cached != subcircuit_cache_.end()) {
            return cached->second;
        }

        auto [i, j] = pair_order_.at(static_cast<std::size_t>(pair_idx));
        int ui = unary_assign[static_cast<std::size_t>(i)];
        int uj = unary_assign[static_cast<std::size_t>(j)];
        int candidate_set_id = suffixes[static_cast<std::size_t>(pair_idx)][0];

        int result = ObddManager::kFalse;
        if (sat_masks[static_cast<std::size_t>(i)] == all_sat_mask_ &&
            sat_masks[static_cast<std::size_t>(j)] == all_sat_mask_) {
            int cube = binary_group_cube(i, j, candidate_set_id);
            if (cube != ObddManager::kFalse) {
                int suffix = stage_ii_no_aux(pair_idx + 1, unary_assign, sat_masks, suffixes);
                result = manager_.apply_and(cube, suffix);
            }
            subcircuit_cache_[key] = result;
            return result;
        }

        for (const auto& group : grouped_btypes(candidate_set_id, sat_masks[static_cast<std::size_t>(i)], sat_masks[static_cast<std::size_t>(j)])) {
            int old_i = sat_masks[static_cast<std::size_t>(i)];
            int old_j = sat_masks[static_cast<std::size_t>(j)];
            sat_masks[static_cast<std::size_t>(i)] = group.first.first;
            sat_masks[static_cast<std::size_t>(j)] = group.first.second;

            int group_set_id = candidate_registry_.id_of(group.second);
            int cube = binary_group_cube(i, j, group_set_id);
            if (cube != ObddManager::kFalse) {
                int suffix = stage_ii_no_aux(pair_idx + 1, unary_assign, sat_masks, suffixes);
                result = manager_.apply_or(result, manager_.apply_and(cube, suffix));
            }

            sat_masks[static_cast<std::size_t>(i)] = old_i;
            sat_masks[static_cast<std::size_t>(j)] = old_j;
        }
        subcircuit_cache_[key] = result;
        return result;
    }

    int stage_ii_with_aux(
        int target,
        int pair_idx,
        const std::vector<int>& unary_assign,
        std::vector<int>& sat_masks,
        const std::vector<std::vector<int>>& suffixes,
        std::vector<int>& aux_config
    ) {
        if (pair_idx == static_cast<int>(pair_order_.size())) {
            return std::all_of(sat_masks.begin(), sat_masks.end(), [&](int m) { return m == all_sat_mask_; })
                ? ObddManager::kTrue
                : ObddManager::kFalse;
        }

        int pair_suffix_id = pair_suffix_registry_.id_of(suffixes[static_cast<std::size_t>(pair_idx)]);
        int sat_state_id = sat_state_registry_.id_of(sat_masks);
        SubcircuitMainKey key{pair_suffix_id, sat_state_id};
        auto cached = subcircuit_cache_.find(key);
        if (cached != subcircuit_cache_.end()) {
            return cached->second;
        }

        auto [i, j] = pair_order_.at(static_cast<std::size_t>(pair_idx));
        int ui = unary_assign[static_cast<std::size_t>(i)];
        int uj = unary_assign[static_cast<std::size_t>(j)];
        int si = sat_masks[static_cast<std::size_t>(i)];
        int sj = sat_masks[static_cast<std::size_t>(j)];
        int candidate_set_id = suffixes[static_cast<std::size_t>(pair_idx)][0];

        bool target_shift = (i != target);
        std::vector<int> aux_config_copy;
        if (target_shift) {
            aux_config_copy = aux_config;
            aux_config[aux_index_of(unary_assign[static_cast<std::size_t>(target)], kAuxTarget, sat_masks[static_cast<std::size_t>(target)])] -= 1;
            target = i;
            aux_config[aux_index_of(ui, kAuxDone, si)] -= 1;
            aux_config[aux_index_of(ui, kAuxTarget, si)] += 1;
            move_done_to_todo(aux_config);
        }

        int old_i_aux_idx = aux_index_of(ui, kAuxTarget, si);
        int old_j_aux_idx = aux_index_of(uj, kAuxTodo, sj);
        int result = ObddManager::kFalse;

        if (si == all_sat_mask_ && sj == all_sat_mask_) {
            aux_config[old_j_aux_idx] -= 1;
            int new_j_aux_idx = aux_index_of(uj, kAuxDone, sj);
            aux_config[new_j_aux_idx] += 1;

            int cube = binary_group_cube(i, j, candidate_set_id);
            if (cube != ObddManager::kFalse) {
                int suffix = stage_ii_with_aux(target, pair_idx + 1, unary_assign, sat_masks, suffixes, aux_config);
                result = manager_.apply_and(cube, suffix);
            }

            subcircuit_cache_[key] = result;
            if (target_shift) {
                aux_config = aux_config_copy;
            } else {
                aux_config[new_j_aux_idx] -= 1;
                aux_config[old_j_aux_idx] += 1;
            }
            return result;
        }

        aux_config[old_i_aux_idx] -= 1;
        aux_config[old_j_aux_idx] -= 1;

        for (const auto& group : grouped_btypes(candidate_set_id, si, sj)) {
            int new_i_aux_idx = aux_index_of(ui, kAuxTarget, group.first.first);
            int new_j_aux_idx = aux_index_of(uj, kAuxDone, group.first.second);
            aux_config[new_i_aux_idx] += 1;
            aux_config[new_j_aux_idx] += 1;

            if (!aux_config_checker_->is_config_sat(aux_config)) {
                aux_config[new_i_aux_idx] -= 1;
                aux_config[new_j_aux_idx] -= 1;
                continue;
            }

            sat_masks[static_cast<std::size_t>(i)] = group.first.first;
            sat_masks[static_cast<std::size_t>(j)] = group.first.second;

            int group_set_id = candidate_registry_.id_of(group.second);
            int cube = binary_group_cube(i, j, group_set_id);
            if (cube != ObddManager::kFalse) {
                int suffix = stage_ii_with_aux(target, pair_idx + 1, unary_assign, sat_masks, suffixes, aux_config);
                result = manager_.apply_or(result, manager_.apply_and(cube, suffix));
            }

            sat_masks[static_cast<std::size_t>(i)] = si;
            sat_masks[static_cast<std::size_t>(j)] = sj;
            aux_config[new_i_aux_idx] -= 1;
            aux_config[new_j_aux_idx] -= 1;
        }

        subcircuit_cache_[key] = result;
        if (target_shift) {
            aux_config = aux_config_copy;
        } else {
            aux_config[old_i_aux_idx] += 1;
            aux_config[old_j_aux_idx] += 1;
        }
        return result;
    }

    const std::vector<std::pair<std::pair<int, int>, std::vector<int>>>& grouped_btypes(
        int candidate_set_id,
        int si,
        int sj
    ) {
        GroupedBTypesKey key{candidate_set_id, si, sj};
        auto it = grouped_btypes_cache_.find(key);
        if (it != grouped_btypes_cache_.end()) {
            return it->second;
        }
        std::map<std::pair<int, int>, std::vector<int>> grouped;
        for (int bidx : candidate_registry_.names(candidate_set_id)) {
            auto masks = binary_sat_mask_.at(static_cast<std::size_t>(bidx));
            grouped[{si | masks.first, sj | masks.second}].push_back(bidx);
        }
        std::vector<std::pair<std::pair<int, int>, std::vector<int>>> out;
        out.reserve(grouped.size());
        for (auto& kv : grouped) {
            out.push_back(std::move(kv));
        }
        auto inserted = grouped_btypes_cache_.emplace(key, std::move(out));
        return inserted.first->second;
    }

    int binary_group_cube(int x, int y, int candidate_set_id) {
        BinaryGroupCubeKey key{x, y, candidate_set_id};
        auto it = binary_group_cube_cache_.find(key);
        if (it != binary_group_cube_cache_.end()) {
            return it->second;
        }
        int node = ObddManager::kFalse;
        for (int bidx : candidate_registry_.names(candidate_set_id)) {
            int cube = manager_.cube(atom_order_.binary_cube(spec_, x, y, bidx));
            node = manager_.apply_or(node, cube);
            if (node == ObddManager::kTrue) {
                break;
            }
        }
        binary_group_cube_cache_.emplace(key, node);
        return node;
    }

    void build_aux_index() {
        std::unordered_map<std::string, int> base_name_to_idx;
        for (int u = 0; u < spec_.unary_count(); ++u) {
            base_name_to_idx.emplace(interner_.str(spec_.unary_name_sids.at(static_cast<std::size_t>(u))), u);
        }
        for (int idx = 0; idx < aux_spec_->unary_count(); ++idx) {
            auto parsed = parse_aux_unary_name(
                aux_spec_->unary_name_sids.at(static_cast<std::size_t>(idx)),
                spec_,
                base_name_to_idx,
                interner_
            );
            if (!parsed.has_value()) {
                throw std::runtime_error("Invalid aux unary type name in OBDD stage2 engine");
            }
            AuxIndexKey key{parsed->base_u_idx, parsed->role, parsed->sat_mask};
            if (!aux_index_.emplace(key, idx).second) {
                throw std::runtime_error("Duplicate aux unary mapping in OBDD stage2 engine");
            }
        }
    }

    void prepare_three_block_layout() {
        int total = aux_spec_->unary_count();
        if (total % 3 != 0) {
            throw std::runtime_error("aux unary type count must be divisible by 3");
        }
        aux_block_size_ = total / 3;
        aux_done_block_start_ = aux_block_size_;
        aux_todo_block_start_ = 2 * aux_block_size_;
        for (int pos = 0; pos < aux_block_size_; ++pos) {
            const auto* target = parsed_aux_at(pos);
            const auto* done = parsed_aux_at(aux_done_block_start_ + pos);
            const auto* todo = parsed_aux_at(aux_todo_block_start_ + pos);
            if (target == nullptr || done == nullptr || todo == nullptr ||
                target->role != kAuxTarget || done->role != kAuxDone || todo->role != kAuxTodo ||
                target->base_u_idx != done->base_u_idx || target->base_u_idx != todo->base_u_idx ||
                target->sat_mask != done->sat_mask || target->sat_mask != todo->sat_mask) {
                throw std::runtime_error("aux unary order must be aligned [target][done][todo] blocks");
            }
        }
    }

    const AuxUnaryParsed* parsed_aux_at(int aux_idx) {
        if (parsed_aux_cache_.empty()) {
            parsed_aux_cache_.resize(static_cast<std::size_t>(aux_spec_->unary_count()));
            std::unordered_map<std::string, int> base_name_to_idx;
            for (int u = 0; u < spec_.unary_count(); ++u) {
                base_name_to_idx.emplace(interner_.str(spec_.unary_name_sids.at(static_cast<std::size_t>(u))), u);
            }
            for (int idx = 0; idx < aux_spec_->unary_count(); ++idx) {
                auto parsed = parse_aux_unary_name(
                    aux_spec_->unary_name_sids.at(static_cast<std::size_t>(idx)),
                    spec_,
                    base_name_to_idx,
                    interner_
                );
                if (!parsed.has_value()) {
                    return nullptr;
                }
                parsed_aux_cache_[static_cast<std::size_t>(idx)] = *parsed;
            }
        }
        return &parsed_aux_cache_.at(static_cast<std::size_t>(aux_idx));
    }

    int aux_index_of(int unary_idx, int role, int sat_mask) const {
        AuxIndexKey key{unary_idx, role, sat_mask};
        auto it = aux_index_.find(key);
        if (it == aux_index_.end()) {
            throw std::runtime_error("Missing aux config index in OBDD stage2 engine");
        }
        return it->second;
    }

    void move_done_to_todo(std::vector<int>& aux_config) const {
        for (int offset = 0; offset < aux_block_size_; ++offset) {
            int done_idx = aux_done_block_start_ + offset;
            int todo_idx = aux_todo_block_start_ + offset;
            aux_config[static_cast<std::size_t>(todo_idx)] += aux_config[static_cast<std::size_t>(done_idx)];
            aux_config[static_cast<std::size_t>(done_idx)] = 0;
        }
    }

    std::vector<int> init_aux_config(const std::vector<int>& unary_assign, const std::vector<int>& sat_masks) const {
        std::vector<int> config(static_cast<std::size_t>(aux_spec_->unary_count()), 0);
        config[static_cast<std::size_t>(aux_index_of(unary_assign[0], kAuxTarget, sat_masks[0]))] += 1;
        for (std::size_t idx = 1; idx < unary_assign.size(); ++idx) {
            config[static_cast<std::size_t>(aux_index_of(unary_assign[idx], kAuxTodo, sat_masks[idx]))] += 1;
        }
        return config;
    }

    const fo2::TypeSystemId& spec_;
    const fo2::TypeSystemId* aux_spec_ = nullptr;
    int n_ = 0;
    std::vector<std::pair<int, int>> pair_order_;
    const AtomOrder& atom_order_;
    ObddManager& manager_;
    fo2::InternTable& interner_;
    int all_sat_mask_ = 0;
    std::vector<int> unary_sat_mask_;
    std::vector<std::pair<int, int>> binary_sat_mask_;
    std::unique_ptr<AuxConfigSATChecker> aux_config_checker_;

    CandidateSetRegistry candidate_registry_;
    std::vector<int> btype_candidate_set_;
    VectorStateRegistry pair_suffix_registry_;
    VectorStateRegistry sat_state_registry_;
    std::unordered_map<std::vector<int>, std::vector<std::vector<int>>, VectorIntHash> pair_signature_suffix_cache_;
    std::unordered_map<SubcircuitMainKey, int, SubcircuitMainKeyHash> subcircuit_cache_;
    std::unordered_map<GroupedBTypesKey, std::vector<std::pair<std::pair<int, int>, std::vector<int>>>, GroupedBTypesKeyHash> grouped_btypes_cache_;
    std::unordered_map<BinaryGroupCubeKey, int, BinaryGroupCubeKeyHash> binary_group_cube_cache_;

    std::unordered_map<AuxIndexKey, int, AuxIndexKeyHash> aux_index_;
    std::vector<AuxUnaryParsed> parsed_aux_cache_;
    int aux_block_size_ = 0;
    int aux_done_block_start_ = 0;
    int aux_todo_block_start_ = 0;
};

class ObddCompiler {
public:
    ObddCompiler(
        const fo2::TypeSystemId& spec,
        const fo2::TypeSystemId* aux_spec,
        int domain_size,
        const fs::path& json_spec_path,
        fo2::InternTable& interner
    )
        : spec_(spec),
          aux_spec_(aux_spec),
          n_(domain_size),
          json_spec_path_(json_spec_path),
          interner_(interner),
          atom_order_(spec, domain_size, interner),
          pair_order_(atom_order_.pairs()),
          manager_(atom_order_.atom_names()),
          sat_checker_(spec, domain_size, pair_order_) {
        unary_clause_cache_.reserve(static_cast<std::size_t>(std::max(1, domain_size * spec.unary_count())));
        maybe_prepare_independence();
        if (component_engines_.empty()) {
            full_engine_ = std::make_unique<ObddStage2Engine>(
                spec_,
                aux_spec_,
                n_,
                pair_order_,
                atom_order_,
                manager_,
                interner_
            );
        }
    }

    int compile() {
        std::vector<int> unary_assign;
        unary_assign.reserve(static_cast<std::size_t>(n_));
        std::vector<int> config(static_cast<std::size_t>(spec_.unary_count()), 0);
        return stage_i(0, unary_assign, config);
    }

    ObddManager& manager() { return manager_; }
    const AtomOrder& atom_order() const { return atom_order_; }

private:
    void maybe_prepare_independence() {
        if (aux_spec_ == nullptr || spec_.existential_count() == 0) {
            return;
        }
        IndependenceAnalysisReport report = analyze_independence_and_build_components(
            spec_,
            *aux_spec_,
            interner_,
            std::nullopt
        );
        if (!report.valid || !report.has_split) {
            return;
        }
        for (const auto& comp : report.components) {
            component_specs_.push_back(comp.main_spec);
            component_aux_specs_.push_back(comp.aux_spec);
        }
        for (std::size_t idx = 0; idx < component_specs_.size(); ++idx) {
            component_engines_.push_back(std::make_unique<ObddStage2Engine>(
                component_specs_[idx],
                &component_aux_specs_[idx],
                n_,
                pair_order_,
                atom_order_,
                manager_,
                interner_
            ));
        }
    }

    int stage_i(int idx, std::vector<int>& unary_assign, std::vector<int>& config) {
        if (idx == n_) {
            if (!component_engines_.empty()) {
                int out = ObddManager::kTrue;
                for (auto& engine : component_engines_) {
                    out = manager_.apply_and(out, engine->compile_from_unary(unary_assign));
                    if (out == ObddManager::kFalse) {
                        break;
                    }
                }
                return out;
            }
            return full_engine_->compile_from_unary(unary_assign);
        }

        int result = ObddManager::kFalse;
        for (int uidx = 0; uidx < spec_.unary_count(); ++uidx) {
            unary_assign.push_back(uidx);
            config[static_cast<std::size_t>(uidx)] += 1;

            if (sat_checker_.check(unary_assign, config)) {
                int cube = unary_clause(idx, uidx);
                if (cube != ObddManager::kFalse) {
                    int suffix = stage_i(idx + 1, unary_assign, config);
                    result = manager_.apply_or(result, manager_.apply_and(cube, suffix));
                }
            }

            config[static_cast<std::size_t>(uidx)] -= 1;
            unary_assign.pop_back();
        }
        return result;
    }

    int unary_clause(int x, int uidx) {
        std::uint64_t key = (static_cast<std::uint64_t>(static_cast<std::uint32_t>(x)) << 32U) |
                            static_cast<std::uint32_t>(uidx);
        auto it = unary_clause_cache_.find(key);
        if (it != unary_clause_cache_.end()) {
            return it->second;
        }
        int node = manager_.cube(atom_order_.unary_cube(x, uidx));
        unary_clause_cache_.emplace(key, node);
        return node;
    }

    const fo2::TypeSystemId& spec_;
    const fo2::TypeSystemId* aux_spec_ = nullptr;
    int n_ = 0;
    fs::path json_spec_path_;
    fo2::InternTable& interner_;
    AtomOrder atom_order_;
    std::vector<std::pair<int, int>> pair_order_;
    ObddManager manager_;
    SATChecker sat_checker_;
    std::unique_ptr<ObddStage2Engine> full_engine_;
    std::deque<fo2::TypeSystemId> component_specs_;
    std::deque<fo2::TypeSystemId> component_aux_specs_;
    std::vector<std::unique_ptr<ObddStage2Engine>> component_engines_;
    std::unordered_map<std::uint64_t, int> unary_clause_cache_;
};

struct ObddCliArgs {
    int domain_size = 0;
    std::string json_spec;
    std::optional<std::string> out;
    bool order = false;
};

[[noreturn]] static void obdd_cli_error(const std::string& msg) {
    throw std::runtime_error(msg);
}

static ObddCliArgs parse_obdd_cli(int argc, char** argv) {
    ObddCliArgs args;
    for (int i = 1; i < argc; ++i) {
        std::string cur = argv[i];
        if (cur == "-n" || cur == "--domain-size") {
            if (i + 1 >= argc) {
                obdd_cli_error("Missing value for " + cur);
            }
            args.domain_size = std::stoi(argv[++i]);
            continue;
        }
        if (cur == "--json-spec") {
            if (i + 1 >= argc) {
                obdd_cli_error("Missing value for --json-spec");
            }
            args.json_spec = argv[++i];
            continue;
        }
        if (cur == "-o" || cur == "--out") {
            if (i + 1 >= argc) {
                obdd_cli_error("Missing value for " + cur);
            }
            args.out = argv[++i];
            continue;
        }
        if (cur == "--order") {
            args.order = true;
            continue;
        }
        if (cur == "-h" || cur == "--help") {
            std::cout
                << "Usage: obdd_compile_cpp --json-spec <path> -n <domain_size> [-o <dot_file>] [--order]\n"
                << "Options:\n"
                << "  --json-spec <path>       Path to JSON spec (required)\n"
                << "  -n, --domain-size <int>  Domain size n (required, >0)\n"
                << "  -o, --out <path>         Optional DOT output path\n"
                << "  --order                  Print atom variable order\n";
            std::exit(0);
        }
        obdd_cli_error("Unknown argument: " + cur);
    }
    if (args.domain_size <= 0) {
        obdd_cli_error("--domain-size must be > 0");
    }
    if (args.json_spec.empty()) {
        obdd_cli_error("--json-spec is required");
    }
    return args;
}

static fs::path derive_aux_spec_path_obdd(const fs::path& json_spec_path) {
    if (json_spec_path.has_extension()) {
        return json_spec_path.parent_path() /
            (json_spec_path.stem().string() + "_aux" + json_spec_path.extension().string());
    }
    return json_spec_path.parent_path() / (json_spec_path.filename().string() + "_aux.json");
}

int run_obdd_main(int argc, char** argv) {
    try {
        const auto start = std::chrono::steady_clock::now();
        ObddCliArgs args = parse_obdd_cli(argc, argv);

        fo2::InternTable interner;
        fs::path spec_path(args.json_spec);
        fo2::TypeSystemId spec = fo2::load_typesystem_id_from_json(spec_path, interner);
        std::optional<fo2::TypeSystemId> aux_spec;
        fs::path aux_path = derive_aux_spec_path_obdd(spec_path);
        if (spec.existential_count() > 0 && fs::exists(aux_path)) {
            aux_spec = fo2::load_typesystem_id_from_json(aux_path, interner);
        }

        auto compiler = std::make_unique<ObddCompiler>(
            spec,
            aux_spec.has_value() ? &*aux_spec : nullptr,
            args.domain_size,
            spec_path,
            interner
        );
        int root = compiler->compile();
        std::size_t nodes = compiler->manager().reachable_nonterminal_count(root);
        std::size_t atom_vars = compiler->manager().atom_names().size();
        BigUInt model_count = compiler->manager().model_count(root);

        if (args.out.has_value()) {
            compiler->manager().write_dot(root, fs::path(*args.out));
        }

        const auto end = std::chrono::steady_clock::now();
        double seconds = std::chrono::duration<double>(end - start).count();

        std::cout << "OBDD nodes: " << nodes << "\n";
        std::cout << "Atom variables: " << atom_vars << "\n";
        std::cout << "Model count: " << model_count << "\n";
        std::cout << "Time: " << std::fixed << std::setprecision(6) << seconds << "s\n";
        if (args.out.has_value()) {
            std::cout << "DOT saved: " << *args.out << "\n";
        }
        if (args.order) {
            std::cout << "Variable order:\n";
            const auto& names = compiler->manager().atom_names();
            for (std::size_t i = 0; i < names.size(); ++i) {
                std::cout << "  " << i << ": " << names[i] << "\n";
            }
        }
        std::cout.flush();
        (void)compiler.release();
        return 0;
    } catch (const std::exception& ex) {
        std::cerr << "Error: " << ex.what() << "\n";
        return 1;
    }
}
