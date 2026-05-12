#include "cudd_core.hpp"

#include <cstddef>
#include <cstdio>

#include "cudd.h"

#include <algorithm>
#include <chrono>
#include <cstdlib>
#include <cstdint>
#include <filesystem>
#include <fstream>
#include <iomanip>
#include <iostream>
#include <limits>
#include <optional>
#include <set>
#include <sstream>
#include <stdexcept>
#include <string>
#include <unordered_map>
#include <unordered_set>
#include <utility>
#include <vector>

namespace {

namespace fs = std::filesystem;

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
        if (carry != 0U) {
            limbs_.push_back(static_cast<std::uint32_t>(carry));
        }
        return *this;
    }

    BigUInt& operator<<=(std::size_t bits) {
        if (bits == 0 || is_zero()) {
            return *this;
        }
        const std::size_t word_shift = bits / 32U;
        const unsigned bit_shift = static_cast<unsigned>(bits % 32U);
        if (word_shift > 0) {
            limbs_.insert(limbs_.begin(), word_shift, 0U);
        }
        if (bit_shift > 0U) {
            std::uint64_t carry = 0;
            for (std::size_t i = 0; i < limbs_.size(); ++i) {
                std::uint64_t cur = (static_cast<std::uint64_t>(limbs_[i]) << bit_shift) | carry;
                limbs_[i] = static_cast<std::uint32_t>(cur & 0xFFFFFFFFULL);
                carry = cur >> 32U;
            }
            if (carry != 0U) {
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
        if (v == 0U) {
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

struct CnfFile {
    fs::path path;
    std::vector<std::string> atom_names;
    std::vector<int> atom_ids;
    int declared_var_count = 0;
    int declared_clause_count = 0;
    std::vector<std::vector<int>> clauses;
};

enum class ReorderMode {
    AutoFinal,
    FinalOnly,
};

struct CuddCliArgs {
    std::string cnf_path;
    std::optional<std::string> out;
    bool order = false;
    bool profile = false;
    Cudd_ReorderingType reorder_type = CUDD_REORDER_SIFT;
    ReorderMode reorder_mode = ReorderMode::AutoFinal;
};

struct ProfileTimings {
    double parse_cnf = 0.0;
    double init_and_vars = 0.0;
    double build_cnf_bdd = 0.0;
    double hidden_scan = 0.0;
    double existential_projection = 0.0;
    double final_reorder = 0.0;
    double model_count = 0.0;
    double explicit_materialize = 0.0;
    double write_dot = 0.0;
    double atom_order = 0.0;
    double total = 0.0;
    double cudd_reordering_time = 0.0;
    unsigned int cudd_reorderings = 0;
    long cudd_live_nodes = 0;
};

class CuddManagerHandle {
public:
    explicit CuddManagerHandle(int num_vars) {
        dd_ = Cudd_Init(
            static_cast<unsigned int>(num_vars),
            0,
            CUDD_UNIQUE_SLOTS,
            CUDD_CACHE_SLOTS,
            0
        );
        if (dd_ == nullptr) {
            throw std::runtime_error("Cudd_Init failed");
        }
    }

    CuddManagerHandle(const CuddManagerHandle&) = delete;
    CuddManagerHandle& operator=(const CuddManagerHandle&) = delete;

    ~CuddManagerHandle() {
        if (dd_ != nullptr) {
            Cudd_Quit(dd_);
        }
    }

    DdManager* get() const {
        return dd_;
    }

private:
    DdManager* dd_ = nullptr;
};

[[noreturn]] void cli_error(const std::string& message) {
    throw std::runtime_error(
        message +
        "\nUsage: ./cudd_compile_cpp --cnf <path> [-o <dot_file>] [--order] "
        "[--profile] [--reorder <sift|group-sift|window2|window3|window4>] "
        "[--reorder-mode <auto-final|final-only>]"
    );
}

double elapsed_seconds(std::chrono::steady_clock::time_point start) {
    return std::chrono::duration<double>(std::chrono::steady_clock::now() - start).count();
}

Cudd_ReorderingType parse_reorder_type(const std::string& value) {
    if (value == "sift") {
        return CUDD_REORDER_SIFT;
    }
    if (value == "group-sift" || value == "group_sift" || value == "groupsift") {
        return CUDD_REORDER_GROUP_SIFT;
    }
    if (value == "window2" || value == "window-2" || value == "window_2") {
        return CUDD_REORDER_WINDOW2;
    }
    if (value == "window3" || value == "window-3" || value == "window_3") {
        return CUDD_REORDER_WINDOW3;
    }
    if (value == "window4" || value == "window-4" || value == "window_4") {
        return CUDD_REORDER_WINDOW4;
    }
    cli_error("unknown --reorder strategy: " + value);
}

ReorderMode parse_reorder_mode(const std::string& value) {
    if (value == "auto-final" || value == "auto_final" || value == "auto") {
        return ReorderMode::AutoFinal;
    }
    if (value == "final-only" || value == "final_only" || value == "final") {
        return ReorderMode::FinalOnly;
    }
    cli_error("unknown --reorder-mode: " + value);
}

std::vector<std::string> split_ws(const std::string& line) {
    std::istringstream iss(line);
    std::vector<std::string> out;
    std::string tok;
    while (iss >> tok) {
        out.push_back(tok);
    }
    return out;
}

std::vector<std::string> parse_comment_payload(const std::string& line, const std::string& description) {
    std::vector<std::string> parts = split_ws(line);
    if (parts.empty() || parts[0] != "c") {
        throw std::runtime_error("expected first token of " + description + " to be `c`: " + line);
    }
    parts.erase(parts.begin());
    if (parts.empty()) {
        throw std::runtime_error("empty " + description + ": " + line);
    }
    return parts;
}

int parse_int_token(const std::string& token, const std::string& context) {
    std::size_t used = 0;
    int value = 0;
    try {
        value = std::stoi(token, &used, 10);
    } catch (const std::exception&) {
        throw std::runtime_error("non-integer token in " + context + ": " + token);
    }
    if (used != token.size()) {
        throw std::runtime_error("non-integer token in " + context + ": " + token);
    }
    return value;
}

CnfFile read_atom_header_dimacs_cnf(const fs::path& path) {
    std::ifstream in(path);
    if (!in) {
        throw std::runtime_error("failed to open CNF file: " + path.string());
    }

    std::vector<std::string> lines;
    std::string line;
    while (std::getline(in, line)) {
        if (!line.empty() && line.back() == '\r') {
            line.pop_back();
        }
        lines.push_back(line);
    }
    if (lines.size() < 3) {
        throw std::runtime_error("CNF file is too short: " + path.string());
    }

    CnfFile cnf;
    cnf.path = path;
    cnf.atom_names = parse_comment_payload(lines[0], "atom-name header");
    std::vector<std::string> atom_id_tokens = parse_comment_payload(lines[1], "atom-id header");
    if (cnf.atom_names.size() != atom_id_tokens.size()) {
        throw std::runtime_error(
            "atom-name and atom-id headers have different lengths in " + path.string()
        );
    }

    std::unordered_set<std::string> seen_names;
    std::unordered_set<int> seen_ids;
    for (const std::string& name : cnf.atom_names) {
        if (!seen_names.insert(name).second) {
            throw std::runtime_error("duplicate atom name in CNF header: " + name);
        }
    }
    for (const std::string& tok : atom_id_tokens) {
        int id = parse_int_token(tok, "atom-id header");
        if (id <= 0) {
            throw std::runtime_error("atom ids must be positive DIMACS ids: " + tok);
        }
        if (!seen_ids.insert(id).second) {
            throw std::runtime_error("duplicate atom id in CNF header: " + tok);
        }
        cnf.atom_ids.push_back(id);
    }

    std::optional<int> declared_var_count;
    std::optional<int> declared_clause_count;
    std::vector<int> current_clause;

    for (std::size_t idx = 2; idx < lines.size(); ++idx) {
        const std::string& raw = lines[idx];
        std::vector<std::string> parts = split_ws(raw);
        if (parts.empty()) {
            continue;
        }
        if (parts[0] == "c") {
            continue;
        }
        if (parts[0] == "p") {
            if (parts.size() != 4 || parts[1] != "cnf") {
                throw std::runtime_error("unsupported DIMACS problem line at " + path.string());
            }
            declared_var_count = parse_int_token(parts[2], "DIMACS problem line");
            declared_clause_count = parse_int_token(parts[3], "DIMACS problem line");
            if (*declared_var_count < 0 || *declared_clause_count < 0) {
                throw std::runtime_error("DIMACS variable and clause counts must be non-negative");
            }
            continue;
        }
        if (!declared_var_count.has_value()) {
            throw std::runtime_error("clause appears before `p cnf` line in " + path.string());
        }

        for (const std::string& tok : parts) {
            int lit = parse_int_token(tok, "DIMACS clause");
            if (lit == 0) {
                cnf.clauses.push_back(current_clause);
                current_clause.clear();
                continue;
            }
            if (std::abs(lit) > *declared_var_count) {
                throw std::runtime_error("literal id exceeds declared variable count in " + path.string());
            }
            current_clause.push_back(lit);
        }
    }

    if (!declared_var_count.has_value() || !declared_clause_count.has_value()) {
        throw std::runtime_error("missing `p cnf <vars> <clauses>` line in " + path.string());
    }
    if (!current_clause.empty()) {
        throw std::runtime_error("last DIMACS clause is missing terminating 0 in " + path.string());
    }
    int max_atom_id = 0;
    for (int id : cnf.atom_ids) {
        max_atom_id = std::max(max_atom_id, id);
    }
    if (max_atom_id > *declared_var_count) {
        throw std::runtime_error("atom id exceeds declared variable count in " + path.string());
    }
    if (static_cast<int>(cnf.clauses.size()) != *declared_clause_count) {
        throw std::runtime_error("declared clause count mismatch in " + path.string());
    }

    cnf.declared_var_count = *declared_var_count;
    cnf.declared_clause_count = *declared_clause_count;
    return cnf;
}

CuddCliArgs parse_cli(int argc, char** argv) {
    CuddCliArgs args;
    for (int i = 1; i < argc; ++i) {
        std::string arg = argv[i];
        if (arg == "--cnf") {
            if (i + 1 >= argc) {
                cli_error("--cnf requires a path");
            }
            args.cnf_path = argv[++i];
        } else if (arg == "-o") {
            if (i + 1 >= argc) {
                cli_error("-o requires a path");
            }
            args.out = std::string(argv[++i]);
        } else if (arg == "--order") {
            args.order = true;
        } else if (arg == "--profile") {
            args.profile = true;
        } else if (arg == "--reorder") {
            if (i + 1 >= argc) {
                cli_error("--reorder requires one of: sift, group-sift, window2, window3, window4");
            }
            args.reorder_type = parse_reorder_type(argv[++i]);
        } else if (arg == "--reorder-mode") {
            if (i + 1 >= argc) {
                cli_error("--reorder-mode requires one of: auto-final, final-only");
            }
            args.reorder_mode = parse_reorder_mode(argv[++i]);
        } else if (arg == "-h" || arg == "--help") {
            std::cout
                << "Usage: ./cudd_compile_cpp --cnf <path> [-o <dot_file>] [--order] "
                << "[--profile] [--reorder <sift|group-sift|window2|window3|window4>] "
                << "[--reorder-mode <auto-final|final-only>]\n";
            std::exit(0);
        } else {
            cli_error("unknown argument: " + arg);
        }
    }
    if (args.cnf_path.empty()) {
        cli_error("--cnf is required");
    }
    return args;
}

DdNode* cudd_checked(DdNode* node, const std::string& operation) {
    if (node == nullptr) {
        throw std::runtime_error("CUDD returned null during " + operation);
    }
    return node;
}

bool is_true(DdManager* dd, DdNode* f) {
    return f == Cudd_ReadOne(dd);
}

bool is_false(DdManager* dd, DdNode* f) {
    return f == Cudd_Not(Cudd_ReadOne(dd));
}

std::uintptr_t node_key(DdNode* f) {
    return reinterpret_cast<std::uintptr_t>(f);
}

DdNode* node_high(DdNode* f) {
    DdNode* regular = Cudd_Regular(f);
    DdNode* high = Cudd_T(regular);
    return Cudd_IsComplement(f) ? Cudd_Not(high) : high;
}

DdNode* node_low(DdNode* f) {
    DdNode* regular = Cudd_Regular(f);
    DdNode* low = Cudd_E(regular);
    return Cudd_IsComplement(f) ? Cudd_Not(low) : low;
}

DdNode* build_cnf_bdd(DdManager* dd, const CnfFile& cnf) {
    DdNode* root = Cudd_ReadOne(dd);
    Cudd_Ref(root);

    try {
        for (const auto& clause_lits : cnf.clauses) {
            DdNode* clause = Cudd_Not(Cudd_ReadOne(dd));
            Cudd_Ref(clause);

            for (int lit : clause_lits) {
                int id = std::abs(lit);
                DdNode* var = cudd_checked(Cudd_bddIthVar(dd, id - 1), "Cudd_bddIthVar");
                DdNode* lit_node = lit < 0 ? Cudd_Not(var) : var;
                DdNode* next_clause = cudd_checked(Cudd_bddOr(dd, clause, lit_node), "clause OR");
                Cudd_Ref(next_clause);
                Cudd_RecursiveDeref(dd, clause);
                clause = next_clause;
            }

            DdNode* next_root = cudd_checked(Cudd_bddAnd(dd, root, clause), "root AND clause");
            Cudd_Ref(next_root);
            Cudd_RecursiveDeref(dd, root);
            Cudd_RecursiveDeref(dd, clause);
            root = next_root;
        }
    } catch (...) {
        Cudd_RecursiveDeref(dd, root);
        throw;
    }

    return root;
}

DdNode* build_hidden_cube(DdManager* dd, const std::vector<int>& hidden_ids) {
    DdNode* cube = Cudd_ReadOne(dd);
    Cudd_Ref(cube);

    try {
        for (int id : hidden_ids) {
            DdNode* var = cudd_checked(Cudd_bddIthVar(dd, id - 1), "Cudd_bddIthVar");
            DdNode* next = cudd_checked(Cudd_bddAnd(dd, cube, var), "hidden cube AND");
            Cudd_Ref(next);
            Cudd_RecursiveDeref(dd, cube);
            cube = next;
        }
    } catch (...) {
        Cudd_RecursiveDeref(dd, cube);
        throw;
    }

    return cube;
}

DdNode* project_hidden_variables(DdManager* dd, DdNode* root, const std::vector<int>& hidden_ids) {
    if (hidden_ids.empty()) {
        Cudd_Ref(root);
        return root;
    }

    DdNode* cube = build_hidden_cube(dd, hidden_ids);
    DdNode* projected = nullptr;
    try {
        projected = cudd_checked(Cudd_bddExistAbstract(dd, root, cube), "existential abstraction");
        Cudd_Ref(projected);
    } catch (...) {
        Cudd_RecursiveDeref(dd, cube);
        throw;
    }
    Cudd_RecursiveDeref(dd, cube);
    return projected;
}

std::vector<int> hidden_dimacs_ids(const CnfFile& cnf) {
    std::vector<char> is_atom(static_cast<std::size_t>(cnf.declared_var_count + 1), 0);
    for (int id : cnf.atom_ids) {
        is_atom[static_cast<std::size_t>(id)] = 1;
    }
    std::vector<int> out;
    for (int id = 1; id <= cnf.declared_var_count; ++id) {
        if (!is_atom[static_cast<std::size_t>(id)]) {
            out.push_back(id);
        }
    }
    return out;
}

std::vector<int> atom_ids_in_final_order(DdManager* dd, const CnfFile& cnf) {
    std::vector<int> ids = cnf.atom_ids;
    std::sort(ids.begin(), ids.end(), [dd](int a, int b) {
        int la = Cudd_ReadPerm(dd, a - 1);
        int lb = Cudd_ReadPerm(dd, b - 1);
        if (la != lb) {
            return la < lb;
        }
        return a < b;
    });
    return ids;
}

std::vector<std::string> atom_order_labels(DdManager* dd, const CnfFile& cnf) {
    std::unordered_map<int, std::string> label_by_id;
    for (std::size_t i = 0; i < cnf.atom_ids.size(); ++i) {
        label_by_id[cnf.atom_ids[i]] = cnf.atom_names[i];
    }
    std::vector<std::string> labels;
    for (int id : atom_ids_in_final_order(dd, cnf)) {
        labels.push_back(label_by_id.at(id));
    }
    return labels;
}

class ExactModelCounter {
public:
    ExactModelCounter(DdManager* dd, const CnfFile& cnf)
        : dd_(dd), atom_count_(cnf.atom_ids.size()) {
        std::vector<int> ordered = atom_ids_in_final_order(dd, cnf);
        for (std::size_t pos = 0; pos < ordered.size(); ++pos) {
            atom_position_by_index_[ordered[pos] - 1] = pos;
        }
    }

    BigUInt count(DdNode* root) {
        return rec(root, 0);
    }

private:
    struct MemoKey {
        std::uintptr_t node = 0;
        std::size_t pos = 0;

        bool operator==(const MemoKey& other) const noexcept {
            return node == other.node && pos == other.pos;
        }
    };

    struct MemoKeyHash {
        std::size_t operator()(const MemoKey& k) const noexcept {
            std::size_t seed = std::hash<std::uintptr_t>{}(k.node);
            seed ^= std::hash<std::size_t>{}(k.pos) + 0x9e3779b97f4a7c15ULL + (seed << 6U) + (seed >> 2U);
            return seed;
        }
    };

    BigUInt pow2(std::size_t bits) const {
        BigUInt out(1);
        out <<= bits;
        return out;
    }

    BigUInt rec(DdNode* u, std::size_t pos) {
        MemoKey key{node_key(u), pos};
        auto it = memo_.find(key);
        if (it != memo_.end()) {
            return it->second;
        }
        if (is_false(dd_, u)) {
            return BigUInt(0);
        }
        if (is_true(dd_, u)) {
            return pow2(atom_count_ - pos);
        }

        DdNode* regular = Cudd_Regular(u);
        int index = static_cast<int>(Cudd_NodeReadIndex(regular));
        auto pos_it = atom_position_by_index_.find(index);
        if (pos_it == atom_position_by_index_.end()) {
            throw std::runtime_error(
                "projected BDD still depends on non-atom DIMACS variable " +
                std::to_string(index + 1)
            );
        }
        std::size_t var_pos = pos_it->second;
        if (var_pos < pos) {
            throw std::runtime_error("BDD variable order is inconsistent during model counting");
        }

        BigUInt low = rec(node_low(u), var_pos + 1);
        BigUInt high = rec(node_high(u), var_pos + 1);
        BigUInt out = low + high;
        out <<= (var_pos - pos);
        memo_.emplace(key, out);
        return out;
    }

    DdManager* dd_ = nullptr;
    std::size_t atom_count_ = 0;
    std::unordered_map<int, std::size_t> atom_position_by_index_;
    std::unordered_map<MemoKey, BigUInt, MemoKeyHash> memo_;
};

struct ExplicitTriple {
    int level = -1;
    int low = 0;
    int high = 0;

    bool operator==(const ExplicitTriple& other) const noexcept {
        return level == other.level && low == other.low && high == other.high;
    }
};

struct ExplicitTripleHash {
    std::size_t operator()(const ExplicitTriple& k) const noexcept {
        std::size_t seed = std::hash<int>{}(k.level);
        seed ^= std::hash<int>{}(k.low) + 0x9e3779b97f4a7c15ULL + (seed << 6U) + (seed >> 2U);
        seed ^= std::hash<int>{}(k.high) + 0x9e3779b97f4a7c15ULL + (seed << 6U) + (seed >> 2U);
        return seed;
    }
};

struct DotNodeInfo {
    std::string label;
    int low = 0;
    int high = 0;
};

class ExplicitObddView {
public:
    ExplicitObddView(DdManager* dd, const CnfFile& cnf)
        : dd_(dd) {
        for (std::size_t i = 0; i < cnf.atom_ids.size(); ++i) {
            label_by_index_[cnf.atom_ids[i] - 1] = cnf.atom_names[i];
        }
    }

    int materialize(DdNode* root) {
        return rec(root);
    }

    std::size_t decision_count() const {
        return unique_.size();
    }

    void write_dot(const fs::path& path, int root_id) const {
        std::ofstream out(path);
        if (!out) {
            throw std::runtime_error("failed to write DOT file: " + path.string());
        }
        out << "digraph OBDD {\n";
        out << "  rankdir=TB;\n";
        out << "  t0 [label=\"FALSE\", shape=box];\n";
        out << "  t1 [label=\"TRUE\", shape=box];\n";
        std::vector<int> ids;
        ids.reserve(node_info_.size());
        for (const auto& kv : node_info_) {
            ids.push_back(kv.first);
        }
        std::sort(ids.begin(), ids.end());
        for (int id : ids) {
            out << "  n" << id << " [label=\"" << dot_escape(node_info_.at(id).label)
                << "\", shape=circle];\n";
        }
        out << "  root [label=\"root\", shape=point];\n";
        out << "  root -> " << dot_target(root_id) << ";\n";
        for (int id : ids) {
            const DotNodeInfo& info = node_info_.at(id);
            out << "  n" << id << " -> " << dot_target(info.low) << " [label=\"0\"];\n";
            out << "  n" << id << " -> " << dot_target(info.high) << " [label=\"1\"];\n";
        }
        out << "}\n";
    }

private:
    int rec(DdNode* u) {
        if (is_false(dd_, u)) {
            terminals_seen_.insert(0);
            return 0;
        }
        if (is_true(dd_, u)) {
            terminals_seen_.insert(1);
            return 1;
        }

        std::uintptr_t key = node_key(u);
        auto memo_it = memo_.find(key);
        if (memo_it != memo_.end()) {
            return memo_it->second;
        }

        DdNode* regular = Cudd_Regular(u);
        int index = static_cast<int>(Cudd_NodeReadIndex(regular));
        int low = rec(node_low(u));
        int high = rec(node_high(u));
        if (low == high) {
            memo_[key] = low;
            return low;
        }

        ExplicitTriple triple{Cudd_ReadPerm(dd_, index), low, high};
        auto unique_it = unique_.find(triple);
        if (unique_it != unique_.end()) {
            memo_[key] = unique_it->second;
            return unique_it->second;
        }

        int id = next_node_id_++;
        unique_[triple] = id;
        auto label_it = label_by_index_.find(index);
        std::string label = (label_it == label_by_index_.end())
            ? ("v" + std::to_string(index + 1))
            : label_it->second;
        node_info_[id] = DotNodeInfo{std::move(label), low, high};
        memo_[key] = id;
        return id;
    }

    static std::string dot_escape(const std::string& s) {
        std::ostringstream oss;
        for (char ch : s) {
            if (ch == '\\') {
                oss << "\\\\";
            } else if (ch == '"') {
                oss << "\\\"";
            } else {
                oss << ch;
            }
        }
        return oss.str();
    }

    static std::string dot_target(int id) {
        if (id == 0 || id == 1) {
            return "t" + std::to_string(id);
        }
        return "n" + std::to_string(id);
    }

    DdManager* dd_ = nullptr;
    int next_node_id_ = 2;
    std::unordered_map<int, std::string> label_by_index_;
    std::unordered_map<std::uintptr_t, int> memo_;
    std::unordered_map<ExplicitTriple, int, ExplicitTripleHash> unique_;
    std::unordered_map<int, DotNodeInfo> node_info_;
    std::set<int> terminals_seen_;
};

struct CompileResult {
    std::size_t obdd_nodes = 0;
    std::size_t atom_variables = 0;
    BigUInt model_count;
    std::vector<std::string> variable_order;
    ProfileTimings profile;
};

CompileResult compile_cudd_cnf(
    const CnfFile& cnf,
    const std::optional<fs::path>& dot_path,
    Cudd_ReorderingType reorder_type,
    ReorderMode reorder_mode
) {
    ProfileTimings profile;
    auto phase_start = std::chrono::steady_clock::now();
    CuddManagerHandle manager(cnf.declared_var_count);
    DdManager* dd = manager.get();
    for (int id = 1; id <= cnf.declared_var_count; ++id) {
        cudd_checked(Cudd_bddIthVar(dd, id - 1), "Cudd_bddIthVar");
    }
    profile.init_and_vars = elapsed_seconds(phase_start);

    if (reorder_mode == ReorderMode::AutoFinal) {
        Cudd_AutodynEnable(dd, reorder_type);
    }

    phase_start = std::chrono::steady_clock::now();
    DdNode* root = build_cnf_bdd(dd, cnf);
    profile.build_cnf_bdd = elapsed_seconds(phase_start);
    phase_start = std::chrono::steady_clock::now();
    std::vector<int> hidden_ids = hidden_dimacs_ids(cnf);
    profile.hidden_scan = elapsed_seconds(phase_start);
    DdNode* projected = nullptr;
    try {
        phase_start = std::chrono::steady_clock::now();
        projected = project_hidden_variables(dd, root, hidden_ids);
        profile.existential_projection = elapsed_seconds(phase_start);
        Cudd_RecursiveDeref(dd, root);
        root = nullptr;

        phase_start = std::chrono::steady_clock::now();
        if (cnf.declared_var_count > 0) {
            if (Cudd_ReduceHeap(dd, reorder_type, 0) == 0) {
                throw std::runtime_error("Cudd_ReduceHeap failed");
            }
        }
        profile.final_reorder = elapsed_seconds(phase_start);
        if (reorder_mode == ReorderMode::AutoFinal) {
            Cudd_AutodynDisable(dd);
        }

        phase_start = std::chrono::steady_clock::now();
        ExactModelCounter counter(dd, cnf);
        BigUInt model_count = counter.count(projected);
        profile.model_count = elapsed_seconds(phase_start);

        phase_start = std::chrono::steady_clock::now();
        ExplicitObddView explicit_view(dd, cnf);
        int explicit_root = explicit_view.materialize(projected);
        profile.explicit_materialize = elapsed_seconds(phase_start);
        if (dot_path.has_value()) {
            phase_start = std::chrono::steady_clock::now();
            explicit_view.write_dot(*dot_path, explicit_root);
            profile.write_dot = elapsed_seconds(phase_start);
        }

        CompileResult result;
        result.obdd_nodes = explicit_view.decision_count();
        result.atom_variables = cnf.atom_ids.size();
        result.model_count = model_count;
        phase_start = std::chrono::steady_clock::now();
        result.variable_order = atom_order_labels(dd, cnf);
        profile.atom_order = elapsed_seconds(phase_start);
        profile.cudd_reorderings = Cudd_ReadReorderings(dd);
        profile.cudd_reordering_time = static_cast<double>(Cudd_ReadReorderingTime(dd)) / 1000.0;
        profile.cudd_live_nodes = Cudd_ReadNodeCount(dd);
        result.profile = profile;

        Cudd_RecursiveDeref(dd, projected);
        projected = nullptr;
        return result;
    } catch (...) {
        if (root != nullptr) {
            Cudd_RecursiveDeref(dd, root);
        }
        if (projected != nullptr) {
            Cudd_RecursiveDeref(dd, projected);
        }
        throw;
    }
}

} // namespace

int run_cudd_main(int argc, char** argv) {
    try {
        const auto start = std::chrono::steady_clock::now();
        CuddCliArgs args = parse_cli(argc, argv);
        fs::path cnf_path(args.cnf_path);
        std::optional<fs::path> dot_path;
        if (args.out.has_value()) {
            dot_path = fs::path(*args.out);
        }

        auto phase_start = std::chrono::steady_clock::now();
        CnfFile cnf = read_atom_header_dimacs_cnf(cnf_path);
        double parse_cnf_seconds = elapsed_seconds(phase_start);
        CompileResult result = compile_cudd_cnf(
            cnf,
            dot_path,
            args.reorder_type,
            args.reorder_mode
        );

        const auto end = std::chrono::steady_clock::now();
        double seconds = std::chrono::duration<double>(end - start).count();
        result.profile.parse_cnf = parse_cnf_seconds;
        result.profile.total = seconds;

        std::cout << "OBDD nodes: " << result.obdd_nodes << "\n";
        std::cout << "Atom variables: " << result.atom_variables << "\n";
        std::cout << "Model count: " << result.model_count << "\n";
        std::cout << "Time: " << std::fixed << std::setprecision(6) << seconds << "s\n";
        if (dot_path.has_value()) {
            std::cout << "DOT saved: " << dot_path->string() << "\n";
        }
        if (args.order) {
            std::cout << "Variable order:\n";
            for (std::size_t i = 0; i < result.variable_order.size(); ++i) {
                std::cout << "  " << i << ": " << result.variable_order[i] << "\n";
            }
        }
        if (args.profile) {
            const ProfileTimings& p = result.profile;
            auto print_phase = [](const char* name, double value) {
                std::cout << "  " << name << ": " << std::fixed << std::setprecision(6)
                          << value << "s\n";
            };
            std::cout << "Profile:\n";
            print_phase("parse_cnf", p.parse_cnf);
            print_phase("init_and_vars", p.init_and_vars);
            print_phase("build_cnf_bdd", p.build_cnf_bdd);
            print_phase("hidden_scan", p.hidden_scan);
            print_phase("existential_projection", p.existential_projection);
            print_phase("final_reorder", p.final_reorder);
            print_phase("model_count", p.model_count);
            print_phase("explicit_materialize", p.explicit_materialize);
            print_phase("write_dot", p.write_dot);
            print_phase("atom_order", p.atom_order);
            print_phase("cudd_reordering_time", p.cudd_reordering_time);
            std::cout << "  cudd_reorderings: " << p.cudd_reorderings << "\n";
            std::cout << "  cudd_live_nodes_after_compile: " << p.cudd_live_nodes << "\n";
        }
        return 0;
    } catch (const std::exception& ex) {
        std::cerr << "Error: " << ex.what() << "\n";
        return 1;
    }
}
