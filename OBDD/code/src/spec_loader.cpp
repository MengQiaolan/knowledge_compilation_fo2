#include "spec_loader.hpp"

#include <algorithm>
#include <cctype>
#include <cmath>
#include <cstddef>
#include <cstring>
#include <fstream>
#include <map>
#include <optional>
#include <set>
#include <sstream>
#include <stdexcept>
#include <string>
#include <unordered_map>
#include <unordered_set>
#include <utility>
#include <variant>
#include <vector>

namespace fo2 {
namespace {

class JsonValue {
public:
    using Object = std::map<std::string, JsonValue>;
    using Array = std::vector<JsonValue>;

    JsonValue() : data_(nullptr) {}
    explicit JsonValue(std::nullptr_t) : data_(nullptr) {}
    explicit JsonValue(bool b) : data_(b) {}
    explicit JsonValue(double d) : data_(d) {}
    explicit JsonValue(std::string s) : data_(std::move(s)) {}
    explicit JsonValue(Array a) : data_(std::move(a)) {}
    explicit JsonValue(Object o) : data_(std::move(o)) {}

    bool is_null() const { return std::holds_alternative<std::nullptr_t>(data_); }
    bool is_bool() const { return std::holds_alternative<bool>(data_); }
    bool is_number() const { return std::holds_alternative<double>(data_); }
    bool is_string() const { return std::holds_alternative<std::string>(data_); }
    bool is_array() const { return std::holds_alternative<Array>(data_); }
    bool is_object() const { return std::holds_alternative<Object>(data_); }

    bool as_bool() const {
        if (!is_bool()) {
            throw std::runtime_error("JSON value is not bool");
        }
        return std::get<bool>(data_);
    }

    double as_number() const {
        if (!is_number()) {
            throw std::runtime_error("JSON value is not number");
        }
        return std::get<double>(data_);
    }

    const std::string& as_string() const {
        if (!is_string()) {
            throw std::runtime_error("JSON value is not string");
        }
        return std::get<std::string>(data_);
    }

    const Array& as_array() const {
        if (!is_array()) {
            throw std::runtime_error("JSON value is not array");
        }
        return std::get<Array>(data_);
    }

    const Object& as_object() const {
        if (!is_object()) {
            throw std::runtime_error("JSON value is not object");
        }
        return std::get<Object>(data_);
    }

    const JsonValue* get(const std::string& key) const {
        if (!is_object()) {
            return nullptr;
        }
        const auto& obj = std::get<Object>(data_);
        auto it = obj.find(key);
        if (it == obj.end()) {
            return nullptr;
        }
        return &it->second;
    }

private:
    std::variant<std::nullptr_t, bool, double, std::string, Array, Object> data_;
};

class JsonParser {
public:
    explicit JsonParser(std::string text) : text_(std::move(text)), pos_(0) {}

    JsonValue parse() {
        skip_ws();
        JsonValue v = parse_value();
        skip_ws();
        if (pos_ != text_.size()) {
            throw error("Unexpected trailing characters");
        }
        return v;
    }

private:
    JsonValue parse_value() {
        if (pos_ >= text_.size()) {
            throw error("Unexpected end of JSON");
        }
        char c = text_[pos_];
        if (c == '{') {
            return parse_object();
        }
        if (c == '[') {
            return parse_array();
        }
        if (c == '"') {
            return JsonValue(parse_string());
        }
        if (c == 't') {
            consume_literal("true");
            return JsonValue(true);
        }
        if (c == 'f') {
            consume_literal("false");
            return JsonValue(false);
        }
        if (c == 'n') {
            consume_literal("null");
            return JsonValue(nullptr);
        }
        if (c == '-' || (c >= '0' && c <= '9')) {
            return JsonValue(parse_number());
        }
        throw error("Invalid JSON token");
    }

    JsonValue parse_object() {
        expect('{');
        skip_ws();
        JsonValue::Object obj;
        if (peek('}')) {
            expect('}');
            return JsonValue(std::move(obj));
        }
        while (true) {
            skip_ws();
            if (!peek('"')) {
                throw error("Object key must be string");
            }
            std::string key = parse_string();
            skip_ws();
            expect(':');
            skip_ws();
            JsonValue value = parse_value();
            obj.emplace(std::move(key), std::move(value));
            skip_ws();
            if (peek('}')) {
                expect('}');
                break;
            }
            expect(',');
        }
        return JsonValue(std::move(obj));
    }

    JsonValue parse_array() {
        expect('[');
        skip_ws();
        JsonValue::Array arr;
        if (peek(']')) {
            expect(']');
            return JsonValue(std::move(arr));
        }
        while (true) {
            skip_ws();
            arr.push_back(parse_value());
            skip_ws();
            if (peek(']')) {
                expect(']');
                break;
            }
            expect(',');
        }
        return JsonValue(std::move(arr));
    }

    std::string parse_string() {
        expect('"');
        std::string out;
        while (pos_ < text_.size()) {
            char c = text_[pos_++];
            if (c == '"') {
                return out;
            }
            if (c == '\\') {
                if (pos_ >= text_.size()) {
                    throw error("Invalid escape sequence");
                }
                char esc = text_[pos_++];
                switch (esc) {
                    case '"': out.push_back('"'); break;
                    case '\\': out.push_back('\\'); break;
                    case '/': out.push_back('/'); break;
                    case 'b': out.push_back('\b'); break;
                    case 'f': out.push_back('\f'); break;
                    case 'n': out.push_back('\n'); break;
                    case 'r': out.push_back('\r'); break;
                    case 't': out.push_back('\t'); break;
                    case 'u': {
                        if (pos_ + 4 > text_.size()) {
                            throw error("Invalid unicode escape");
                        }
                        std::string hex = text_.substr(pos_, 4);
                        pos_ += 4;
                        char16_t code = static_cast<char16_t>(std::stoi(hex, nullptr, 16));
                        if (code <= 0x7F) {
                            out.push_back(static_cast<char>(code));
                        } else {
                            throw error("Only ASCII unicode escapes are supported");
                        }
                        break;
                    }
                    default:
                        throw error("Unsupported escape sequence");
                }
            } else {
                out.push_back(c);
            }
        }
        throw error("Unterminated string");
    }

    double parse_number() {
        std::size_t start = pos_;
        if (text_[pos_] == '-') {
            ++pos_;
        }
        if (pos_ >= text_.size()) {
            throw error("Invalid number");
        }
        if (text_[pos_] == '0') {
            ++pos_;
        } else if (text_[pos_] >= '1' && text_[pos_] <= '9') {
            while (pos_ < text_.size() && text_[pos_] >= '0' && text_[pos_] <= '9') {
                ++pos_;
            }
        } else {
            throw error("Invalid number");
        }
        if (pos_ < text_.size() && text_[pos_] == '.') {
            ++pos_;
            if (pos_ >= text_.size() || text_[pos_] < '0' || text_[pos_] > '9') {
                throw error("Invalid number");
            }
            while (pos_ < text_.size() && text_[pos_] >= '0' && text_[pos_] <= '9') {
                ++pos_;
            }
        }
        if (pos_ < text_.size() && (text_[pos_] == 'e' || text_[pos_] == 'E')) {
            ++pos_;
            if (pos_ < text_.size() && (text_[pos_] == '+' || text_[pos_] == '-')) {
                ++pos_;
            }
            if (pos_ >= text_.size() || text_[pos_] < '0' || text_[pos_] > '9') {
                throw error("Invalid number");
            }
            while (pos_ < text_.size() && text_[pos_] >= '0' && text_[pos_] <= '9') {
                ++pos_;
            }
        }
        const std::string num = text_.substr(start, pos_ - start);
        try {
            return std::stod(num);
        } catch (...) {
            throw error("Invalid number literal");
        }
    }

    void skip_ws() {
        while (pos_ < text_.size()) {
            char c = text_[pos_];
            if (c == ' ' || c == '\n' || c == '\r' || c == '\t') {
                ++pos_;
            } else {
                break;
            }
        }
    }

    bool peek(char expected) const {
        return pos_ < text_.size() && text_[pos_] == expected;
    }

    void expect(char expected) {
        if (!peek(expected)) {
            throw error(std::string("Expected '") + expected + "'");
        }
        ++pos_;
    }

    void consume_literal(const char* literal) {
        const std::size_t n = std::strlen(literal);
        if (pos_ + n > text_.size() || text_.compare(pos_, n, literal) != 0) {
            throw error(std::string("Expected literal '") + literal + "'");
        }
        pos_ += n;
    }

    std::runtime_error error(const std::string& msg) const {
        std::ostringstream oss;
        oss << "JSON parse error at offset " << pos_ << ": " << msg;
        return std::runtime_error(oss.str());
    }

    std::string text_;
    std::size_t pos_;
};

struct PairIntHash {
    std::size_t operator()(const std::pair<int, int>& p) const noexcept {
        return (static_cast<std::size_t>(static_cast<uint32_t>(p.first)) << 32U) ^
               static_cast<std::size_t>(static_cast<uint32_t>(p.second));
    }
};

struct RawUnary {
    int name_sid = -1;
    std::vector<AtomTemplateLit> literals;
    std::vector<int> satisfies_self_sids;
    std::optional<int> sat_bound;
};

struct RawBinary {
    int name_sid = -1;
    std::vector<AtomTemplateLit> literals;
    std::vector<int> sat_left_sids;
    std::vector<int> sat_right_sids;
};

struct RawTypeSystem {
    std::vector<int> existential_constraint_sids;
    std::vector<RawUnary> unary_types;
    std::vector<RawBinary> binary_types;
    std::unordered_map<std::pair<int, int>, std::vector<int>, PairIntHash> pair_binary_choice_sids;
};

static std::string read_file_utf8(const std::filesystem::path& path) {
    std::ifstream in(path, std::ios::in | std::ios::binary);
    if (!in) {
        throw std::runtime_error("Failed to open file: " + path.string());
    }
    std::ostringstream oss;
    oss << in.rdbuf();
    return oss.str();
}

static std::vector<int> as_sid_vector(const JsonValue* raw, const std::string& field_name, InternTable& interner) {
    if (raw == nullptr || !raw->is_array()) {
        throw std::runtime_error(field_name + " must be a list of strings");
    }
    std::vector<int> out;
    for (std::size_t i = 0; i < raw->as_array().size(); ++i) {
        const JsonValue& item = raw->as_array()[i];
        if (!item.is_string() || item.as_string().empty()) {
            throw std::runtime_error(field_name + "[" + std::to_string(i) + "] must be a non-empty string");
        }
        out.push_back(interner.intern(item.as_string()));
    }
    return out;
}

static std::vector<AtomTemplateLit> as_lit_vector(const JsonValue* raw, const std::string& field_name, InternTable& interner) {
    if (raw == nullptr || !raw->is_object()) {
        throw std::runtime_error(field_name + " must be an object of atom -> bool");
    }
    std::vector<AtomTemplateLit> out;
    for (const auto& kv : raw->as_object()) {
        if (kv.first.empty()) {
            throw std::runtime_error(field_name + " keys must be non-empty strings");
        }
        if (!kv.second.is_bool()) {
            throw std::runtime_error(field_name + "[" + kv.first + "] must be bool");
        }
        out.emplace_back(interner.intern(kv.first), kv.second.as_bool());
    }
    std::sort(out.begin(), out.end());
    return out;
}

static int as_nonempty_sid_field(const JsonValue& obj, const std::string& field_name, const std::string& ctx, InternTable& interner) {
    if (!obj.is_object()) {
        throw std::runtime_error(ctx + " must be an object");
    }
    const JsonValue* raw = obj.get(field_name);
    if (raw == nullptr || !raw->is_string() || raw->as_string().empty()) {
        throw std::runtime_error(ctx + "." + field_name + " must be a non-empty string");
    }
    return interner.intern(raw->as_string());
}

static std::optional<int> as_optional_nonneg_int(const JsonValue* raw, const std::string& field_name) {
    if (raw == nullptr || raw->is_null()) {
        return std::nullopt;
    }
    if (!raw->is_number()) {
        throw std::runtime_error(field_name + " must be a non-negative integer or null");
    }
    double d = raw->as_number();
    if (d < 0.0 || std::floor(d) != d) {
        throw std::runtime_error(field_name + " must be a non-negative integer or null");
    }
    return static_cast<int>(d);
}

static std::vector<int> canonicalize_sid_set(std::vector<int> ids) {
    std::sort(ids.begin(), ids.end());
    ids.erase(std::unique(ids.begin(), ids.end()), ids.end());
    return ids;
}

static std::vector<RawUnary> parse_unary_types(const JsonValue* raw, InternTable& interner) {
    if (raw == nullptr || !raw->is_array()) {
        throw std::runtime_error("'unary_types' must be a list");
    }
    std::unordered_set<int> seen;
    std::vector<RawUnary> out;
    out.reserve(raw->as_array().size());

    for (const auto& entry : raw->as_array()) {
        RawUnary u;
        u.name_sid = as_nonempty_sid_field(entry, "name", "unary type", interner);
        if (!seen.insert(u.name_sid).second) {
            throw std::runtime_error("Duplicate unary type name");
        }
        u.literals = as_lit_vector(entry.get("literals"), "unary_types.literals", interner);
        u.sat_bound = as_optional_nonneg_int(entry.get("sat_bound"), "unary_types.sat_bound");

        const JsonValue* sat_raw = entry.get("satisfies_self");
        if (sat_raw != nullptr) {
            u.satisfies_self_sids = as_sid_vector(sat_raw, "unary_types.satisfies_self", interner);
        }
        out.push_back(std::move(u));
    }
    return out;
}

static std::vector<RawBinary> parse_binary_pool(const JsonValue::Array& raw, InternTable& interner) {
    std::unordered_set<int> seen;
    std::vector<RawBinary> out;
    out.reserve(raw.size());

    for (const auto& entry : raw) {
        RawBinary b;
        b.name_sid = as_nonempty_sid_field(entry, "name", "binary type", interner);
        if (!seen.insert(b.name_sid).second) {
            throw std::runtime_error("Duplicate binary type name");
        }
        b.literals = as_lit_vector(entry.get("literals"), "binary_types.literals", interner);

        if (const JsonValue* left = entry.get("satisfies_from_left"); left != nullptr) {
            b.sat_left_sids = as_sid_vector(left, "binary_types.satisfies_from_left", interner);
        }
        if (const JsonValue* right = entry.get("satisfies_from_right"); right != nullptr) {
            b.sat_right_sids = as_sid_vector(right, "binary_types.satisfies_from_right", interner);
        }
        out.push_back(std::move(b));
    }
    return out;
}

static std::unordered_map<int, std::vector<int>>
parse_candidate_sets(const JsonValue* raw, InternTable& interner) {
    if (raw == nullptr || !raw->is_object()) {
        throw std::runtime_error("'candidate_sets' must be an object");
    }

    std::unordered_map<int, std::vector<int>> out;
    for (const auto& kv : raw->as_object()) {
        if (kv.first.empty()) {
            throw std::runtime_error("candidate_sets keys must be non-empty strings");
        }
        int set_sid = interner.intern(kv.first);
        if (!kv.second.is_array()) {
            throw std::runtime_error("candidate_sets[" + kv.first + "] must be a list");
        }
        std::vector<int> candidates = as_sid_vector(&kv.second, "candidate_sets[" + kv.first + "]", interner);
        candidates = canonicalize_sid_set(std::move(candidates));
        if (!out.emplace(set_sid, std::move(candidates)).second) {
            throw std::runtime_error("Duplicate candidate set name in candidate_sets");
        }
    }
    return out;
}

static std::unordered_map<std::pair<int, int>, std::vector<int>, PairIntHash>
parse_pair_binary_rules(
    const JsonValue* raw,
    const std::unordered_map<int, std::vector<int>>& candidate_sets,
    const std::vector<RawUnary>& unary_types,
    InternTable& interner
) {
    if (raw == nullptr || !raw->is_array()) {
        throw std::runtime_error("'pair_binary_rules' must be a list");
    }

    std::vector<int> unary_sids;
    unary_sids.reserve(unary_types.size());
    std::unordered_set<int> unary_sid_set;
    for (const auto& u : unary_types) {
        unary_sids.push_back(u.name_sid);
        unary_sid_set.insert(u.name_sid);
    }

    auto resolve_set_candidates = [&](const JsonValue& rule, const std::string& field_name) -> const std::vector<int>& {
        int set_sid = as_nonempty_sid_field(rule, field_name, "pair_binary_rules", interner);
        auto it = candidate_sets.find(set_sid);
        if (it == candidate_sets.end()) {
            throw std::runtime_error("pair_binary_rules references unknown candidate set: " + interner.str(set_sid));
        }
        return it->second;
    };

    auto parse_optional_bool = [](const JsonValue* raw_bool, const std::string& field_name) -> bool {
        if (raw_bool == nullptr) {
            return false;
        }
        if (!raw_bool->is_bool()) {
            throw std::runtime_error(field_name + " must be bool");
        }
        return raw_bool->as_bool();
    };

    std::unordered_map<std::pair<int, int>, std::vector<int>, PairIntHash> out;
    auto assign_pairs = [&](const std::vector<int>& left_types, const std::vector<int>& right_types, bool same_type, const std::vector<int>& candidates) {
        for (int left_sid : left_types) {
            if (!unary_sid_set.count(left_sid)) {
                throw std::runtime_error("pair_binary_rules references unknown unary type: " + interner.str(left_sid));
            }
            for (int right_sid : right_types) {
                if (!unary_sid_set.count(right_sid)) {
                    throw std::runtime_error("pair_binary_rules references unknown unary type: " + interner.str(right_sid));
                }
                if (same_type && left_sid != right_sid) {
                    continue;
                }
                auto key = std::make_pair(left_sid, right_sid);
                out[key] = candidates;
            }
        }
    };

    for (std::size_t rule_idx = 0; rule_idx < raw->as_array().size(); ++rule_idx) {
        const JsonValue& rule = raw->as_array()[rule_idx];
        if (!rule.is_object()) {
            throw std::runtime_error("pair_binary_rules entry must be object");
        }

        const JsonValue* default_set_raw = rule.get("default_set");
        if (default_set_raw != nullptr) {
            const std::vector<int>& candidates = resolve_set_candidates(rule, "default_set");
            assign_pairs(unary_sids, unary_sids, false, candidates);
            continue;
        }

        const std::vector<int>& candidates = resolve_set_candidates(rule, "set");
        bool same_type = parse_optional_bool(rule.get("same_type"), "pair_binary_rules.same_type");

        std::vector<int> left_types;
        std::vector<int> right_types;

        if (rule.get("left_types") != nullptr || rule.get("right_types") != nullptr) {
            left_types = as_sid_vector(rule.get("left_types"), "pair_binary_rules.left_types", interner);
            right_types = as_sid_vector(rule.get("right_types"), "pair_binary_rules.right_types", interner);
        } else if (rule.get("left_type") != nullptr || rule.get("right_type") != nullptr) {
            left_types = {as_nonempty_sid_field(rule, "left_type", "pair_binary_rules", interner)};
            right_types = {as_nonempty_sid_field(rule, "right_type", "pair_binary_rules", interner)};
        } else {
            left_types = unary_sids;
            right_types = unary_sids;
        }

        assign_pairs(left_types, right_types, same_type, candidates);
    }

    for (int left_sid : unary_sids) {
        for (int right_sid : unary_sids) {
            if (!out.count({left_sid, right_sid})) {
                throw std::runtime_error(
                    "Missing binary choice list for unary pair (" + interner.str(left_sid) + ", " + interner.str(right_sid) + ")"
                );
            }
        }
    }

    return out;
}

static RawTypeSystem parse_raw_typesystem(const JsonValue& payload, InternTable& interner) {
    if (!payload.is_object()) {
        throw std::runtime_error("JSON root must be an object");
    }

    RawTypeSystem out;

    if (const JsonValue* existential_raw = payload.get("existential_constraints"); existential_raw != nullptr) {
        out.existential_constraint_sids = as_sid_vector(existential_raw, "existential_constraints", interner);
    }

    out.unary_types = parse_unary_types(payload.get("unary_types"), interner);

    const JsonValue* binary_types_raw = payload.get("binary_types");
    if (binary_types_raw == nullptr || !binary_types_raw->is_array()) {
        throw std::runtime_error("'binary_types' must be a list");
    }

    const auto& binary_entries = binary_types_raw->as_array();
    out.binary_types = parse_binary_pool(binary_entries, interner);
    std::unordered_map<int, std::vector<int>> candidate_sets = parse_candidate_sets(payload.get("candidate_sets"), interner);
    out.pair_binary_choice_sids = parse_pair_binary_rules(payload.get("pair_binary_rules"), candidate_sets, out.unary_types, interner);

    return out;
}

static TypeSystemId compile_raw_to_id(const RawTypeSystem& raw) {
    TypeSystemId spec;

    spec.existential_constraint_sids = raw.existential_constraint_sids;

    std::unordered_map<int, int> constraint_sid_to_idx;
    for (std::size_t i = 0; i < spec.existential_constraint_sids.size(); ++i) {
        int sid = spec.existential_constraint_sids[i];
        if (!constraint_sid_to_idx.emplace(sid, static_cast<int>(i)).second) {
            throw std::runtime_error("existential_constraints must be unique");
        }
    }

    spec.unary_types.reserve(raw.unary_types.size());
    for (const auto& u : raw.unary_types) {
        int idx = static_cast<int>(spec.unary_types.size());
        if (!spec.unary_sid_to_idx.emplace(u.name_sid, idx).second) {
            throw std::runtime_error("Duplicate unary type name");
        }

        UnaryTypeId out_u;
        out_u.name_sid = u.name_sid;
        out_u.literals = u.literals;
        out_u.sat_bound = u.sat_bound;

        std::unordered_set<int> sat_seen;
        for (int c_sid : u.satisfies_self_sids) {
            auto it = constraint_sid_to_idx.find(c_sid);
            if (it == constraint_sid_to_idx.end()) {
                throw std::runtime_error("Unary type uses unknown constraint sid");
            }
            if (sat_seen.insert(it->second).second) {
                out_u.satisfies_self.push_back(it->second);
            }
        }

        spec.unary_types.push_back(std::move(out_u));
        spec.unary_name_sids.push_back(u.name_sid);
    }

    spec.binary_types.reserve(raw.binary_types.size());
    for (const auto& b : raw.binary_types) {
        int idx = static_cast<int>(spec.binary_types.size());
        if (!spec.binary_sid_to_idx.emplace(b.name_sid, idx).second) {
            throw std::runtime_error("Duplicate binary type name");
        }

        BinaryTypeId out_b;
        out_b.name_sid = b.name_sid;
        out_b.literals = b.literals;

        std::unordered_set<int> left_seen;
        for (int c_sid : b.sat_left_sids) {
            auto it = constraint_sid_to_idx.find(c_sid);
            if (it == constraint_sid_to_idx.end()) {
                throw std::runtime_error("Binary type uses unknown left constraint sid");
            }
            if (left_seen.insert(it->second).second) {
                out_b.satisfies_from_left.push_back(it->second);
            }
        }

        std::unordered_set<int> right_seen;
        for (int c_sid : b.sat_right_sids) {
            auto it = constraint_sid_to_idx.find(c_sid);
            if (it == constraint_sid_to_idx.end()) {
                throw std::runtime_error("Binary type uses unknown right constraint sid");
            }
            if (right_seen.insert(it->second).second) {
                out_b.satisfies_from_right.push_back(it->second);
            }
        }

        spec.binary_types.push_back(std::move(out_b));
        spec.binary_name_sids.push_back(b.name_sid);
    }

    int u = spec.unary_count();
    spec.pair_binary_choices.assign(static_cast<std::size_t>(u * u), {});

    for (const auto& kv : raw.pair_binary_choice_sids) {
        int left_sid = kv.first.first;
        int right_sid = kv.first.second;

        auto left_it = spec.unary_sid_to_idx.find(left_sid);
        auto right_it = spec.unary_sid_to_idx.find(right_sid);
        if (left_it == spec.unary_sid_to_idx.end() || right_it == spec.unary_sid_to_idx.end()) {
            throw std::runtime_error("pair_binary_choices references unknown unary type");
        }

        std::vector<int> cand_indices;
        cand_indices.reserve(kv.second.size());
        for (int b_sid : kv.second) {
            auto b_it = spec.binary_sid_to_idx.find(b_sid);
            if (b_it == spec.binary_sid_to_idx.end()) {
                throw std::runtime_error("pair_binary_choices references unknown binary type");
            }
            cand_indices.push_back(b_it->second);
        }
        cand_indices = canonicalize_sid_set(std::move(cand_indices));

        int slot = left_it->second * u + right_it->second;
        auto& existing = spec.pair_binary_choices[static_cast<std::size_t>(slot)];
        if (!existing.empty() && existing != cand_indices) {
            throw std::runtime_error("Conflicting candidates for unary pair");
        }
        existing = std::move(cand_indices);
    }

    for (int left = 0; left < u; ++left) {
        for (int right = 0; right < u; ++right) {
            const auto& cand = spec.pair_choice_names(left, right);
            if (cand.empty() && !raw.pair_binary_choice_sids.count({spec.unary_name_sids[left], spec.unary_name_sids[right]})) {
                throw std::runtime_error("Missing binary choice list for unary pair");
            }
        }
    }

    spec.validate();
    return spec;
}

}  // namespace

TypeSystemId load_typesystem_id_from_json(const std::filesystem::path& path, InternTable& interner) {
    std::string text = read_file_utf8(path);
    JsonParser parser(std::move(text));
    JsonValue root = parser.parse();
    RawTypeSystem raw = parse_raw_typesystem(root, interner);
    return compile_raw_to_id(raw);
}

}  // namespace fo2
