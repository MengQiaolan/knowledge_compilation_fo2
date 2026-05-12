#include "compiler_branches.hpp"

#include "compiler_common.hpp"
#include "compiler_existential.hpp"
#include "compiler_independent.hpp"

static bool contains_int_branch(const std::vector<int>& xs, int value) {
    return std::find(xs.begin(), xs.end(), value) != xs.end();
}

static std::vector<int> canonicalize_ints_branch(std::vector<int> values) {
    std::sort(values.begin(), values.end());
    values.erase(std::unique(values.begin(), values.end()), values.end());
    return values;
}

static std::string trim_ascii_branch(std::string s) {
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

static std::string join_strings_branch(const std::vector<std::string>& items, const std::string& sep) {
    std::ostringstream oss;
    for (std::size_t i = 0; i < items.size(); ++i) {
        if (i != 0) {
            oss << sep;
        }
        oss << items[i];
    }
    return oss.str();
}

static std::string json_escape_branch(const std::string& s) {
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

static std::string format_duration_branch(double seconds) {
    std::ostringstream oss;
    oss << std::fixed << std::setprecision(6) << seconds << "s ("
        << std::setprecision(2) << (seconds * 1000.0) << " ms)";
    return oss.str();
}

static fs::path derive_aux_spec_path_branch(const fs::path& json_spec_path) {
    if (json_spec_path.has_extension()) {
        return json_spec_path.parent_path() /
            (json_spec_path.stem().string() + "_aux" + json_spec_path.extension().string());
    }
    return json_spec_path.parent_path() / (json_spec_path.filename().string() + "_aux.json");
}

#define contains_int contains_int_branch
#define canonicalize_ints canonicalize_ints_branch
#define trim_ascii trim_ascii_branch
#define join_strings join_strings_branch
#define json_escape json_escape_branch
#include "compiler_independence.hpp"
#undef json_escape
#undef join_strings
#undef trim_ascii
#undef canonicalize_ints
#undef contains_int

int run_existential_compile_branch(
    int domain_size,
    int post_process_mode,
    bool mem_debug,
    bool analyze_independence,
    bool analyze_independence_only,
    const std::string& component_aux_out_dir,
    const std::string& json_spec_path,
    const std::string& spec_name,
    const fo2::TypeSystemId& spec,
    fo2::InternTable& interner,
    const std::chrono::steady_clock::time_point& t0,
    const std::chrono::steady_clock::time_point& t1,
    std::string& aux_spec_name,
    int& root,
    CompiledCircuit& circuit
) {
    fs::path aux_path = derive_aux_spec_path_branch(json_spec_path);
    fo2::TypeSystemId aux_spec = fo2::load_typesystem_id_from_json(aux_path, interner);
    aux_spec_name = "json:" + fs::absolute(aux_path).string();

    std::optional<fs::path> dump_dir = std::nullopt;
    if (analyze_independence && !component_aux_out_dir.empty()) {
        dump_dir = fs::path(component_aux_out_dir);
    }
    IndependenceAnalysisReport report = analyze_independence_and_build_components(
        spec,
        aux_spec,
        interner,
        dump_dir
    );

    if (analyze_independence) {
        std::cout << "Independence analysis:\n";
        std::vector<std::string> all_pred_names;
        for (int sid : report.all_predicate_sids) {
            all_pred_names.push_back(interner.str(sid));
        }
        std::cout << "  binary predicates: [" << join_strings_branch(all_pred_names, ", ") << "]\n";
        std::cout << "  split detected: " << (report.has_split ? "yes" : "no") << "\n";
        std::cout << "  analysis valid: " << (report.valid ? "yes" : "no") << "\n";
        std::cout << "  reason: " << report.reason << "\n";
        for (const auto& comp : report.components) {
            std::vector<std::string> pred_names;
            pred_names.reserve(comp.predicate_sids.size());
            for (int sid : comp.predicate_sids) {
                pred_names.push_back(interner.str(sid));
            }

            std::vector<std::string> c_names;
            c_names.reserve(comp.constraint_indices.size());
            for (int cidx : comp.constraint_indices) {
                c_names.push_back(interner.str(spec.existential_constraint_sids[static_cast<std::size_t>(cidx)]));
            }

            std::cout << "  component[" << comp.component_id << "]:\n";
            std::cout << "    predicates: [" << join_strings_branch(pred_names, ", ") << "]\n";
            std::cout << "    constraints: [" << join_strings_branch(c_names, ", ") << "]\n";
            std::cout << "    projected main: "
                      << (comp.main_ok ? "PASS" : "FAIL")
                      << "  (unary=" << comp.main_spec.unary_count()
                      << ", binary=" << comp.main_spec.binary_count()
                      << ", m=" << comp.main_spec.existential_count() << ")\n";
            std::cout << "    projected aux:  "
                      << (comp.aux_ok ? "PASS" : "FAIL")
                      << "  (unary=" << comp.aux_spec.unary_count()
                      << ", binary=" << comp.aux_spec.binary_count()
                      << ", m=" << comp.aux_spec.existential_count() << ")\n";
            if (!comp.main_ok) {
                std::cout << "    main error: " << comp.main_error << "\n";
            }
            if (!comp.aux_ok) {
                std::cout << "    aux error: " << comp.aux_error << "\n";
            }
            if (comp.dumped_aux_path.has_value()) {
                std::cout << "    dumped: " << fs::absolute(*comp.dumped_aux_path).string() << "\n";
            }
        }
    }

    if (analyze_independence_only) {
        return report.valid ? 0 : 1;
    }

    const bool use_independent = report.valid && report.has_split;
    if (use_independent) {
        std::vector<fo2::TypeSystemId> component_specs;
        std::vector<fo2::TypeSystemId> component_aux_specs;
        component_specs.reserve(report.components.size());
        component_aux_specs.reserve(report.components.size());
        for (const auto& comp : report.components) {
            component_specs.push_back(comp.main_spec);
            component_aux_specs.push_back(comp.aux_spec);
        }

        CompilerIndependent compiler(domain_size, spec, component_specs, component_aux_specs, interner);
        root = compiler.compile_raw();
        const auto t2 = std::chrono::steady_clock::now();
        circuit = compiler.post_process(root, post_process_mode);
        const auto t3 = std::chrono::steady_clock::now();

        const double pre = std::chrono::duration<double>(t1 - t0).count();
        const double compiling = std::chrono::duration<double>(t2 - t1).count();
        const double post = std::chrono::duration<double>(t3 - t2).count();

        const auto stats = circuit.stats();
        std::cout << "Spec: " << spec_name << "\n";
        std::cout << "Aux spec: " << aux_spec_name << "\n";
        std::cout << "Domain size n: " << domain_size << "\n";
        std::cout << "Timing:\n";
        std::cout << "  pre processing: " << format_duration_branch(pre) << "\n";
        std::cout << "  compiling: " << format_duration_branch(compiling) << "\n";
        std::cout << "  post processing: " << format_duration_branch(post) << "\n";
        std::cout << "Circuit stats:\n";
        std::cout << "  nodes: " << stats.nodes << "  (and: " << stats.and_nodes
                  << ", or: " << stats.or_nodes << ", leaves: " << stats.leaf_nodes << ")\n";
        std::cout << "  edges: " << stats.edges << "\n";
        std::cout << "Independence compile mode: enabled (" << report.components.size() << " components)\n";
        if (mem_debug) {
            std::cout << "MEMDEBUG existential: component mode (detailed counters not implemented in this mode)\n";
        }
    } else {
        Compiler compiler(domain_size, spec, aux_spec, interner);
        root = compiler.compile_raw();
        std::optional<Compiler::DebugStats> debug_before_post;
        if (mem_debug) {
            debug_before_post = compiler.debug_stats();
        }
        const auto t2 = std::chrono::steady_clock::now();
        circuit = compiler.post_process(root, post_process_mode);
        const auto t3 = std::chrono::steady_clock::now();

        const double pre = std::chrono::duration<double>(t1 - t0).count();
        const double compiling = std::chrono::duration<double>(t2 - t1).count();
        const double post = std::chrono::duration<double>(t3 - t2).count();

        const auto stats = circuit.stats();
        std::cout << "Spec: " << spec_name << "\n";
        std::cout << "Aux spec: " << aux_spec_name << "\n";
        std::cout << "Domain size n: " << domain_size << "\n";
        std::cout << "Timing:\n";
        std::cout << "  pre processing: " << format_duration_branch(pre) << "\n";
        std::cout << "  compiling: " << format_duration_branch(compiling) << "\n";
        std::cout << "  post processing: " << format_duration_branch(post) << "\n";
        std::cout << "Circuit stats:\n";
        std::cout << "  nodes: " << stats.nodes << "  (and: " << stats.and_nodes
                  << ", or: " << stats.or_nodes << ", leaves: " << stats.leaf_nodes << ")\n";
        std::cout << "  edges: " << stats.edges << "\n";
        std::cout << "Independence compile mode: disabled\n";

        if (mem_debug) {
            const auto& ds = debug_before_post.value();
            std::cout << "MEMDEBUG existential:\n";
            std::cout << "  sat.solver_vars: " << ds.sat.solver_vars << "\n";
            std::cout << "  sat.cnf_clauses: " << ds.sat.cnf_clauses << "\n";
            std::cout << "  sat.cnf_lits: " << ds.sat.cnf_lits << "\n";
            std::cout << "  sat.u_var_size: " << ds.sat.u_var_size << "\n";
            std::cout << "  sat.b_var_size: " << ds.sat.b_var_size << "\n";
            std::cout << "  sat.pair_groups: " << ds.sat.pair_groups << "\n";
            std::cout << "  sat.pair_group_lits_total: " << ds.sat.pair_group_lits_total << "\n";
            std::cout << "  sat.config_cache_size: " << ds.sat.config_cache_size << "\n";
            std::cout << "  sat.config_cache_key_refs: " << ds.sat.config_cache_key_refs << "\n";
            std::cout << "  aux.raw_result_cache_size: " << ds.aux_sat.raw_result_cache_size << "\n";
            std::cout << "  aux.reduced_result_cache_size: " << ds.aux_sat.reduced_result_cache_size << "\n";
            std::cout << "  aux.raw_result_key_refs: " << ds.aux_sat.raw_result_key_refs << "\n";
            std::cout << "  aux.reduced_result_key_refs: " << ds.aux_sat.reduced_result_key_refs << "\n";
            std::cout << "  circuit.node_count: " << ds.circuit.node_count << "\n";
            std::cout << "  circuit.node_child_refs: " << ds.circuit.node_child_refs << "\n";
            std::cout << "  circuit.and_cache_size: " << ds.circuit.and_cache_size << "\n";
            std::cout << "  circuit.and_cache_key_refs: " << ds.circuit.and_cache_key_refs << "\n";
            std::cout << "  circuit.or_cache_size: " << ds.circuit.or_cache_size << "\n";
            std::cout << "  circuit.or_cache_key_refs: " << ds.circuit.or_cache_key_refs << "\n";
            std::cout << "  subcircuit_cache_size: " << ds.subcircuit_cache_size << "\n";
            std::cout << "  pair_suffix_registry_size: " << ds.pair_suffix_registry_size << "\n";
            std::cout << "  pair_suffix_registry_total_refs: " << ds.pair_suffix_registry_total_refs << "\n";
            std::cout << "  sat_state_registry_size: " << ds.sat_state_registry_size << "\n";
            std::cout << "  sat_state_registry_total_refs: " << ds.sat_state_registry_total_refs << "\n";
            std::cout << "  subcircuit_key_pair_suffix_total: " << ds.subcircuit_key_pair_suffix_total << "\n";
            std::cout << "  subcircuit_key_sat_masks_total: " << ds.subcircuit_key_sat_masks_total << "\n";
            std::cout << "  pair_signature_suffix_cache_size: " << ds.pair_signature_suffix_cache_size << "\n";
            std::cout << "  pair_signature_suffix_key_refs: " << ds.pair_signature_suffix_key_refs << "\n";
            std::cout << "  pair_signature_suffix_value_refs: " << ds.pair_signature_suffix_value_refs << "\n";
            std::cout << "  grouped_btypes_cache_size: " << ds.grouped_btypes_cache_size << "\n";
            std::cout << "  grouped_btypes_total_groups: " << ds.grouped_btypes_total_groups << "\n";
            std::cout << "  grouped_btypes_total_name_refs: " << ds.grouped_btypes_total_name_refs << "\n";
            std::cout << "  binary_group_terms_cache_size: " << ds.binary_group_terms_cache_size << "\n";
            std::cout << "  binary_group_terms_total_terms: " << ds.binary_group_terms_total_terms << "\n";
            std::cout << "  binary_group_terms_total_lits: " << ds.binary_group_terms_total_lits << "\n";
            std::cout << "  binary_group_clause_cache_size: " << ds.binary_group_clause_cache_size << "\n";
            std::cout << "  binary_term_clause_cache_size: " << ds.binary_term_clause_cache_size << "\n";
            std::cout << "  unary_clause_cache_size: " << ds.unary_clause_cache_size << "\n";
            std::cout << "  binary_clause_cache_size: " << ds.binary_clause_cache_size << "\n";
        }
    }

    return 0;
}
