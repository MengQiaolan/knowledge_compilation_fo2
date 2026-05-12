struct CliArgs {
    int domain_size = 0;
    std::string json_spec;
    bool show = false;
    std::string out = "dnnf_circuit";
    int post_process = kPostProcessNone;
    bool model_count = false;
    bool verify_correctness = false;
    int max_sat_models = 0;
    int max_dnnf_models = 0;
    bool analyze_independence = false;
    bool analyze_independence_only = false;
    std::string component_aux_out_dir;
};

[[noreturn]] static void cli_error(const std::string& msg) {
    throw std::runtime_error(msg);
}

static CliArgs parse_cli_args(int argc, char** argv) {
    CliArgs args;

    for (int i = 1; i < argc; ++i) {
        std::string cur = argv[i];
        if (cur == "-n" || cur == "--domain-size") {
            if (i + 1 >= argc) {
                cli_error("Missing value for " + cur);
            }
            args.domain_size = std::stoi(argv[++i]);
            continue;
        }
        if (cur == "--json-spec") {
            if (i + 1 >= argc) {
                cli_error("Missing value for --json-spec");
            }
            args.json_spec = argv[++i];
            continue;
        }
        if (cur == "-s" || cur == "--show") {
            args.show = true;
            continue;
        }
        if (cur == "-o" || cur == "--out") {
            if (i + 1 >= argc) {
                cli_error("Missing value for " + cur);
            }
            args.out = argv[++i];
            continue;
        }
        if (cur == "--post-process") {
            if (i + 1 >= argc) {
                cli_error("Missing value for --post-process");
            }
            args.post_process = std::stoi(argv[++i]);
            continue;
        }
        if (cur == "--verify-correctness") {
            args.verify_correctness = true;
            continue;
        }
        if (cur == "--model-count") {
            args.model_count = true;
            continue;
        }
        if (cur == "--max-sat-models") {
            if (i + 1 >= argc) {
                cli_error("Missing value for --max-sat-models");
            }
            args.max_sat_models = std::stoi(argv[++i]);
            continue;
        }
        if (cur == "--max-dnnf-models") {
            if (i + 1 >= argc) {
                cli_error("Missing value for --max-dnnf-models");
            }
            args.max_dnnf_models = std::stoi(argv[++i]);
            continue;
        }
        if (cur == "--analyze-independence") {
            args.analyze_independence = true;
            continue;
        }
        if (cur == "--analyze-independence-only") {
            args.analyze_independence = true;
            args.analyze_independence_only = true;
            continue;
        }
        if (cur == "--component-aux-out-dir") {
            if (i + 1 >= argc) {
                cli_error("Missing value for --component-aux-out-dir");
            }
            args.component_aux_out_dir = argv[++i];
            continue;
        }
        if (cur == "-h" || cur == "--help") {
            std::cout
                << "Usage: dnnf_cpp -n <domain_size> --json-spec <path> [options]\n"
                << "Options:\n"
                << "  -n, --domain-size <int>       Domain size n (required, >0)\n"
                << "  --json-spec <path>            Path to JSON spec (required)\n"
                << "  -s, --show                    Save DOT graph\n"
                << "  -o, --out <prefix>            Output prefix (default: dnnf_circuit)\n"
                << "  --post-process <-1|0|1>       Post-process mode: -1(full), 0(disabled), 1(single-pass), default=0\n"
                << "  --model-count                 Print exact model count of compiled circuit\n"
                << "  --verify-correctness          Run bidirectional model-enumeration verifier\n"
                << "  --max-sat-models <int>        SAT-side unique atom model limit (0=no limit)\n"
                << "  --max-dnnf-models <int>       d-DNNF-side unique atom model limit (0=no limit)\n"
                << "  --analyze-independence        Detect predicate-independence and build component-aux projections\n"
                << "  --analyze-independence-only   Run independence analysis only, then exit\n"
                << "  --component-aux-out-dir <p>   Dump projected component-aux json files to directory\n";
            std::exit(0);
        }
        cli_error("Unknown argument: " + cur);
    }

    if (args.domain_size <= 0) {
        cli_error("--domain-size must be > 0");
    }
    if (args.json_spec.empty()) {
        cli_error("--json-spec is required");
    }
    if (args.post_process != kPostProcessFull &&
        args.post_process != kPostProcessNone &&
        args.post_process != kPostProcessSinglePass) {
        cli_error("--post-process must be one of -1, 0, 1");
    }
    if (args.max_sat_models < 0) {
        cli_error("--max-sat-models must be >= 0");
    }
    if (args.max_dnnf_models < 0) {
        cli_error("--max-dnnf-models must be >= 0");
    }
    if (args.analyze_independence_only && !args.analyze_independence) {
        cli_error("--analyze-independence-only requires --analyze-independence");
    }

    return args;
}

int run_dnnf_main(int argc, char** argv) {
    try {
        const auto t0 = std::chrono::steady_clock::now();
        const CliArgs args = parse_cli_args(argc, argv);
        const bool mem_debug = (std::getenv("DNNF_MEM_DEBUG") != nullptr);
        fo2::InternTable interner;

        fo2::TypeSystemId spec = fo2::load_typesystem_id_from_json(args.json_spec, interner);
        std::string spec_name = "json:" + fs::absolute(args.json_spec).string();
        std::string aux_spec_name = "N/A (universal-only mode)";

        const auto t1 = std::chrono::steady_clock::now();

        int root = kNoneNode;
        CompiledCircuit circuit;

        int branch_rc = 0;
        if (spec.existential_count() == 0) {
            branch_rc = run_universal_compile_branch(
                args.domain_size,
                args.post_process,
                mem_debug,
                args.analyze_independence,
                args.analyze_independence_only,
                spec_name,
                aux_spec_name,
                spec,
                interner,
                t0,
                t1,
                root,
                circuit
            );
        } else {
            branch_rc = run_existential_compile_branch(
                args.domain_size,
                args.post_process,
                mem_debug,
                args.analyze_independence,
                args.analyze_independence_only,
                args.component_aux_out_dir,
                args.json_spec,
                spec_name,
                spec,
                interner,
                t0,
                t1,
                aux_spec_name,
                root,
                circuit
            );
        }
        if (args.analyze_independence_only || branch_rc != 0) {
            return branch_rc;
        }

        if (args.model_count) {
            BigInt mc = model_count_circuit(spec, circuit, args.domain_size, interner);
            std::cout << "Model count: " << mc << "\n";
        }

        if (args.verify_correctness) {
            VerificationResult vr = verify_circuit_by_enumeration(
                spec,
                circuit,
                args.domain_size,
                interner,
                args.max_sat_models,
                args.max_dnnf_models
            );
            std::cout << "Verification stats:\n";
            std::cout << "  SAT models (raw): " << vr.stats.sat_raw_models << "\n";
            std::cout << "  SAT models (unique atom-projection): " << vr.stats.sat_unique_atom_models << "\n";
            std::cout << "  d-DNNF models (raw): " << vr.stats.dnnf_raw_models << "\n";
            std::cout << "  d-DNNF models (unique atom-projection): " << vr.stats.dnnf_unique_atom_models << "\n";
            std::cout << "Verification result: " << (vr.ok ? "PASS" : "FAIL") << "\n";
            std::cout << vr.message << "\n";
            if (!vr.ok) {
                return 1;
            }
        }

        if (args.show) {
            fs::path out_prefix = fs::absolute(args.out);
            fs::path dot_path = out_prefix.string() + ".dot";
            save_dot(circuit, dot_path, interner);
            std::cout << "DOT saved: " << dot_path.string() << "\n";
        }

        return 0;
    } catch (const std::exception& ex) {
        std::cerr << ex.what() << "\n";
        return 2;
    }
}
