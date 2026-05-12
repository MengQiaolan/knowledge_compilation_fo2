# OBDD Compilers

This repository contains two OBDD compilers:

1. `obdd_compile_cpp`: native C++ compiler from JSON spec and domain size.
2. `cudd_compile_cpp`: C++ CUDD baseline compiler from grounded CNF.

Both tools print:

```text
OBDD nodes: <reachable non-terminal decision nodes>
Atom variables: <atom variable count>
Model count: <exact model count>
Time: <seconds>s
```

If `-o <dot_file>` is provided, they also save a DOT file and print:

```text
DOT saved: <dot_file>
```

## 1. Native C++ OBDD Compiler

Build:

```bash
clang++ -std=c++20 \
  code/obdd_run.cpp code/src/obdd_core.cpp code/src/spec_loader.cpp \
  -Icode/include -Icode/src \
  -lminisat \
  -O2 -o obdd_compile_cpp
```

If MiniSat is installed in a custom prefix, add its include and library paths:

```bash
clang++ -std=c++20 \
  code/obdd_run.cpp code/src/obdd_core.cpp code/src/spec_loader.cpp \
  -Icode/include -Icode/src \
  -I$MINISAT_DIR/include -L$MINISAT_DIR/lib \
  -lminisat \
  -O2 -o obdd_compile_cpp
```

Run:

```bash
./obdd_compile_cpp --json-spec examples/non_isolated_graph.json -n 3
```

With DOT output:

```bash
./obdd_compile_cpp --json-spec examples/non_isolated_graph.json -n 3 -o /tmp/noniso_obdd.dot
```

Print the final atom variable order:

```bash
./obdd_compile_cpp --json-spec examples/non_isolated_graph.json -n 3 --order
```

CLI:

```text
./obdd_compile_cpp --json-spec <path> -n <domain_size> [-o <dot_file>] [--order]
```

## 2. C++ CUDD Baseline Compiler

This compiler takes a grounded CNF file. The first two comment lines of the CNF map DIMACS variable ids to atom names; they are not treated as a fixed variable order.

Build with an installed CUDD:

```bash
clang++ -std=c++20 \
  code/cudd_run.cpp code/src/cudd_core.cpp \
  -Icode/include \
  -I$CUDD_DIR/include -L$CUDD_DIR/lib \
  -lcudd \
  -O2 -o cudd_compile_cpp
```

If using a static CUDD library:

```bash
clang++ -std=c++20 \
  code/cudd_run.cpp code/src/cudd_core.cpp \
  -Icode/include \
  -I$CUDD_DIR/include \
  $CUDD_DIR/lib/libcudd.a \
  -O2 -o cudd_compile_cpp
```

If CUDD is dynamically linked, make sure the runtime library path is visible, for example:

```bash
export LD_LIBRARY_PATH=$CUDD_DIR/lib:$LD_LIBRARY_PATH
```

Run:

```bash
./cudd_compile_cpp --cnf cnf/cnf-u4-b2/6.cnf
```

With DOT output:

```bash
./cudd_compile_cpp --cnf cnf/cnf-u4-b2/6.cnf -o /tmp/u4_b2_cudd.dot
```

Print the final atom variable order:

```bash
./cudd_compile_cpp --cnf cnf/cnf-u4-b2/6.cnf --order
```

Profile CUDD stage timings:

```bash
./cudd_compile_cpp --cnf cnf/cnf-u4-b2/6.cnf --profile
```

Choose CUDD reordering strategy:

```bash
./cudd_compile_cpp --cnf cnf/cnf-u4-b2/6.cnf --reorder sift
./cudd_compile_cpp --cnf cnf/cnf-u4-b2/6.cnf --reorder window3
./cudd_compile_cpp --cnf cnf/cnf-u4-b2/6.cnf --reorder group-sift
```

Default CUDD setting:

```text
--reorder sift --reorder-mode auto-final
```

Available reordering strategies:

```text
sift
group-sift
window2
window3
window4
```

Available reordering modes:

```text
auto-final   # dynamic reordering during build, plus one final ReduceHeap
final-only   # no build-time dynamic reordering, only final ReduceHeap
```

CLI:

```text
./cudd_compile_cpp --cnf <path> [-o <dot_file>] [--order] [--profile] \
  [--reorder <sift|group-sift|window2|window3|window4>] \
  [--reorder-mode <auto-final|final-only>]
```
