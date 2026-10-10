#!/usr/bin/env bash
# run_all.sh -- re-run every check of "Even lattice paths and the Catalan numbers".
#
#   C       verification/c/star_lemma.c           the cell identity, the star lemma and the formula for
#                                                 canonical pairs for every word length k <= 13
#   C++     verification/cpp/skeletons.cpp        skeleton systems admissible and extremal (m <= 10);
#                                                 exhaustive search: the extremal systems of length m <= 5
#                                                 are the skeleton systems; the families F_M (n <= 6)
#   Shell   verification/shell/check_paths.sh     bash integer arithmetic only: star lemma k <= 6,
#                                                 Shankar's conjecture n <= 3 by clique counting
#   Python  verification/python/verify_sat.py     SAT: extremal systems for m <= 6, Shankar's conjecture
#                                                 for n <= 5, groupings for k <= 7; star lemma k <= 9
#                                                 (needs python-sat; QUICK=1 stops at m <= 5, n <= 4)
#   Julia   verification/julia/verify_systems.jl  skeleton/path bijection, the induction step on
#                                                 skeleton systems, groupings by search, F_M for n <= 7
#                                                 (if julia is on PATH or $JULIA is set)
#   Lean    verification/lean/LatticePaths.lean   kernel checks: star lemma k <= 6, canonical pairs
#                                                 k <= 7, skeleton identity m <= 6, skeleton count
#                                                 m <= 12, Shankar's conjecture n <= 3 (if lean is on
#                                                 PATH; the folder pins v4.34.1)
#
# Exit status 0 means every check that ran passed.
set -uo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
V="$ROOT/verification"
BUILD="$ROOT/build"
mkdir -p "$BUILD"
FAILED=0
fail() { echo "FAIL: $*"; FAILED=1; }
ok() { echo "ok:   $*"; }

echo "== C and C++"
cc -O2 -Wall -o "$BUILD/star_lemma" "$V/c/star_lemma.c" || fail "compile star_lemma.c"
c++ -O2 -Wall -std=c++17 -o "$BUILD/skeletons" "$V/cpp/skeletons.cpp" || fail "compile skeletons.cpp"
"$BUILD/star_lemma" 13 > "$BUILD/c.txt" && grep -q '^ALL OK' "$BUILD/c.txt" \
  && grep -q "k=13 .*canonical=  4096 .*exceptional=1 " "$BUILD/c.txt" \
  && ok "C: Lemmas 4.1, 4.2 and 5.2 for k <= 13" || fail "C (see build/c.txt)"
"$BUILD/skeletons" > "$BUILD/cpp.txt" && grep -q '^ALL OK' "$BUILD/cpp.txt" \
  && grep -q "m=5  .*extremal systems=10  all skeleton systems: yes" "$BUILD/cpp.txt" \
  && ok "C++: skeleton systems (m <= 10), exhaustive search (m <= 5), F_M (n <= 6)" || fail "C++ (see build/cpp.txt)"

echo "== Shell"
bash "$V/shell/check_paths.sh" > "$BUILD/sh.txt" 2>&1 && grep -q '^ALL OK' "$BUILD/sh.txt" \
  && ok "check_paths.sh" || fail "check_paths.sh (see build/sh.txt)"

echo "== Python"
if [ "${QUICK:-0}" = 1 ]; then PYARGS="5 4"; else PYARGS="6 5"; fi
python3 "$V/python/verify_sat.py" $PYARGS > "$BUILD/py.txt" 2>&1 && grep -q '^ALL OK' "$BUILD/py.txt" \
  && ok "verify_sat.py $PYARGS" || fail "verify_sat.py (see build/py.txt)"

echo "== Julia"
JULIA="${JULIA:-$(command -v julia || true)}"
if [ -z "$JULIA" ]; then echo "julia not found: skipping"; else
  "$JULIA" "$V/julia/verify_systems.jl" > "$BUILD/jl.txt" 2>&1 && grep -q '^ALL OK' "$BUILD/jl.txt" \
    && ok "verify_systems.jl" || fail "verify_systems.jl (see build/jl.txt)"
fi

echo "== Lean"
if ! command -v lean > /dev/null; then echo "lean not found: skipping (install elan)"; else
  out=$(cd "$V/lean" && lean LatticePaths.lean 2>&1); st=$?
  echo "$out" > "$BUILD/lean.txt"
  if [ $st -eq 0 ] && ! grep -q "error\|sorryAx" <<< "$out" \
       && [ "$(grep -c "does not depend on any axioms\|depends on axioms: \[propext\]" <<< "$out")" = 7 ]; then
    ok "LatticePaths.lean (kernel-checked)"
  else fail "LatticePaths.lean (see build/lean.txt)"; fi
fi

if [ $FAILED -eq 0 ]; then echo "ALL CHECKS PASSED"; else echo "SOME CHECKS FAILED"; fi
exit $FAILED
