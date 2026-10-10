#!/usr/bin/env bash
# check_paths.sh -- bash integer arithmetic only, no other programs.
#
#   1. Lemma 4.1 (star lemma) for k <= 6, from a precomputed table of B.
#   2. Theorem 1.1 for n <= 3: the even-intersecting families of 2^n paths from (0,0) to (n,n)
#      are counted by a clique search (1, 2, 5), none has 2^n + 1 paths, and each family F_M of a
#      Dyck matching is one of them.
#   3. Corollary 1.3: the skeletons of [m] number C(m, floor(m/2)) for m <= 16.
#
# A word of length k is an integer: bit i-1 holds the i-th letter (1 = N, 0 = E).
# Prints ALL OK when every check passes.
set -u
FAILED=0
fail() { echo "FAIL: $*"; FAILED=1; }

# B k x y -> RET: parity of the number of i with x_i = y_i and w(x_{<i}) = w(y_{<i})
B() {
  local k=$1 x=$2 y=$3 s=0 d=0 i xi yi
  for ((i = 0; i < k; i++)); do
    xi=$(( (x >> i) & 1 )); yi=$(( (y >> i) & 1 ))
    (( d == 0 && xi == yi )) && s=$(( s ^ 1 ))
    d=$(( d + xi - yi ))
  done
  RET=$s
}
wt() { local x=$1 c=0; while (( x )); do c=$(( c + (x & 1) )); x=$(( x >> 1 )); done; RET=$c; }

echo "== star lemma"
for ((k = 1; k <= 6; k++)); do
  N=$(( 1 << k )); declare -a T W
  for ((x = 0; x < N; x++)); do
    wt $x; W[x]=$RET
    for ((y = 0; y < N; y++)); do B $k $x $y; T[x*N+y]=$RET; done
  done
  last=$(( 1 << (k - 1) )); ea=1; eb=0
  for ((i = 1; i < k; i++)); do
    if (( i % 2 )); then ea=$(( ea | (1 << i) )); else eb=$(( eb | (1 << i) )); fi
  done
  canon=0; exc=0; other=0
  for ((a = 0; a < N; a++)); do
    for ((b = 0; b < N; b++)); do
      (( W[a] == W[b] + 1 && T[a*N+b] == ((k + 1) & 1) )) || continue
      ok=1
      for ((c = 0; c < N; c++)); do
        if (( W[c] != W[a] && W[c] != W[b] && T[a*N+c] != T[b*N+c] )); then ok=0; break; fi
      done
      (( ok )) || continue
      if (( (a & ~last) == (b & ~last) && (a & last) && !(b & last) )); then canon=$(( canon + 1 ))
      elif (( k % 2 == 1 && k >= 3 && a == ea && b == eb )); then exc=$(( exc + 1 ))
      else other=$(( other + 1 )); fi
    done
  done
  want_exc=$(( k % 2 == 1 && k >= 3 ? 1 : 0 ))
  echo "k=$k  canonical=$canon (2^(k-1)=$last)  exceptional=$exc  other=$other"
  (( canon == last && exc == want_exc && other == 0 )) || fail "star lemma at k=$k"
  unset T W
done

echo "== Shankar's conjecture for n <= 3"
# cliques S LIST... : number of cliques of size S among the listed paths (global n2 = 2n)
cliques() {
  local s=$1; shift
  if (( s == 0 )); then RET=1; return; fi
  if (( $# == 0 )); then RET=0; return; fi
  local v=$1; shift
  local rest=("$@") nb=() x total
  for x in "${rest[@]}"; do B $n2 $v $x; (( RET == 0 )) && nb+=("$x"); done
  cliques $(( s - 1 )) "${nb[@]}"; total=$RET
  cliques $s "${rest[@]}"; RET=$(( total + RET ))
}
for ((n = 1; n <= 3; n++)); do
  n2=$(( 2 * n )); P=()
  for ((x = 0; x < (1 << n2); x++)); do wt $x; (( RET == n )) && P+=("$x"); done
  cliques $(( 1 << n )) "${P[@]}"; exact=$RET
  cliques $(( (1 << n) + 1 )) "${P[@]}"; above=$RET
  catalan=$(( n == 1 ? 1 : (n == 2 ? 2 : 5) ))
  echo "n=$n  paths=${#P[@]}  even families of size 2^n: $exact (C_n=$catalan)  of size 2^n+1: $above"
  (( exact == catalan && above == 0 )) || fail "family count at n=$n"
done
# the five families F_M for n = 3, as orientations of the five Dyck matchings of {0..5}
for M in "0 1 2 3 4 5" "0 1 2 5 3 4" "0 3 1 2 4 5" "0 5 1 2 3 4" "0 5 1 4 2 3"; do
  set -- $M; F=()
  for ((o = 0; o < 8; o++)); do
    x=$(( ((o & 1) ? 1 << $1 : 1 << $2) | ((o & 2) ? 1 << $3 : 1 << $4) | ((o & 4) ? 1 << $5 : 1 << $6) ))
    F+=("$x")
  done
  for x in "${F[@]}"; do for y in "${F[@]}"; do
    (( x == y )) && continue; B 6 $x $y; (( RET == 0 )) || fail "F_M not even for M = $M"
  done; done
done
echo "the five families F_M for n = 3 are even-intersecting"

echo "== skeleton count"
# skel POS DEPTH M -> number of completions; free points only at depth 0
for ((m = 0; m <= 16; m++)); do
  declare -a cnt new; cnt=(1); for ((h = 1; h <= m + 1; h++)); do cnt[h]=0; done
  for ((pos = 0; pos < m; pos++)); do
    for ((h = 0; h <= m + 1; h++)); do new[h]=0; done
    for ((h = 0; h <= m; h++)); do
      (( cnt[h] )) || continue
      new[h+1]=$(( new[h+1] + cnt[h] ))
      if (( h > 0 )); then new[h-1]=$(( new[h-1] + cnt[h] )); else new[0]=$(( new[0] + cnt[0] )); fi
    done
    for ((h = 0; h <= m + 1; h++)); do cnt[h]=${new[h]}; done
  done
  c=1; for ((i = 1; i <= m / 2; i++)); do c=$(( c * (m - m / 2 + i) / i )); done
  (( cnt[0] == c )) || fail "skeleton count at m=$m"
  (( m % 4 == 0 )) && echo "m=$m  skeletons=${cnt[0]}  C(m,floor(m/2))=$c"
  unset cnt new
done

if (( FAILED )); then echo "FAILED"; exit 1; fi
echo "ALL OK"
