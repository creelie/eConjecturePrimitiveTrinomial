# Parity Families of Lattice Paths and Real-Rooted Signed Eulerian Polynomials

Deep Bhattacharjee

Concept DOI (all versions): [10.5281/zenodo.23281333](https://doi.org/10.5281/zenodo.23281333)

The paper is `paper/LatticePathsPaper.pdf`. This archive holds the machine checks of its finite
statements: kernel-checked theorems in Lean 4 and exact computations in Julia. No result uses
floating point; all arithmetic is in integers or rationals of arbitrary size. Contact for
GitHub-related matters: egspl@proton.me.

## Lean (`lean/`)

Lean 4.24.0, core library only (no Mathlib). Every theorem is proved by `decide +kernel`, so the
Lean kernel evaluates the definitions itself; there is no `native_decide`, no `sorry` and no axiom.
`lean/axioms.txt` is the output of `#print axioms` for all 29 theorems: none depends on any axiom.

    lean LatticePaths.lean      # 14 theorems, about 2 minutes
    lean Enumerative.lean       # 15 theorems, about 2 minutes

`LatticePaths.lean` (words are natural numbers, bit i-1 = i-th letter, 1 = N, 0 = E):

| theorem | statement |
|---|---|
| `star_lemma`, `canonical_pairs`, `skeleton_identity`, `skeleton_count` | the star lemma for k <= 6, the canonical pairs for k <= 7, the skeleton identity for m <= 6, the number C(m, floor(m/2)) of skeletons for m <= 12 |
| `shankar_n1`, `shankar_n2`, `shankar_n3` | for n <= 3 there are exactly C_n families of 2^n paths with pairwise even numbers of common edges, and none of 2^n + 1 paths |
| `three_rows_even` | for a = 4, 8, 10, 12 the family T_a has 2a - 2 paths from (0,0) to (a,3), pairwise with an even number of common edges |
| `square_odd` | the families F_10 and F_12 have 33 and 54 paths in the square, pairwise with an odd number of common edges |
| `odd_family_7`, `odd_family_8` | explicit families of 23 paths (side 7) and 31 paths (side 8), pairwise with an odd number of common edges |
| `block_families_dim3`, `_dim4`, `_dim5` | over d letters the d^r concatenations of r blocks ab, ba, cc pairwise share an even number of edges (d = 3, 4: r <= 3; d = 5: r <= 2) |

`Enumerative.lean` (polynomials are lists of integer coefficients):

| theorem | statement |
|---|---|
| `eulerian_des`, `eulerian_exc` | descents and excedances over S_n are Eulerian, n <= 7, by enumeration |
| `mantaci`, `desarmenien_foata` | the two signed identities for n <= 7, by enumeration |
| `small_even_odd` | P_3, P_4, Q_4, P_5, Q_5 by enumeration of the even and odd permutations |
| `p5_identity` | 2 P_5 = A_5 + (1 - t)^4 and 4 P_5 = (2t^2 + 11t + 2)^2 + 15 t^2 as coefficient lists |
| `caged_example` | c(6 7 2 1 5 9 8 3 4) = 3 with exactly 16 maximal pairs |
| `dumont_small`, `dumont_table` | a(n, j) by enumeration equals the closed formula for n <= 4; the rows n = 4, 8 of the table |
| `q_values` | Q_0, ..., Q_24 by dynamic programming from the definition |
| `hankel_shifted`, `hankel_unshifted` | det(Q_(i+j+1))_{12x12} and det(Q_(i+j))_{13x13} are the stated negative integers, by fraction-free elimination and by the division-free characteristic polynomial |
| `hankel_minors_positive` | the smaller leading Hankel determinants are positive |
| `steiner_path` | 2-Steiner matrix of the path P_n, 3 <= n <= 10: a_0 = -(n-1), a_(2n-4) = -(3n-5), a_(2n-5) = -(n-1)(n-2)(2n^2+6n-15)/6 |
| `steiner_peak` | for 6 <= n <= 10 the largest \|a_i\|, i <= 2n-4, is at i = n-1 only |

## Julia (`julia/`)

Julia 1.11, standard library only. Each script prints `PASS:` / `FAIL:` lines and ends with
`SUMMARY: p passed, f failed`; `run_all.jl` runs all of them and prints the total
(653 passed, 0 failed, about 16 minutes; the output is kept in `run_all.log`).

    julia run_all.jl

| script | what it checks |
|---|---|
| `verify_systems.jl` | skeletons and nonnegative paths (m <= 22), the induction step on skeleton systems (m <= 9), the groupings (k <= 4), the families F_M (n <= 7) |
| `odd_families.jl` | the odd families of `data/best7.txt`, `best8.txt`, `best9.txt` (23, 31, 36 paths); the three-row families T_a for even a <= 60; the window families in the square for n <= 30, pair by pair, with their sizes and the bound n^2/2 - 3n |
| `blocks.jl` | block families over d = 2, ..., 6 letters; the weighted inequality for all families with (d, m) = (3, 2), (2, 4) and for greedy maximal families with (d, m) = (3, 4), (4, 3), (4, 4) |
| `regions.jl` | n <= 6: heights in F_M, strips and random regions, a forbidden point, Dyck paths (largest even family 2^(n-1), unique, by exact clique search), intersections 2^c for pairs and triples, numbers of meander systems, the Gram matrix is nonsingular with the product formula for its determinant |
| `searches.jl` | every exhaustive search reported in Sections 4 to 7, by exact maximum-clique search: the table of M(a,b), M*(a,b); two rows for a <= 22; three and four rows; Modd(n,n) for n <= 6; Modd(n+1,n) = 2^n for n <= 5 with the C_(n+1) families for n <= 4; free endpoints; tau and the column space of A_(a,b); pairs of matchings by loops; sigma(M); families through (i, i+1); the table of 26 boxes; free endpoints over d letters |
| `eulerian.jl` | Eulerian numbers and the signed identities for n <= 8 by enumeration; the identity for P_5; exact numbers of real roots of B_n, C_n, P_n, Q_n for 2 <= n <= 60 by Sturm sequences (only P_3, P_4, Q_4, P_5 have non-real roots) |
| `canon.jl` | descent polynomials of the 321-avoiding canon words for k <= 110 (log-concave), their numbers of nonreal zeros for k <= 45, and the classes of lattice words on four letters for k <= 6 |
| `caged.jl` | the example for n = 9; exhaustive search for 5 <= n <= 10 and the counts of extremal permutations, orbits and extremal n-cycles for n <= 14; the permutations beta(mu) for k <= 5; the five-term inequality for n <= 8; the n-cycle construction for 8 <= n <= 60 and the ten explicit cycles |
| `dumont.jl` | a(n, j) for n <= 7 by enumeration against the closed formula; the transfer recursion, the table, the recurrence, the polynomials G_j, the first-letter count |
| `hankel.jl` | Q_k by enumeration (k <= 5), by two dynamic programmes and by Shankar's multisum (k <= 24); the two Hankel determinants by rational and by fraction-free elimination; an explicit vector v with v^T H v < 0 |
| `steiner.jl` | characteristic polynomials of the 2-Steiner matrix of P_n for 3 <= n <= 60 (two methods for n <= 16); the formula for a_(2n-5); the unique index of the largest coefficient for 6 <= n <= 60 |
| `common.jl` | shared helpers (common edges, permutations, exact determinants) |
