# Catalan Rigidity of Even Lattice Paths

Deep Bhattacharjee

Concept DOI (all versions): [10.5281/zenodo.23281333](https://doi.org/10.5281/zenodo.23281333)

A family of North–East lattice paths from (0,0) to (n,n) in which any two paths share an even number of
edges has at most 2^n members (Shankar, arXiv:2607.23117). The paper proves Shankar's conjecture that
exactly C_n families attain this bound, one for each noncrossing perfect matching, by classifying all
equality cases of the underlying inequality, and continues with:

- the binary rank ab − gcd(a+1, b+1) + 1 of every grid graph;
- eventown and oddtown bounds for paths in every rectangle;
- at least C_{n+1} odd families of size 2^n of paths from (0,0) to (n+1, n);
- the largest odd family in the n × n square: 1, 2, 3, 6, 10, 16 for n ≤ 6, and at least 20 and 28 for
  n = 7, 8;
- even and odd families in the a × 2 rectangle of sizes ⌊a/2⌋+3, ⌊(5a−1)/4⌋, ⌊(5a−2)/4⌋, optimal for
  a ≤ 22.

Open: the growth of the largest odd family in the square, whether 2^n bounds the odd families from
(0,0) to (n+1, n), and the exact even value in rectangles that are not squares.
The second problem is reduced to a conjecture on paths with free endpoints (Conjecture 9.2,
Proposition 9.3): paths of odd length m from (0,0) with pairwise odd numbers of common edges number at
most 2^((m−1)/2); this is verified for m ≤ 9.

`preprintCatalanRigidity/` holds the LaTeX source and PNG figures (`figsrc/` draws the plots);
`dist/catalan-rigidity-even-lattice-paths.pdf` and `-tex.zip` are the compiled paper and its source.
`verification/catalan-rigidity/` holds the exact maximum clique search, the search for paths with free
endpoints and the checks of the two-row families (see its README).

The rest of this README describes the first paper, which proves Shankar's conjecture alone.

## Even-intersecting families of lattice paths and the Catalan numbers

Shankar (*Oddtown and eventown theorems for lattice paths*, arXiv:2607.23117) proved that a family of
North–East lattice paths from (0,0) to (n,n) in which any two paths share an even number of edges has at
most 2^n members. For a noncrossing perfect matching M of {1, …, 2n}, the paths whose steps differ at the
two ends of every pair of M form such a family F_M of size 2^n, so there are at least C_n extremal families.
Shankar conjectured that there are no others (his Conjecture 4.1, checked by him for n ≤ 5).

The conjecture is true. The paper proves:

1. **Theorem 1.1.** Every family of 2^n paths from (0,0) to (n,n) with pairwise even intersections is F_M
   for a noncrossing perfect matching M; so there are exactly C_n of them.
2. **Theorem 1.2.** Shankar's bound comes from an inequality Σ|A|² ≤ 2^m for "admissible systems" of sets
   of binary words of length m (his Lemma 2.3). Equality holds exactly for the *skeleton systems*: take a
   noncrossing partial matching of {1, …, m} whose unmatched points lie under no arc, and group the words
   that alternate on every arc by their letters at the unmatched points.
3. **Corollary 1.3.** There are exactly C(m, ⌊m/2⌋) extremal admissible systems of length m.

The proof follows Shankar's induction, which deletes the last letter. For an extremal system the two
systems of length m − 1 it produces coincide (a merging argument on overlapping classes), so by induction
they form a skeleton system, and the system of length m comes from pairing some of its classes. A
rigidity lemma (Lemma 4.1) says that two words of adjacent weights that no word of another weight can
tell apart differ only in the last letter, or form the pair 1(10)^j, 0(01)^j; its proof flips paths across
unit squares, which shows that the vertex sets of the two paths differ by a pattern constant along
diagonals. A counting argument removes the exceptional pair, and only two pairings survive; each gives
a skeleton system of length m.

### Paper

`preprintLatticePaths/` holds the LaTeX source and the TikZ figures; `dist/` holds the PDF, a source zip
(figures as PNG) and an arXiv tarball (figures as PDF), rebuilt by `scripts/build_paper.sh`.

### Checks

```
verification/c/star_lemma.c            for every word length k <= 13: the cell identity (Lemma 4.2) at every
                                       path and unit square, the star lemma (Lemma 4.1) from its hypotheses,
                                       and the formula of Lemma 5.2 for canonical pairs
verification/cpp/skeletons.cpp         skeleton systems: B_m(x,y) = B_k(a,a') pair by pair, admissible and
                                       extremal, all different, C(m, m/2) of them (m <= 10); an exhaustive
                                       search over all admissible systems of length m <= 5, built from all
                                       partial set partitions of each weight level: the largest total of
                                       squares is 2^m and the extremal systems are the skeleton systems;
                                       the C_n families F_M for n <= 6
verification/shell/check_paths.sh      bash integer arithmetic only: the star lemma for k <= 6; Shankar's
                                       conjecture for n <= 3 by counting cliques (1, 2, 5, none larger);
                                       skeleton counts for m <= 16
verification/python/verify_sat.py      SAT (python-sat, CaDiCaL): all extremal admissible systems of length
                                       m <= 6 are the skeleton systems and none beats 2^m; Shankar's
                                       conjecture for n <= 5 (1, 2, 5, 14, 42 families, none larger);
                                       Proposition 5.1 for k <= 7; the star lemma for k <= 9
verification/julia/verify_systems.jl   the bijection between skeletons and nonnegative paths (m <= 14) and
                                       its count (m <= 22); the induction step of Section 3 on every skeleton
                                       system of length m <= 9; Proposition 5.1 for k <= 4 by depth-first
                                       search; the families F_M for n <= 7 with edges counted as edges
verification/lean/LatticePaths.lean    Lean 4 kernel checks (decide +kernel, no Mathlib): the star lemma for
                                       k <= 6, Lemma 5.2 for k <= 7, Proposition 2.2 for m <= 6, the
                                       skeleton count for m <= 12, and Shankar's conjecture for n <= 3
```

The proofs in the paper are by hand and cover every n and m; the programs check the statements and the
key lemmas independently on all small cases.

`scripts/run_all.sh` runs them all (`QUICK=1` stops the SAT checks at m <= 5 and n <= 4); the `verify`
workflow runs them on every pull request.

## Citation

Cite the GitHub release; see `CITATION.cff`.

| Release | Link |
|---|---|
| v2.0.0 | https://github.com/creelie/eConjecturePrimitiveTrinomial/releases/tag/v2.0.0, DOI [10.5281/zenodo.24090676](https://doi.org/10.5281/zenodo.24090676) |
| v2.1.0 | https://github.com/creelie/eConjecturePrimitiveTrinomial/releases/tag/v2.1.0, DOI [10.5281/zenodo.24091548](https://doi.org/10.5281/zenodo.24091548) |
| v2.2.0 | https://github.com/creelie/eConjecturePrimitiveTrinomial/releases/tag/v2.2.0, DOI [10.5281/zenodo.24124754](https://doi.org/10.5281/zenodo.24124754) |
| v1.1.0 | https://github.com/creelie/eConjecturePrimitiveTrinomial/releases/tag/v1.1.0 |
| v1.0.0 | https://github.com/creelie/eConjecturePrimitiveTrinomial/releases/tag/v1.0.0 |

## Licence

MIT, see `LICENSE`.
