**Even-intersecting families of lattice paths and the Catalan numbers**, by Deep Bhattacharjee.

Shankar proved that a family of North–East lattice paths from (0,0) to (n,n) in which any two paths share an even number of edges has at most 2^n members, and conjectured that exactly C_n families attain the bound (arXiv:2607.23117, Conjecture 4.1). The paper proves the conjecture and determines all equality cases of the inequality behind the bound.

| Step | Content |
|---|---|
| Proposition 2.2 | Skeleton systems (noncrossing partial matchings with no unmatched point under an arc) are extremal |
| Lemmas 3.1–3.5 | Shankar's induction: for an extremal system both shorter systems coincide, and the system is a pairing of their classes |
| Lemma 4.1 | Rigidity: two words of adjacent weights that no word of another weight can tell apart differ only in the last letter, or form 1(10)^j, 0(01)^j |
| Proposition 5.1 | Only two pairings exist |
| Theorem 1.2, Corollary 1.3 | Extremal systems are the skeleton systems; there are C(m, ⌊m/2⌋) of them |
| Theorem 1.1 | Shankar's conjecture: the extremal families are exactly the C_n families F_M |

Version 1.1.0 cites this release in the data availability statement and adds `paper/paper1` (PDF) and `paper/paper2` (tex zip). The mathematics is that of v1.0.0.

The proofs are by hand. Checks in C, C++, Bash, Python (SAT), Julia and Lean 4 (kernel) confirm the lemmas and the theorems on all small cases: the rigidity lemma for word lengths up to 13, all extremal systems up to length 6, and Shankar's conjecture up to n = 5.

Files:
- `even-lattice-paths-catalan.pdf`: the paper
- `even-lattice-paths-catalan-tex.zip`: LaTeX source with the figures as PNG (and their TikZ sources)
- `even-lattice-paths-catalan-arxiv.tar.gz`: LaTeX source with the figures as PDF, ready for arXiv

Run `scripts/run_all.sh` to repeat the checks and `scripts/build_paper.sh` to rebuild the files above.
