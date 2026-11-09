**Catalan Rigidity of Even Lattice Paths**, by Deep Bhattacharjee.

A family of North–East lattice paths from (0,0) to (n,n) in which any two paths share an even number of edges has at most 2^n members (Shankar, arXiv:2607.23117). The paper proves Shankar's conjecture that exactly C_n families attain this bound, one for each noncrossing perfect matching, by classifying all equality cases of the underlying inequality, and continues with parity families of paths in every rectangle.

| Result | Content |
|---|---|
| Theorems A, B | Shankar's conjecture; the extremal admissible systems are the skeleton systems, C(m, ⌊m/2⌋) of them |
| Grid rank | the binary rank of the a × b grid graph is ab − gcd(a+1, b+1) + 1 |
| Rectangles | eventown and oddtown bounds for paths from (0,0) to (a,b) |
| Odd length | at least C_{n+1} odd families of size 2^n from (0,0) to (n+1, n) |
| Square, odd | largest odd family 1, 2, 3, 6, 10, 16 for n ≤ 6; at least 20 and 28 for n = 7, 8 |
| Two rows (Theorem 8.6, Proposition 8.7) | families of sizes ⌊a/2⌋+3, ⌊(5a−1)/4⌋, ⌊(5a−2)/4⌋ in the a × 2 rectangle, optimal for a ≤ 22 |

Open problems stated in the paper: the growth of the largest odd family in the square, whether 2^n bounds the odd families from (0,0) to (n+1, n), and the exact even value in rectangles that are not squares.

Files:
- `catalan-rigidity-even-lattice-paths.pdf`: the paper
- `catalan-rigidity-even-lattice-paths-tex.zip`: LaTeX source with the figures as PNG
- `even-lattice-paths-catalan.pdf`, `-tex.zip`, `-arxiv.tar.gz`: the earlier paper on Shankar's conjecture

`verification/catalan-rigidity/` repeats the exact searches and checks the two-row families; `scripts/run_all.sh` repeats the checks of the earlier paper.
