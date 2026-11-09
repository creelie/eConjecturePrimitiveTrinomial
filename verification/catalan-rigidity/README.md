# Checks for "Catalan Rigidity of Even Lattice Paths"

```
gcc -O2 -o maxclique maxclique.c
python3 largest_family.py 5 5 1     # Modd(5,5) = 10 and a family attaining it
python3 two_rows_exact.py 22        # Meven(a,2), Modd(a,2) for a <= 22 (Proposition 8.7)
python3 two_rows_constructions.py   # the families of Theorem 8.6, checked for a <= 60
python3 free_end_families.py 9      # Conjecture 9.2 at m = 9: 16 = 2^4
python3 free_end_families.py 9 0    # f(4) = 16 (Proposition 9.3), words of even weight
```

`largest_family.py a b p` finds a largest family of paths from (0,0) to (a,b) whose pairwise numbers of
common edges are all congruent to p mod 2 (Proposition 8.8 for the square, Appendix A of the paper).
The exact values are maximum cliques; the paper states which ones are proved by hand.

`free_end_families.py m [p]` finds a largest set of paths of odd length m from (0,0), with free endpoints,
whose pairwise numbers of common edges are odd (Conjecture 9.2); with p only paths with a number of North
steps congruent to p mod 2 are used, which gives f(k) of Proposition 9.3 for m = 2k + 1.
