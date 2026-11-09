"""Exact largest even and odd families in the a x 2 rectangle
(Proposition 8.7), by exact maximum clique.

usage: python3 two_rows_exact.py AMAX       (prints a, Meven(a,2), Modd(a,2))

A path is the pair (i, i') of the columns of its two North steps.
Needs ./maxclique built from maxclique.c.
"""
import os
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))


def common_edges(a, p, q):
    """Number of edges shared by the two-row paths p and q."""
    (i, ii), (k, kk) = p, q
    return (min(i, k) + max(0, min(ii, kk) - max(i, k)) + a - max(ii, kk)
            + (i == k) + (ii == kk))


def largest(a, par):
    paths = [(i, j) for i in range(a + 1) for j in range(i, a + 1)]
    rows = [''.join('1' if p != q and common_edges(a, p, q) % 2 == par else '0'
                    for q in paths) for p in paths]
    data = f"{len(paths)}\n" + "\n".join(rows) + "\n"
    out = subprocess.run([os.path.join(HERE, 'maxclique')], input=data,
                         capture_output=True, text=True, check=True).stdout
    return int(out.split('\n')[0])


def main():
    for a in range(2, int(sys.argv[1]) + 1):
        print(a, largest(a, 0), largest(a, 1), flush=True)


if __name__ == '__main__':
    main()
