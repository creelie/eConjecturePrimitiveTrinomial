"""Largest family of North-East paths from (0,0) to (a,b) whose pairwise
numbers of common edges all have a given parity, by exact maximum clique.

usage: python3 largest_family.py a b parity      (parity 0 = even, 1 = odd)

Prints the size of a largest family and one family, one path per line
(1 = North step, 0 = East step).  Needs the binary ./maxclique built from
maxclique.c (gcc -O2 -o maxclique maxclique.c).
"""
import itertools
import os
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))


def common_edges(x, y):
    """Number of edges shared by the paths with step words x and y."""
    c = wx = wy = 0
    for s, t in zip(x, y):
        if s == t and wx == wy:
            c += 1
        wx += s
        wy += t
    return c


def main():
    a, b, par = map(int, sys.argv[1:4])
    words = [x for x in itertools.product([0, 1], repeat=a + b) if sum(x) == b]
    rows = [''.join('1' if x != y and common_edges(x, y) % 2 == par else '0'
                    for y in words) for x in words]
    data = f"{len(words)}\n" + "\n".join(rows) + "\n"
    out = subprocess.run([os.path.join(HERE, 'maxclique')], input=data,
                         capture_output=True, text=True, check=True).stdout.split('\n')
    print(out[0])
    for i in sorted(map(int, out[1].split())):
        print(''.join(map(str, words[i])))


if __name__ == '__main__':
    main()
