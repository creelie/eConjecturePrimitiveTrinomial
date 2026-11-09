"""Largest set of North-East paths of odd length m from (0,0), with free
endpoints, in which every two paths share an odd number of edges, by exact
maximum clique.

usage: python3 free_end_families.py m          (all 2^m paths)
       python3 free_end_families.py m p        (only paths whose number of
                                                North steps is congruent to p)

The conjecture of Section 9 of the paper predicts the size 2^((m-1)/2);
with a parity p and m = 2k+1 the size is f(k), predicted to be 2^k.
Prints the size and one largest set, one path per line (1 = North, 0 = East).
Needs the binary ./maxclique built from maxclique.c.
"""
import itertools
import os
import subprocess
import sys

from largest_family import HERE, common_edges


def main():
    m = int(sys.argv[1])
    words = list(itertools.product([0, 1], repeat=m))
    if len(sys.argv) > 2:
        p = int(sys.argv[2])
        words = [x for x in words if sum(x) % 2 == p]
    rows = [''.join('1' if x != y and common_edges(x, y) % 2 == 1 else '0'
                    for y in words) for x in words]
    data = f"{len(words)}\n" + "\n".join(rows) + "\n"
    out = subprocess.run([os.path.join(HERE, 'maxclique')], input=data,
                         capture_output=True, text=True, check=True).stdout.split('\n')
    size = int(out[0])
    fam = [words[i] for i in sorted(map(int, out[1].split()))]
    assert len(fam) == size
    assert all(common_edges(x, y) % 2 == 1 for x, y in itertools.combinations(fam, 2))
    print(size)
    for x in fam:
        print(''.join(map(str, x)))


if __name__ == '__main__':
    main()
