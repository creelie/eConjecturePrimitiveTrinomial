"""verify_sat.py -- SAT and brute-force checks of the paper's results for small lengths.

Words of length m are tuples of 0/1 (1 = N, 0 = E).  B(x, y) is the parity of the number of
positions i with x_i = y_i and w(x_{<i}) = w(y_{<i}), the parity of the number of common edges.

  1. Theorem 1.2 for m <= 6 (MAXM): with a SAT solver, every extremal admissible system of
     length m is a skeleton system, there are C(m, floor(m/2)) of them, and no admissible system
     has squares of class sizes adding up to more than 2^m (Lemma 2.3).
  2. Theorem 1.1 for n <= 4 (MAXN): the families of 2^n paths from (0,0) to (n,n) with pairwise
     even common edges are exactly the C_n families F_M.
  3. Proposition 5.1 for k <= 7: the groupings of {0,1}^k into singletons and pairs satisfying
     (G1)-(G3) are the grouping with no pairs and the grouping into all canonical pairs.
  4. Lemma 4.1 (star lemma) for k <= 9, by brute force.

Needs python-sat (pip install python-sat).  Prints ALL OK when every check passes.
Usage: python3 verify_sat.py [MAXM [MAXN]]
"""
import itertools
import sys
import time
from math import comb

from pysat.card import CardEnc, EncType
from pysat.formula import IDPool
from pysat.solvers import Cadical153

FAIL = []


def check(ok, what):
    if not ok:
        FAIL.append(what)
        print("FAIL:", what)


def B(x, y):
    s = wx = wy = 0
    for xi, yi in zip(x, y):
        if xi == yi and wx == wy:
            s ^= 1
        wx += xi
        wy += yi
    return s


def words(m):
    return list(itertools.product((0, 1), repeat=m))


def skeletons(m):
    """All (arcs, free points) with noncrossing arcs and no free point inside an arc."""
    out = []

    def rec(pos, stack, arcs, free):
        if pos == m:
            if not stack:
                out.append((tuple(arcs), tuple(free)))
            return
        if len(stack) + 1 <= m - pos - 1:
            rec(pos + 1, stack + [pos], arcs, free)
        if stack:
            rec(pos + 1, stack[:-1], arcs + [(stack[-1], pos)], free)
        else:
            rec(pos + 1, stack, arcs, free + [pos])

    rec(0, [], [], [])
    return out


def skeleton_system(m, arcs, free):
    classes = []
    for a in itertools.product((0, 1), repeat=len(free)):
        cls = []
        for o in itertools.product((0, 1), repeat=len(arcs)):
            x = [None] * m
            for s, e in zip(free, a):
                x[s] = e
            for (p, q), e in zip(arcs, o):
                x[p], x[q] = e, 1 - e
            cls.append(tuple(x))
        classes.append(frozenset(cls))
    return frozenset(classes)


# ---------------------------------------------------------------- 1. extremal admissible systems
def extremal_systems(m, target):
    """SAT model: y[w,v] says that w lies in the class whose smallest word is v."""
    W = words(m)
    order = {w: i for i, w in enumerate(W)}
    wt = {w: sum(w) for w in W}
    pool = IDPool()
    y = {}
    for w in W:
        for v in W:
            if order[v] <= order[w] and wt[v] == wt[w]:
                y[w, v] = pool.id(("y", w, v))
    cl = []
    byw = {w: [v for v in W if (w, v) in y] for w in W}
    for w in W:
        lits = [y[w, v] for v in byw[w]]
        cl += CardEnc.atmost(lits=lits, bound=1, vpool=pool, encoding=EncType.pairwise).clauses
        for v in byw[w]:
            if v != w:
                cl.append([-y[w, v], y[v, v]])
    members = {v: [w for w in W if (w, v) in y] for v in W}
    par = m & 1
    for v in W:
        for w1, w2 in itertools.combinations_with_replacement(members[v], 2):
            if B(w1, w2) != par:
                cl.append([-y[w1, v], -y[w2, v]])
    # constant value z[v,v'] between the classes with smallest words v and v'
    reps = [v for v in W if (v, v) in y]
    for v1, v2 in itertools.combinations(reps, 2):
        z = pool.id(("z", v1, v2))
        for w1 in members[v1]:
            for w2 in members[v2]:
                if w1 == w2:
                    continue
                cl.append([-y[w1, v1], -y[w2, v2], z if B(w1, w2) else -z])
    # sum of squares = #used words + 2 #(unordered pairs in one class)
    count = []
    for w in W:
        u = pool.id(("u", w))
        cl.append([-u] + [y[w, v] for v in byw[w]])
        count.append(u)
    for w1, w2 in itertools.combinations(W, 2):
        if wt[w1] != wt[w2]:
            continue
        common = [v for v in byw[w1] if (w2, v) in y]
        if not common:
            continue
        q, q2 = pool.id(("q", w1, w2)), pool.id(("q2", w1, w2))
        rs = []
        for v in common:
            r = pool.id(("r", w1, w2, v))
            cl += [[-r, y[w1, v]], [-r, y[w2, v]]]
            rs.append(r)
        cl.append([-q] + rs)
        cl.append([-q2, q])
        count += [q, q2]
    if target > len(count):
        return set()
    cl += CardEnc.atleast(lits=count, bound=target, vpool=pool, encoding=EncType.seqcounter).clauses
    ylits = list(y.values())
    found = set()
    with Cadical153(bootstrap_with=cl) as s:
        while s.solve():
            model = set(l for l in s.get_model() if l > 0)
            cls = {}
            for (w, v), lit in y.items():
                if lit in model:
                    cls.setdefault(v, set()).add(w)
            found.add(frozenset(frozenset(c) for c in cls.values()))
            s.add_clause([-l if l in model else l for l in ylits])
    return found


def check_theorem_1_2(maxm):
    for m in range(0, maxm + 1):
        t0 = time.time()
        found = extremal_systems(m, 2 ** m)
        skel = {skeleton_system(m, a, f) for a, f in skeletons(m)}
        over = extremal_systems(m, 2 ** m + 1)
        check(found == skel, "m=%d: extremal systems are the skeleton systems" % m)
        check(len(skel) == comb(m, m // 2), "m=%d: C(m, m//2) skeleton systems" % m)
        check(not over, "m=%d: no admissible system beats 2^m" % m)
        print("m=%d  extremal systems=%d  skeleton systems=%d  C(m,m//2)=%d  equal=%s  above 2^m: %d  (%.1fs)"
              % (m, len(found), len(skel), comb(m, m // 2), found == skel, len(over), time.time() - t0))


# ---------------------------------------------------------------- 2. Shankar's conjecture
def edges(w):
    x = y = 0
    E = set()
    for s in w:
        E.add((x, y, s))
        if s:
            y += 1
        else:
            x += 1
    return frozenset(E)


def check_theorem_1_1(maxn):
    for n in range(1, maxn + 1):
        t0 = time.time()
        P = [w for w in words(2 * n) if sum(w) == n]
        E = [edges(w) for w in P]
        N = len(P)
        pool = IDPool(start_from=N + 1)
        cl = [[-(i + 1), -(j + 1)] for i in range(N) for j in range(i + 1, N) if len(E[i] & E[j]) % 2]
        card = CardEnc.atleast(lits=list(range(1, N + 1)), bound=2 ** n, vpool=pool, encoding=EncType.seqcounter)
        found = set()
        with Cadical153(bootstrap_with=cl + card.clauses) as s:
            while s.solve():
                m = s.get_model()
                found.add(frozenset(P[i] for i in range(N) if m[i] > 0))
                s.add_clause([-(i + 1) for i in range(N) if m[i] > 0])
        catalan = {next(iter(skeleton_system(2 * n, a, f))) for a, f in skeletons(2 * n) if not f}
        sizes = {len(f) for f in found}
        check(found == catalan, "n=%d: the extremal families are the F_M" % n)
        check(sizes == {2 ** n}, "n=%d: no family has more than 2^n paths" % n)
        print("n=%d  paths=%d  families of size >= 2^n: %d  sizes=%s  C_n=%d  all F_M: %s  (%.1fs)"
              % (n, N, len(found), sorted(sizes), comb(2 * n, n) // (n + 1), found == catalan, time.time() - t0))


# ---------------------------------------------------------------- 3. groupings
def check_groupings(maxk):
    for k in range(0, maxk + 1):
        U = words(k)
        cand = [(a, b) for a in U for b in U if sum(a) == sum(b) + 1 and B(a, b) == (k + 1) & 1]
        var = {p: i + 1 for i, p in enumerate(cand)}
        cov = {u: [] for u in U}
        for p in cand:
            cov[p[0]].append(var[p])
            cov[p[1]].append(var[p])

        def val(it1, it2):  # value of B_{k+1} on the class items (word, appended letter)
            (x, e), (z, f) = it1, it2
            return (B(x, z) + (1 if e == f and sum(x) == sum(z) else 0)) & 1

        def const(P, Q):
            return len({val(x, z) for x in P for z in Q}) == 1

        cl = [[-v1, -v2] for u in U for v1, v2 in itertools.combinations(cov[u], 2)]
        for i, p in enumerate(cand):
            P = [(p[0], 0), (p[1], 1)]
            for q in cand[i + 1:]:
                if set(p) & set(q):
                    continue
                if not const(P, [(q[0], 0), (q[1], 1)]):
                    cl.append([-var[p], -var[q]])
            for c in U:
                if c in p:
                    continue
                # if c is a singleton, both items (c,0) and (c,1) are classes
                if not (const(P, [(c, 0)]) and const(P, [(c, 1)])):
                    cl.append([-var[p]] + cov[c])
        sols = []
        with Cadical153(bootstrap_with=cl) as s:
            while s.solve():
                true = set(l for l in s.get_model() if l > 0)
                chosen = sorted(p for p in cand if var[p] in true)
                sols.append(tuple(chosen))
                if not cand:
                    break
                s.add_clause([-var[p] if var[p] in true else var[p] for p in cand])
        canon = tuple(sorted((u + (1,), u + (0,)) for u in words(k - 1))) if k else ()
        expect = sorted({(), canon})
        check(sorted(sols) == expect, "k=%d: only the two groupings" % k)
        print("k=%d  candidate pairs=%d  groupings=%d  (no pairs, all canonical pairs): %s"
              % (k, len(cand), len(sols), sorted(sols) == expect))


# ---------------------------------------------------------------- 4. star lemma
def check_star(maxk):
    for k in range(1, maxk + 1):
        U = words(k)
        idx = {u: i for i, u in enumerate(U)}
        T = [[B(a, c) for c in U] for a in U]
        wt = [sum(u) for u in U]
        found = []
        for a in U:
            for b in U:
                ia, ib = idx[a], idx[b]
                if wt[ia] != wt[ib] + 1 or T[ia][ib] != (k + 1) & 1:
                    continue
                Ta, Tb = T[ia], T[ib]
                if all(Ta[j] == Tb[j] for j in range(len(U)) if wt[j] != wt[ia] and wt[j] != wt[ib]):
                    found.append((a, b))
        expect = [(u + (1,), u + (0,)) for u in words(k - 1)]
        if k % 2 == 1 and k >= 3:
            j = (k - 1) // 2
            expect.append(((1,) + (1, 0) * j, (0,) + (0, 1) * j))
        check(sorted(found) == sorted(expect), "k=%d: star lemma" % k)
        print("k=%d  star pairs=%d  canonical=%d  exceptional=%d  as stated: %s"
              % (k, len(found), 2 ** (k - 1), len(expect) - 2 ** (k - 1), sorted(found) == sorted(expect)))


if __name__ == "__main__":
    maxm = int(sys.argv[1]) if len(sys.argv) > 1 else 6
    maxn = int(sys.argv[2]) if len(sys.argv) > 2 else 4
    print("== Theorem 1.2: extremal admissible systems (SAT)")
    check_theorem_1_2(maxm)
    print("== Theorem 1.1: Shankar's conjecture (SAT)")
    check_theorem_1_1(maxn)
    print("== Proposition 5.1: groupings (SAT)")
    check_groupings(7)
    print("== Lemma 4.1: star lemma (brute force)")
    check_star(9)
    if FAIL:
        print("FAILED:", len(FAIL))
        sys.exit(1)
    print("ALL OK")
