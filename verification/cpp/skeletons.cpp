// skeletons.cpp -- checks of Sections 2, 3 and 6 of the paper.
//
// A word x of length m is a bit mask (bit i-1 holds the i-th letter, 1 = N, 0 = E), and
// B_m(x, y) is the parity of the number of positions i with x_i = y_i and w(x_{<i}) = w(y_{<i}).
// An admissible system is a collection of disjoint nonempty classes of words such that
//   (i)   each class lies in one weight level,
//   (ii)  B_m(x, y) = m (mod 2) for x, y in the same class,
//   (iii) B_m is constant on A x A' for distinct classes A, A';
// it is extremal if the squares of the class sizes add up to 2^m.
//
// Part 1 (Proposition 2.2, Corollary 1.3), for every m <= 10: every skeleton (M, S) of [m] gives
//   classes C_a, a in {0,1}^S, with B_m(x, y) = B_k(a, a') and w(x) = |M| + w(a); the system is
//   admissible and extremal (checked from the definition, pair by pair); different skeletons give
//   different systems; there are C(m, floor(m/2)) skeletons.
// Part 2 (Theorem 1.2), for every m <= 5: an exhaustive search over all admissible systems, built
//   level by level from all partial set partitions of each weight level. It confirms that the
//   squares of the class sizes never add up to more than 2^m (Lemma 2.3) and that the extremal
//   systems are exactly the skeleton systems.
// Part 3 (Theorem 1.1), for every n <= 6: the C_n families F_M of Dyck matchings M of [2n] are
//   pairwise even-intersecting, have 2^n elements each, and are distinct.
//
// Prints ALL OK when every check passes.
#include <algorithm>
#include <cstdio>
#include <cstdlib>
#include <map>
#include <set>
#include <vector>

using std::vector;
typedef vector<unsigned> Class;
typedef vector<Class> System;

static int Bm(unsigned x, unsigned y, int m) {
  int s = 0, d = 0;
  for (int i = 0; i < m; i++) {
    int xi = (x >> i) & 1, yi = (y >> i) & 1;
    if (d == 0 && xi == yi) s ^= 1;
    d += xi - yi;
  }
  return s;
}

static long long binom(int n, int r) {
  long long c = 1;
  for (int i = 1; i <= r; i++) c = c * (n - r + i) / i;
  return c;
}

struct Skeleton {
  vector<std::pair<int, int>> arcs;  // 0-based positions p < q
  vector<int> free;                  // 0-based free points, increasing
};

// all skeletons of [m]: free points only where no arc is open, arcs close in stack order
static void gen(int m, int pos, vector<int>& stack, Skeleton& cur, vector<Skeleton>& out) {
  if (pos == m) {
    if (stack.empty()) out.push_back(cur);
    return;
  }
  if ((int)stack.size() + 1 <= m - pos - 1) {  // open an arc (it must close later)
    stack.push_back(pos);
    gen(m, pos + 1, stack, cur, out);
    stack.pop_back();
  }
  if (!stack.empty()) {  // close the innermost open arc
    int p = stack.back();
    stack.pop_back();
    cur.arcs.push_back({p, pos});
    gen(m, pos + 1, stack, cur, out);
    cur.arcs.pop_back();
    stack.push_back(p);
  } else {  // free point
    cur.free.push_back(pos);
    gen(m, pos + 1, stack, cur, out);
    cur.free.pop_back();
  }
}

// the classes C_a, indexed by a in {0,1}^k (bit j of a = letter at the j-th free point)
static System skeletonSystem(int m, const Skeleton& sk) {
  int k = sk.free.size(), h = sk.arcs.size();
  System sys(1u << k);
  for (unsigned a = 0; a < (1u << k); a++)
    for (unsigned o = 0; o < (1u << h); o++) {
      unsigned x = 0;
      for (int j = 0; j < k; j++)
        if ((a >> j) & 1) x |= 1u << sk.free[j];
      for (int t = 0; t < h; t++)
        x |= 1u << (((o >> t) & 1) ? sk.arcs[t].first : sk.arcs[t].second);
      sys[a].push_back(x);
    }
  (void)m;
  return sys;
}

static bool admissible(const System& sys, int m) {
  for (size_t i = 0; i < sys.size(); i++) {
    if (sys[i].empty()) return false;
    int w = __builtin_popcount(sys[i][0]);
    for (unsigned x : sys[i]) {
      if (__builtin_popcount(x) != w) return false;
      for (unsigned y : sys[i])
        if (Bm(x, y, m) != (m & 1)) return false;
    }
    for (size_t j = 0; j < sys.size(); j++) {
      if (j == i) continue;
      int v = Bm(sys[i][0], sys[j][0], m);
      for (unsigned x : sys[i])
        for (unsigned y : sys[j])
          if (Bm(x, y, m) != v) return false;
    }
  }
  std::set<unsigned> seen;
  for (auto& c : sys)
    for (unsigned x : c)
      if (!seen.insert(x).second) return false;
  return true;
}

static long long sumsq(const System& sys) {
  long long s = 0;
  for (auto& c : sys) s += (long long)c.size() * c.size();
  return s;
}

static System canon(System s) {
  for (auto& c : s) std::sort(c.begin(), c.end());
  std::sort(s.begin(), s.end());
  return s;
}

static int failures = 0;
static void check(bool ok, const char* what) {
  if (!ok) {
    std::printf("FAIL: %s\n", what);
    failures++;
  }
}

// ---------- Part 2: exhaustive search ----------
static int M;                        // word length
static vector<vector<unsigned>> lev; // words of each weight
static vector<vector<System>> cand;  // admissible systems inside each level
static vector<vector<long long>> candsq;
static vector<long long> bestRest;   // max total of the squares available from levels >= l
static long long best;               // largest total of the squares found
static std::set<System> extremal;

// all partial partitions of one level into classes with B = M inside and B constant between
static void levelSystems(const vector<unsigned>& W, size_t i, System& cur, vector<System>& out) {
  if (i == W.size()) {
    out.push_back(cur);
    return;
  }
  unsigned x = W[i];
  levelSystems(W, i + 1, cur, out);  // x unused
  for (size_t c = 0; c <= cur.size(); c++) {
    bool newc = c == cur.size();
    if (!newc) {
      bool ok = true;
      for (unsigned y : cur[c])
        if (Bm(x, y, M) != (M & 1)) ok = false;
      if (!ok) continue;
    }
    // constancy against every other class of this level
    bool ok = true;
    for (size_t d = 0; d < cur.size() && ok; d++) {
      if (d == c) continue;
      int v = Bm(x, cur[d][0], M);
      for (unsigned y : cur[d])
        if (Bm(x, y, M) != v) ok = false;
      if (ok && !newc) {
        // the value on cur[c] x cur[d] is already fixed
        if (Bm(cur[c][0], cur[d][0], M) != v) ok = false;
      }
    }
    if (!ok) continue;
    if (newc) cur.push_back(Class{x});
    else cur[c].push_back(x);
    levelSystems(W, i + 1, cur, out);
    if (newc) cur.pop_back();
    else cur[c].pop_back();
  }
}

static bool crossOK(const System& a, const System& b) {
  for (auto& A : a)
    for (auto& C : b) {
      int v = Bm(A[0], C[0], M);
      for (unsigned x : A)
        for (unsigned y : C)
          if (Bm(x, y, M) != v) return false;
    }
  return true;
}

static void combine(int l, vector<const System*>& chosen, long long sq) {
  if (l > M) {
    best = std::max(best, sq);
    if (sq == (1LL << M)) {
      System all;
      for (auto s : chosen) all.insert(all.end(), s->begin(), s->end());
      extremal.insert(canon(all));
    }
    return;
  }
  for (size_t t = 0; t < cand[l].size(); t++) {
    // candidates are sorted by decreasing total; stop once the target is out of reach
    if (sq + candsq[l][t] + (l < M ? bestRest[l + 1] : 0) < std::max(best, 1LL << M)) break;
    const System& s = cand[l][t];
    bool ok = true;
    for (auto p : chosen)
      if (!crossOK(*p, s)) { ok = false; break; }
    if (!ok) continue;
    chosen.push_back(&s);
    combine(l + 1, chosen, sq + candsq[l][t]);
    chosen.pop_back();
  }
}

int main() {
  // ---------- Part 1 ----------
  for (int m = 0; m <= 10; m++) {
    vector<Skeleton> sks;
    vector<int> st;
    Skeleton cur;
    gen(m, 0, st, cur, sks);
    std::set<System> distinct;
    for (auto& sk : sks) {
      System sys = skeletonSystem(m, sk);
      int k = sk.free.size(), h = sk.arcs.size();
      for (unsigned a = 0; a < sys.size(); a++)
        for (unsigned x : sys[a])
          check(__builtin_popcount(x) == h + __builtin_popcount(a), "weight of a skeleton class");
      for (unsigned a = 0; a < sys.size(); a++)
        for (unsigned b = 0; b < sys.size(); b++) {
          int v = Bm(a, b, k);
          for (unsigned x : sys[a])
            for (unsigned y : sys[b]) check(Bm(x, y, m) == v, "B_m(x,y) = B_k(a,a')");
        }
      check(admissible(sys, m), "skeleton system admissible");
      check(sumsq(sys) == (1LL << m), "skeleton system extremal");
      distinct.insert(canon(sys));
    }
    check((long long)sks.size() == binom(m, m / 2), "number of skeletons = C(m, floor(m/2))");
    check(distinct.size() == sks.size(), "different skeletons give different systems");
    std::printf("m=%2d  skeletons=%4zu  C(m,floor(m/2))=%4lld  distinct systems=%4zu  all admissible and extremal\n",
                m, sks.size(), binom(m, m / 2), distinct.size());
  }

  // ---------- Part 2 ----------
  for (M = 0; M <= 5; M++) {
    lev.assign(M + 1, {});
    for (unsigned x = 0; x < (1u << M); x++) lev[__builtin_popcount(x)].push_back(x);
    cand.assign(M + 1, {});
    candsq.assign(M + 1, {});
    long long nlevel = 0;
    for (int l = 0; l <= M; l++) {
      System cur;
      levelSystems(lev[l], 0, cur, cand[l]);
      std::sort(cand[l].begin(), cand[l].end(),
                [](const System& a, const System& b) { return sumsq(a) > sumsq(b); });
      for (auto& s : cand[l]) candsq[l].push_back(sumsq(s));
      nlevel += cand[l].size();
    }
    bestRest.assign(M + 2, 0);
    for (int l = M; l >= 0; l--) bestRest[l] = bestRest[l + 1] + candsq[l][0];
    best = 0;
    extremal.clear();
    vector<const System*> chosen;
    combine(0, chosen, 0);
    // the skeleton systems of [M]
    vector<Skeleton> sks;
    vector<int> st;
    Skeleton cur;
    gen(M, 0, st, cur, sks);
    std::set<System> skel;
    for (auto& sk : sks) skel.insert(canon(skeletonSystem(M, sk)));
    check(best == (1LL << M), "largest total of squares is 2^m");
    check(extremal == skel, "extremal systems = skeleton systems");
    std::printf("m=%d  level systems=%lld  max sum of squares=%lld (2^m=%lld)  extremal systems=%zu  "
                "all skeleton systems: %s\n",
                M, nlevel, best, 1LL << M, extremal.size(), extremal == skel ? "yes" : "NO");
  }

  // ---------- Part 3 ----------
  for (int n = 1; n <= 6; n++) {
    int m = 2 * n;
    vector<Skeleton> sks;
    vector<int> st;
    Skeleton cur;
    gen(m, 0, st, cur, sks);
    std::set<System> fams;
    long long catalan = binom(2 * n, n) / (n + 1);
    for (auto& sk : sks) {
      if (!sk.free.empty()) continue;
      System s = skeletonSystem(m, sk);
      const Class& F = s[0];
      check(F.size() == (1u << n), "|F_M| = 2^n");
      for (unsigned x : F) {
        check(__builtin_popcount(x) == n, "F_M paths end at (n,n)");
        for (unsigned y : F)
          if (x != y) check(Bm(x, y, m) == 0, "F_M even-intersecting");
      }
      fams.insert(canon(s));
    }
    check((long long)fams.size() == catalan, "C_n distinct families F_M");
    std::printf("n=%d  families F_M=%zu (C_n=%lld), each of size 2^n and even-intersecting\n", n, fams.size(),
                catalan);
  }

  if (failures) {
    std::printf("FAILED (%d)\n", failures);
    return 1;
  }
  std::printf("ALL OK\n");
  return 0;
}
