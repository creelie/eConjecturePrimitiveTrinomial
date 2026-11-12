# regions.jl -- the families F_M of the noncrossing perfect matchings M of [2n], n <= 6.
#
# A word is an integer below 2^(2n) (bit i-1 = i-th letter, 1 = N, 0 = E); F_M consists of the
# 2^n words that have different letters at the two ends of every arc of M.
#
#  1. Heights: the number of words of F_M at height h after i letters is C(d, (d+h)/2) 2^(n-d),
#     d = d_M(i) the number of arcs open at i.
#  2. Regions: F_M lies in the strip |height| <= s, and in the half strip height >= -s, exactly
#     when the Dyck word of M has height <= s; the numbers of such M are the numbers of Dyck
#     paths of bounded height. Random regions L <= height <= U: F_M lies inside iff
#     d_M <= min(U, -L).
#  3. A forbidden point: the number of M such that no word of F_M passes through a given
#     point is given by the formula with ballot numbers.
#  4. Dyck paths: the 2^(n-1) words N u_1 ... u_(n-1) E, u_t in {NE, EN}, are Dyck paths that
#     pairwise share an even number of edges (n <= 8); for n <= 6 the largest such family of
#     Dyck paths has 2^(n-1) members and is unique (exact clique search).
#  5. Intersections: |F_M1 n F_M2| = 2^c, c the number of components of M1 u M2 (loops of the
#     meander system), for all pairs; the numbers of pairs with c loops; all triples for n <= 4;
#     the intersection of all families is the two staircases.
#  6. The Gram matrix (2^c(M,M')) is nonsingular over Q and its determinant is
#     prod (i+1)^a(n,i), a(n,i) = C(2n,n-i) - 2 C(2n,n-i-1) + C(2n,n-i-2).

include(joinpath(@__DIR__, "common.jl"))

binom(a, k) = (0 <= k <= a) ? binomial(big(a), big(k)) : big(0)
catalan(n) = binom(2n, n) ÷ (n + 1)
"number of nonnegative +-1 walks of length i from 0 to g"
ballot(i, g) = (g < 0 || g > i || isodd(i - g)) ? big(0) : binom(i, (i - g) ÷ 2) - binom(i, (i - g) ÷ 2 - 1)

"noncrossing perfect matchings of 0..2n-1 as lists of arcs (p, q), p < q"
function matchings(n)
    function rec(lo, hi)
        lo > hi && return [Tuple{Int,Int}[]]
        out = Vector{Tuple{Int,Int}}[]
        for q in lo+1:2:hi, a in rec(lo + 1, q - 1), b in rec(q + 1, hi)
            push!(out, vcat([(lo, q)], a, b))
        end
        out
    end
    rec(0, 2n - 1)
end
function family(M)
    F = Int[]
    for o in 0:(1<<length(M))-1
        x = 0
        for (t, (p, q)) in enumerate(M)
            x |= 1 << (((o >> (t - 1)) & 1 == 1) ? p : q)
        end
        push!(F, x)
    end
    sort(F)
end
heights(x, m) = cumsum([((x >> i) & 1 == 1) ? 1 : -1 for i in 0:m-1])        # h_1, ..., h_m
dM(M, m) = [count(a -> a[1] < i <= a[2], M) for i in 1:m]                   # d_M(1), ..., d_M(m)
function components(Ms, m)
    par = collect(1:m)
    find(a) = (while par[a] != a; par[a] = par[par[a]]; a = par[a]; end; a)
    for M in Ms, (p, q) in M
        par[find(p + 1)] = find(q + 1)
    end
    length(Set(find(a) for a in 1:m))
end
function Bpar(x, y, m)
    s = 0; d = 0
    for i in 0:m-1
        xi = (x >> i) & 1; yi = (y >> i) & 1
        (d == 0 && xi == yi) && (s ⊻= 1)
        d += xi - yi
    end
    s
end

const NMAX = 6
const MS = Dict(n => matchings(n) for n in 1:NMAX)
const FS = Dict(n => [family(M) for M in MS[n]] for n in 1:NMAX)
check(all(length(MS[n]) == catalan(n) && length(Set(FS[n])) == catalan(n) for n in 1:NMAX), "C_n matchings and C_n distinct families, n <= $NMAX")

println("== heights")
for n in 1:NMAX
    ok = true
    for (M, F) in zip(MS[n], FS[n])
        d = dM(M, 2n); H = [heights(x, 2n) for x in F]
        for i in 1:2n, h in -n:n
            cnt = count(hh -> hh[i] == h, H)
            pred = (abs(h) <= d[i] && iseven(d[i] + h)) ? binom(d[i], (d[i] + h) ÷ 2) * big(2)^(n - d[i]) : 0
            ok &= cnt == pred
        end
    end
    check(ok, "number of words of F_M at a given height, n=$n")
end

println("== regions")
const TABLE = Dict(1 => [1, 1, 1, 1, 1, 1], 2 => [1, 2, 4, 8, 16, 32], 3 => [1, 2, 5, 13, 34, 89],
                   4 => [1, 2, 5, 14, 41, 122], 5 => [1, 2, 5, 14, 42, 131])
for s in 1:5
    ok = true; counts = Int[]
    for n in 1:NMAX
        inside = 0
        for (M, F) in zip(MS[n], FS[n])
            strip = all(x -> all(h -> abs(h) <= s, heights(x, 2n)), F)
            halfstrip = all(x -> all(h -> h >= -s, heights(x, 2n)), F)
            dyck = maximum(dM(M, 2n)) <= s
            ok &= strip == dyck && halfstrip == dyck
            inside += strip
        end
        push!(counts, inside)
    end
    check(ok && counts == TABLE[s], "strip of half width $s: the families inside are those of height <= $s; counts $counts")
end
mutable struct LCG; s::UInt64; end
next!(g::LCG) = (g.s = g.s * 6364136223846793005 + 1442695040888963407; g.s >> 33)
let g = LCG(0x9e3779b97f4a7c15), ok = true, trials = 0
    for n in 2:5, _ in 1:60
        U = [Int(next!(g) % 4) for _ in 1:2n]; L = [-Int(next!(g) % 4) for _ in 1:2n]
        V = min.(U, -L)
        for (M, F) in zip(MS[n], FS[n])
            inside = all(x -> (h = heights(x, 2n); all(L .<= h .<= U)), F)
            ok &= inside == all(dM(M, 2n) .<= V)
        end
        trials += 1
    end
    check(ok, "F_M lies in the region L <= height <= U iff d_M <= min(U, -L) ($trials random regions, n <= 5)")
end

println("== a forbidden point")
for n in 1:NMAX
    ok = true
    for i in 1:2n-1, h in -min(i, 2n - i):2:min(i, 2n - i)
        avoiding = count(F -> all(x -> heights(x, 2n)[i] != h, F), FS[n])
        pred = abs(h) >= 2 ? catalan(n) - sum(ballot(i, g) * ballot(2n - i, g) for g in abs(h):n) : 0
        ok &= avoiding == pred
    end
    check(ok, "number of families avoiding a point, all points, n=$n")
end

println("== Dyck paths")
isdyck(x, m) = all(>=(0), heights(x, m))
"sets of vertices 0..191 as bit masks"
struct Bits
    a::UInt64; b::UInt64; c::UInt64
end
Base.:&(x::Bits, y::Bits) = Bits(x.a & y.a, x.b & y.b, x.c & y.c)
Base.:|(x::Bits, y::Bits) = Bits(x.a | y.a, x.b | y.b, x.c | y.c)
without(x::Bits, y::Bits) = Bits(x.a & ~y.a, x.b & ~y.b, x.c & ~y.c)
isnone(x::Bits) = (x.a | x.b | x.c) == 0
size_of(x::Bits) = count_ones(x.a) + count_ones(x.b) + count_ones(x.c)
bit(v) = v < 64 ? Bits(UInt64(1) << v, 0, 0) : v < 128 ? Bits(0, UInt64(1) << (v - 64), 0) : Bits(0, 0, UInt64(1) << (v - 128))
first_of(x::Bits) = x.a != 0 ? trailing_zeros(x.a) : x.b != 0 ? 64 + trailing_zeros(x.b) : 128 + trailing_zeros(x.c)

"(clique number, number of maximum cliques) of the graph with adjacency sets `adj`"
function maxcliques(adj::Vector{Bits})
    best = 0; nbest = 0
    function expand(size, P::Bits)
        if isnone(P)
            size > best ? (best = size; nbest = 1) : (size == best && (nbest += 1))
            return
        end
        # greedy colouring bound
        Q = P; colours = 0
        while !isnone(Q)
            colours += 1; R = Q
            while !isnone(R)
                v = first_of(R); R = without(without(R, bit(v)), adj[v+1]); Q = without(Q, bit(v))
            end
        end
        size + colours < best && return
        Q = P
        while !isnone(Q)
            size + size_of(Q) < best && return
            v = first_of(Q); Q = without(Q, bit(v))
            expand(size + 1, Q & adj[v+1])
        end
    end
    expand(0, reduce(|, (bit(v) for v in 0:length(adj)-1)))
    best, nbest
end
for n in 1:8
    F = [1 | (sum(((o >> (t - 1)) & 1 == 1 ? 1 : 2) << (2t - 1) for t in 1:n-1; init=0)) for o in 0:(1<<(n-1))-1]
    ok = length(Set(F)) == 2^(n - 1) && all(x -> count_ones(x) == n && isdyck(x, 2n), F) &&
         all(Bpar(x, y, 2n) == 0 for x in F for y in F if x != y)
    check(ok, "N u_1 ... u_(n-1) E: 2^(n-1) = $(2^(n-1)) Dyck paths, pairwise even, n=$n")
end
for n in 1:6
    V = [x for x in 0:(1<<(2n))-1 if count_ones(x) == n && isdyck(x, 2n)]
    adj = [reduce(|, (bit(j - 1) for j in eachindex(V) if j != i && Bpar(V[i], V[j], 2n) == 0); init=Bits(0, 0, 0)) for i in eachindex(V)]
    w, cnt = maxcliques(adj)
    check(length(V) == catalan(n) && w == 2^(n - 1) && cnt == 1,
          "Dyck paths, n=$n: the largest even family has $w = 2^(n-1) paths and there is $cnt such family")
end

println("== intersections")
const LOOPS = Dict(1 => [1], 2 => [2, 2], 3 => [8, 12, 5], 4 => [42, 84, 56, 14], 5 => [262, 640, 580, 240, 42],
                   6 => [1828, 5236, 5894, 3344, 990, 132])
const GRAM = Dict{Int,Matrix{BigInt}}()
for n in 1:NMAX
    Ms = MS[n]; Fs = [Set(F) for F in FS[n]]; N = length(Ms)
    G = zeros(BigInt, N, N); dist = zeros(Int, n); ok = true
    for i in 1:N, j in 1:N
        c = components([Ms[i], Ms[j]], 2n)
        ok &= length(intersect(Fs[i], Fs[j])) == 2^c
        G[i, j] = big(2)^c; dist[c] += 1
    end
    GRAM[n] = G
    check(ok, "|F_M n F_M'| = 2^c for all $(N^2) ordered pairs, n=$n")
    check(dist == LOOPS[n], "pairs by number of loops: $dist, n=$n")
    n >= 2 && check(dist[n-1] == 2 * binom(2n, n - 2), "pairs sharing 2^(n-1) paths: 2 C(2n, n-2) = $(dist[n-1]), n=$n")
    stair = Set([sum(1 << i for i in 0:2:2n-1), sum(1 << i for i in 1:2:2n-1)])
    check(intersect(Fs...) == stair && (n == 1 || components(Ms, 2n) == 1), "the intersection of all families is the two staircases, n=$n")
    cnt = Dict{Int,Int}()
    for F in Fs, x in F
        cnt[x] = get(cnt, x, 0) + 1
    end
    check(sum(v^2 for v in values(cnt)) == sum(G), "sum_p f(p)^2 = sum of 2^c = $(sum(G)), n=$n")
end
for n in 1:4
    Ms = MS[n]; Fs = [Set(F) for F in FS[n]]; N = length(Ms)
    check(all(length(intersect(Fs[i], Fs[j], Fs[k])) == 2^components([Ms[i], Ms[j], Ms[k]], 2n) for i in 1:N, j in 1:N, k in 1:N),
          "|F_M1 n F_M2 n F_M3| = 2^c for all triples, n=$n")
end

println("== Gram matrix")
a_(n, i) = binom(2n, n - i) - 2 * binom(2n, n - i - 1) + binom(2n, n - i - 2)
for n in 1:NMAX
    d = det_bareiss(GRAM[n])
    pred = prod(big(i + 1)^a_(n, i) for i in 1:n)
    check(d != 0 && d == pred, "det of the Gram matrix is nonzero and equals prod (i+1)^a(n,i) ($(ndigits(d)) digits), n=$n")
end
check(det_rational(GRAM[4]) == det_bareiss(GRAM[4]) && det_bareiss(GRAM[3]) == 5184, "determinant by rational elimination agrees (n = 4); det G_3 = 5184")

summary()
