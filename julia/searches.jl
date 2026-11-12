# searches.jl -- the exhaustive searches behind the small values reported in Sections 4 to 7.
#
# A family of paths is a clique in the graph whose vertices are the paths and whose edges join
# two paths sharing a number of edges of the prescribed parity; its largest size is the clique
# number. The clique number is computed exactly by branch and bound with a colouring bound
# (bit-parallel, in the manner of Tomita and of San Segundo), and all cliques of a given size
# are listed by the same procedure with a weaker cut.
#
#  1. Table of M(a,b), M*(a,b) and the box bound for 1 <= b <= a <= 7, a + b <= 12.
#  2. M(a,2) = floor(a/2) + 3 and M*(a,2) = floor((5a-1)/4), floor((5a-2)/4) for 2 <= a <= 22.
#  3. Meven(a,3) for a = 4, ..., 12 even, and M*(a,b) for the rows b = 1, ..., 4 of the table of
#     Section 6.
#  4. Modd(n,n) = 1, 2, 3, 6, 10, 16 for n <= 6.
#  5. Modd(n+1,n) = 2^n for n <= 5; for n <= 4 the odd families of 2^n paths are exactly the
#     C_(n+1) families R_M (2, 5, 14, 42 of them).
#  6. Free endpoints: odd length m <= 9, pairwise odd: at most 2^((m-1)/2).
#  7. tau lies in the column space of A_(a,b) (a, b <= 10, a + b even) exactly in the stated cases.
#  8. Pairs of noncrossing matchings by the number of loops, n <= 6.
#  9. sigma(M) for n <= 6: maxima 1, 2, 2, 3, 3 for n = 2, ..., 6 (sigma = 0 at n = 1) and the distribution for n = 6.
# 10. Even families through (i, i+1): at most 2^(n-1) for n <= 5 and all i.
# 11. The table of 26 boxes in dimensions 2 to 5: number of paths, Madm, Moth, the box bound,
#     R(p) and |E| - |V| + 2.
# 12. Words over d letters with free endpoints: d^floor(m/2) for the stated (d, m).

include(joinpath(@__DIR__, "common.jl"))

# ---------------------------------------------------------------- words and common edges

"all words with p[c] letters c-1 (c = 1..d), in lexicographic order"
function boxwords(p::Vector{Int})
    d = length(p); m = sum(p); out = Vector{Vector{Int8}}(); w = zeros(Int8, m); left = copy(p)
    function rec(i)
        if i > m
            push!(out, copy(w)); return
        end
        for c in 1:d
            if left[c] > 0
                left[c] -= 1; w[i] = c - 1; rec(i + 1); left[c] += 1
            end
        end
    end
    rec(1); out
end

"all words of length m over d letters"
allwords(d, m) = [Int8[(k ÷ d^(i - 1)) % d for i in 1:m] for k in 0:d^m-1]

"prefix states: s[i] encodes the letter counts of w[1..i-1]"
function states(w, d)
    s = Vector{Int}(undef, length(w)); cnt = zeros(Int, d)
    for i in eachindex(w)
        h = 0
        for c in 1:d
            h = h * 64 + cnt[c]
        end
        s[i] = h; cnt[w[i]+1] += 1
    end
    s
end

"number of common edges: positions with the same letter and the same prefix state"
function ncommon(x, sx, y, sy)
    c = 0
    @inbounds for i in eachindex(x)
        (x[i] == y[i] && sx[i] == sy[i]) && (c += 1)
    end
    c
end

# ---------------------------------------------------------------- bit graphs and cliques

struct BitGraph
    n::Int
    W::Int
    adj::Vector{Vector{UInt64}}
end

function BitGraph(n, edge)
    W = cld(n, 64); adj = [zeros(UInt64, W) for _ in 1:n]
    for i in 1:n, j in i+1:n
        if edge(i, j)
            adj[i][(j-1)>>6+1] |= UInt64(1) << ((j - 1) & 63)
            adj[j][(i-1)>>6+1] |= UInt64(1) << ((i - 1) & 63)
        end
    end
    BitGraph(n, W, adj)
end

"graph on the words, joining x and y when their number of common edges is = par (mod 2)"
function pathgraph(words, d, par)
    S = [states(w, d) for w in words]
    BitGraph(length(words), (i, j) -> ncommon(words[i], S[i], words[j], S[j]) % 2 == par)
end

"relabel the vertices by decreasing degree (improves the colouring bound)"
function bydegree(G::BitGraph)
    deg = [sum(count_ones, G.adj[v]) for v in 1:G.n]
    ord = sortperm(deg; rev=true); pos = invperm(ord)
    H = BitGraph(G.n, (i, j) -> begin
        a = ord[i]; b = ord[j]; (G.adj[a][(b-1)>>6+1] >> ((b - 1) & 63)) & 1 == 1
    end)
    H, ord
end

@inline isempty_bits(P) = all(==(0), P)

"colour classes of P greedily; returns vertices and colours in order of increasing colour"
function colour_sort(G::BitGraph, P::Vector{UInt64})
    U = copy(P); Q = similar(P); verts = Int[]; cols = Int[]; k = 0
    while !isempty_bits(U)
        k += 1; copyto!(Q, U)
        while true
            w = findfirst(!=(0), Q)
            w === nothing && break
            v = (w - 1) * 64 + trailing_zeros(Q[w]) + 1
            Q[w] &= Q[w] - 1; U[w] &= ~(UInt64(1) << ((v - 1) & 63))
            @inbounds for t in 1:G.W
                Q[t] &= ~G.adj[v][t]
            end
            push!(verts, v); push!(cols, k)
        end
    end
    verts, cols
end

"clique number of G and one maximum clique"
function maxclique(G0::BitGraph)
    G, ord = bydegree(G0)
    best = Ref(0); bestset = Int[]; cur = Int[]
    function expand(P)
        verts, cols = colour_sort(G, P)
        for i in length(verts):-1:1
            length(cur) + cols[i] <= best[] && return
            v = verts[i]
            push!(cur, v)
            NP = P .& G.adj[v]
            if isempty_bits(NP)
                if length(cur) > best[]
                    best[] = length(cur); bestset = copy(cur)
                end
            else
                expand(NP)
            end
            pop!(cur)
            P[(v-1)>>6+1] &= ~(UInt64(1) << ((v - 1) & 63))
        end
    end
    P = zeros(UInt64, G.W)
    for v in 1:G.n
        P[(v-1)>>6+1] |= UInt64(1) << ((v - 1) & 63)
    end
    expand(P)
    best[], sort(ord[bestset])
end

"all cliques of size k in G (as sorted vertex lists)"
function cliques_of_size(G::BitGraph, k)
    out = Vector{Vector{Int}}(); cur = Int[]
    function expand(P)
        verts, cols = colour_sort(G, P)
        for i in length(verts):-1:1
            length(cur) + cols[i] < k && return
            v = verts[i]
            push!(cur, v)
            if length(cur) == k
                push!(out, sort(cur))
            else
                NP = P .& G.adj[v]
                isempty_bits(NP) || expand(NP)
            end
            pop!(cur)
            P[(v-1)>>6+1] &= ~(UInt64(1) << ((v - 1) & 63))
        end
    end
    P = zeros(UInt64, G.W)
    for v in 1:G.n
        P[(v-1)>>6+1] |= UInt64(1) << ((v - 1) & 63)
    end
    expand(P)
    unique(out)
end

"verify that the vertex list is a clique"
isclique(G, C) = all((G.adj[C[i]][(C[j]-1)>>6+1] >> ((C[j] - 1) & 63)) & 1 == 1 for i in eachindex(C) for j in i+1:length(C))

"largest family of paths in the box p with pairwise common edges = par (mod 2), with a check"
function boxmax(p, par)
    words = boxwords(p); G = pathgraph(words, length(p), par)
    k, C = maxclique(G)
    @assert isclique(G, C) && length(C) == k
    k
end

rectwords(a, b) = boxwords([a, b])          # letter 0 = E, letter 1 = N
M(a, b) = boxmax([a, b], (a + b) % 2)        # matching families
Mstar(a, b) = boxmax([a, b], (a + b + 1) % 2) # mismatched families
boxbound(p) = (m = sum(p); isqrt_floor(big(m)^m, prod(big(c)^c for c in p)))
"floor(sqrt(N/D)) for positive integers"
function isqrt_floor(N, D)
    s = isqrt(N ÷ D)
    while (s + 1)^2 * D <= N
        s += 1
    end
    while s^2 * D > N
        s -= 1
    end
    s
end

# ---------------------------------------------------------------- 1. rectangle table

println("== 1. the table of M(a,b), M*(a,b), floor(beta)")
const RECT = Dict((1,1)=>(2,1,2), (2,1)=>(2,2,2), (2,2)=>(4,2,4), (3,1)=>(2,2,3), (3,2)=>(4,3,5),
    (3,3)=>(8,3,8), (4,1)=>(2,3,3), (4,2)=>(5,4,6), (4,3)=>(8,6,10), (4,4)=>(16,6,16),
    (5,1)=>(2,3,3), (5,2)=>(5,6,8), (5,3)=>(10,7,14), (5,4)=>(16,10,22), (5,5)=>(32,10,32),
    (6,1)=>(2,4,4), (6,2)=>(6,7,9), (6,3)=>(10,10,17), (6,4)=>(21,11,28), (6,5)=>(32,16,44),
    (6,6)=>(64,16,64), (7,1)=>(2,4,4), (7,2)=>(6,8,10), (7,3)=>(12,11,21), (7,4)=>(21,15,36),
    (7,5)=>(42,18,58))
for a in 1:7, b in 1:a
    a + b <= 12 || continue
    t = time()
    v = (M(a, b), Mstar(a, b), Int(boxbound([a, b])))
    check(v == RECT[(a, b)], "(a,b) = ($a,$b): M, M*, floor(beta) = $v  [$(round(time() - t; digits=1)) s]")
end

# ---------------------------------------------------------------- 2. two rows

println("== 2. two rows of cells, 2 <= a <= 22")
for a in 2:22
    want = (a ÷ 2 + 3, isodd(a) ? (5a - 1) ÷ 4 : (5a - 2) ÷ 4)
    check((M(a, 2), Mstar(a, 2)) == want, "M(a,2), M*(a,2) = $want, a = $a")
end

# ---------------------------------------------------------------- 3. three and more rows

println("== 3. three rows, and the table of M*(a,b) for b <= 4")
check([boxmax([a, 3], 0) for a in 4:2:12] == [6, 10, 14, 18, 22], "Meven(a,3) = 6, 10, 14, 18, 22 for a = 4, 6, 8, 10, 12")
const ROWS = Dict(1 => (1:10, [1,2,2,3,3,4,4,5,5,6]),
                  2 => (2:16, [2,3,4,6,7,8,9,11,12,13,14,16,17,18,19]),
                  3 => (3:13, [3,6,7,10,11,14,15,18,18,22,23]),
                  4 => (5:10, [10,11,15,17,20,22]))
for b in 1:4
    rng, want = ROWS[b]
    t = time()
    got = [Mstar(a, b) for a in rng]
    check(got == want, "M*(a,$b) for a in $rng: $got  [$(round(time() - t; digits=1)) s]")
end

# ---------------------------------------------------------------- 4. odd families in squares

println("== 4. odd families in the square")
check([boxmax([n, n], 1) for n in 1:6] == [1, 2, 3, 6, 10, 16], "Modd(n,n) = 1, 2, 3, 6, 10, 16 for n <= 6")

# ---------------------------------------------------------------- 5. the rectangle (n+1) x n

println("== 5. odd families from (0,0) to (n+1,n)")
"noncrossing perfect matchings of 1:2n as vectors of partners"
function ncmatchings(n)
    n == 0 && return [Int[]]
    out = Vector{Vector{Int}}()
    for k in 0:n-1                       # 1 is matched with 2k+2
        for A in ncmatchings(k), B in ncmatchings(n - 1 - k)
            mt = zeros(Int, 2n); mt[1] = 2k + 2; mt[2k+2] = 1
            for i in 1:2k
                mt[i+1] = A[i] + 1
            end
            for i in 1:2(n-1-k)
                mt[2k+2+i] = B[i] + 2k + 2
            end
            push!(out, mt)
        end
    end
    out
end
"F_M: the words x of length 2n (1 = N) with x_i != x_j for every arc {i, j}"
function familyF(mt)
    N = length(mt); out = Vector{Vector{Int8}}()
    for k in 0:2^N-1
        x = Int8[(k >> (i - 1)) & 1 for i in 1:N]
        all(x[i] != x[mt[i]] for i in 1:N) && push!(out, x)
    end
    out
end
check([boxmax([n + 1, n], 1) for n in 1:5] == [2, 4, 8, 16, 32], "Modd(n+1,n) = 2^n for n <= 5")
for n in 1:4
    words = rectwords(n + 1, n); G = pathgraph(words, 2, 1)
    C = cliques_of_size(G, 2^n)
    fams = Set(Set(words[c] for c in cl) for cl in C)
    RM = Set(Set(x[1:end-1] for x in familyF(mt) if x[end] == 1) for mt in ncmatchings(n + 1))
    check(length(C) == length(RM) && fams == RM,
          "n = $n: the odd families of $(2^n) paths to ($(n+1),$n) are the $(length(RM)) families R_M")
end

# ---------------------------------------------------------------- 6. free endpoints, two letters

println("== 6. free endpoints, odd length")
for m in 1:2:9
    words = allwords(2, m); G = pathgraph(words, 2, 1)
    k, _ = maxclique(G)
    check(k == 2^((m - 1) ÷ 2), "length $m, pairwise odd, endpoints free: largest set has $k = 2^$((m-1)÷2) words")
end

# ---------------------------------------------------------------- 7. tau and the column space

println("== 7. tau in the column space of A_(a,b)")
"is the vector t in the column space of the matrix A over F_2 (rows as Bool vectors)"
function incolspace(A::Matrix{Bool}, t::Vector{Bool})
    r = rank_f2(A); r == rank_f2(hcat(A, t))
end
function rank_f2(A::Matrix{Bool})
    B = copy(A); nr, nc = size(B); r = 0
    for c in 1:nc
        piv = findfirst(i -> B[i, c], r+1:nr)
        piv === nothing && continue
        piv += r; r += 1
        B[r, :], B[piv, :] = B[piv, :], B[r, :]
        for i in 1:nr
            (i != r && B[i, c]) && (B[i, :] .⊻= B[r, :])
        end
    end
    r
end
function gridadj(a, b)
    idx(i, j) = (j - 1) * a + i
    A = falses(a * b, a * b)
    for i in 1:a, j in 1:b, (di, dj) in ((1, 0), (-1, 0), (0, 1), (0, -1))
        (1 <= i + di <= a && 1 <= j + dj <= b) && (A[idx(i, j), idx(i + di, j + dj)] = true)
    end
    Matrix{Bool}(A)
end
let ok = true, okrank = true
    for a in 1:10, b in 1:10
        iseven(a + b) || continue
        A = gridadj(a, b)
        t = Bool[(i == 1) ⊻ (j == b) for j in 1:b for i in 1:a]
        predicted = (iseven(a) && iseven(b)) || a == b || (a % 4 == 1 && b % 4 == 1)
        ok &= incolspace(A, t) == predicted
        okrank &= rank_f2(A) == a * b - gcd(a + 1, b + 1) + 1
    end
    check(ok, "a, b <= 10, a + b even: tau in the column space iff a, b even, or a = b, or a = b = 1 (mod 4)")
    check(okrank, "rank A_(a,b) = ab - gcd(a+1,b+1) + 1 for a + b even, a, b <= 10 (Gaussian elimination)")
end

# ---------------------------------------------------------------- 8. loops of pairs of matchings

println("== 8. pairs of matchings by the number of loops")
"components of the union of the matchings (graph on 1:N)"
function components(ms)
    N = length(ms[1]); par = collect(1:N)
    f(x) = (while par[x] != x; par[x] = par[par[x]]; x = par[x]; end; x)
    for mt in ms, i in 1:N
        par[f(i)] = f(mt[i])
    end
    length(Set(f(i) for i in 1:N))
end
const LOOPS = Dict(1 => [1], 2 => [2, 2], 3 => [8, 12, 5], 4 => [42, 84, 56, 14],
                   5 => [262, 640, 580, 240, 42], 6 => [1828, 5236, 5894, 3344, 990, 132])
for n in 1:6
    Ms = ncmatchings(n); cnt = zeros(Int, n)
    for A in Ms, B in Ms
        cnt[components([A, B])] += 1
    end
    check(cnt == LOOPS[n] && cnt[end] == length(Ms) && (n < 2 || cnt[n-1] == 2binomial(2n, n - 2)),
          "n = $n: ordered pairs by the number of loops $(cnt)")
end
let ok = true
    for n in 1:4
        Ms = ncmatchings(n); Fs = [Set(familyF(mt)) for mt in Ms]
        for A in 1:length(Ms), B in 1:length(Ms)
            ok &= length(intersect(Fs[A], Fs[B])) == 2^components([Ms[A], Ms[B]])
        end
    end
    check(ok, "|F_M cap F_M'| = 2^(number of loops) for n <= 4, by listing the families")
end

# ---------------------------------------------------------------- 9. sigma(M)

println("== 9. sigma(M)")
"least size of a subset of F_M contained in no other F_M'"
function sigma(i, Ms, Fs)
    F = collect(Fs[i]); others = [Fs[j] for j in eachindex(Ms) if j != i]; K = length(others)
    W = cld(K, 64); full = zeros(UInt64, W)
    for j in 1:K
        full[(j-1)>>6+1] |= UInt64(1) << ((j - 1) & 63)
    end
    # mask[t]: the other families that do not contain F[t]
    mask = [begin z = zeros(UInt64, W)
                for j in 1:K
                    F[t] in others[j] || (z[(j-1)>>6+1] |= UInt64(1) << ((j - 1) & 63))
                end; z end for t in eachindex(F)]
    K == 0 && return 0
    N = length(F)
    for t in 1:N
        mask[t] == full && return 1
    end
    for t in 1:N, u in t+1:N
        (mask[t] .| mask[u]) == full && return 2
    end
    for t in 1:N, u in t+1:N
        mu = mask[t] .| mask[u]
        for v in u+1:N
            (mu .| mask[v]) == full && return 3
        end
    end
    error("sigma > 3")
end
let maxima = Int[], dist6 = Dict{Int,Int}()
    for n in 1:6
        Ms = ncmatchings(n); Fs = [Set(familyF(mt)) for mt in Ms]
        sig = [sigma(i, Ms, Fs) for i in eachindex(Ms)]
        push!(maxima, maximum(sig))
        n == 6 && for s in sig; dist6[s] = get(dist6, s, 0) + 1; end
    end
    check(maxima == [0, 1, 2, 2, 3, 3], "max sigma(M) = 0, 1, 2, 2, 3, 3 for n = 1, ..., 6 (one family at n = 1)")
    check(dist6 == Dict(1 => 6, 2 => 112, 3 => 14), "n = 6: sigma = 1, 2, 3 for 6, 112, 14 matchings")
end

# ---------------------------------------------------------------- 10. through a point off the diagonal

println("== 10. even families through (i, i+1)")
let ok = true
    for n in 1:5, i in 0:n-1
        words = [w for w in rectwords(n, n) if sum(w[1:2i+1]) == i + 1]   # at (i, i+1) after 2i+1 steps
        G = pathgraph(words, 2, 0)
        k, _ = maxclique(G)
        ok &= k == 2^(n - 1)
    end
    check(ok, "for n <= 5 and 0 <= i <= n-1 the largest even family through (i, i+1) has 2^(n-1) paths")
end

# ---------------------------------------------------------------- 11. boxes

println("== 11. the table of boxes")
const BOXES = [
    ([1,1], 2, 2, 2, 1, 0, 2), ([2,2], 6, 4, 4, 2, 2, 5), ([3,3], 20, 8, 8, 3, 6, 10),
    ([4,2], 15, 5, 6, 4, 8, 9), ([5,1], 6, 2, 3, 3, 4, 6), ([6,2], 28, 6, 9, 7, 12, 13),
    ([1,1,1], 6, 2, 5, 3, 4, 6), ([2,1,1], 12, 5, 8, 3, 8, 10), ([2,2,1], 30, 5, 13, 7, 14, 17),
    ([3,1,1], 20, 5, 10, 6, 12, 14), ([2,2,2], 90, 15, 27, 7, 22, 29), ([3,2,1], 60, 12, 20, 7, 24, 24),
    ([4,1,1], 30, 7, 13, 6, 16, 18), ([3,3,1], 140, 12, 33, 13, 28, 34), ([3,2,2], 210, 15, 43, 16, 38, 41),
    ([4,2,1], 105, 12, 28, 11, 31, 31), ([5,1,1], 42, 7, 16, 9, 20, 22), ([4,2,2], 420, 30, 64, 16, 50, 53),
    ([3,3,2], 560, 37, 75, 16, 54, 58), ([4,3,1], 280, 26, 49, 13, 44, 44),
    ([1,1,1,1], 24, 8, 16, 3, 12, 18), ([2,1,1,1], 60, 8, 27, 10, 28, 30), ([2,2,1,1], 180, 24, 54, 10, 42, 50),
    ([3,1,1,1], 120, 14, 41, 10, 36, 42), ([1,1,1,1,1], 120, 8, 55, 15, 36, 50),
    ([2,1,1,1,1], 360, 31, 108, 15, 76, 82)]
for (p, npaths, madm, bound, moth, R, cyc) in BOXES
    t = time(); m = sum(p); d = length(p)
    words = boxwords(p); S = [states(w, d) for w in words]
    B = Bool[ncommon(words[i], S[i], words[j], S[j]) % 2 == 1 for i in eachindex(words), j in eachindex(words)]
    V = prod(c + 1 for c in p); E = sum(p[c] * prod(p[c2] + 1 for c2 in 1:d if c2 != c) for c in 1:d)
    got = (length(words), boxmax(p, m % 2), Int(boxbound(p)), boxmax(p, (m + 1) % 2), rank_f2(B), E - V + 2)
    check(got == (npaths, madm, bound, moth, R, cyc),
          "box $p: paths, Madm, bound, Moth, R(p), |E|-|V|+2 = $got  [$(round(time() - t; digits=1)) s]")
end

# ---------------------------------------------------------------- 12. free endpoints, d letters

println("== 12. words over d letters with free endpoints")
for (d, mmax) in ((2, 8), (3, 5), (4, 4), (5, 3)), m in 1:mmax
    words = allwords(d, m); G = pathgraph(words, d, m % 2)
    k, _ = maxclique(G)
    check(k == d^(m ÷ 2), "d = $d, m = $m: largest set with pairwise common edges = m (mod 2) has $k = $d^$(m ÷ 2) words")
end

summary()
