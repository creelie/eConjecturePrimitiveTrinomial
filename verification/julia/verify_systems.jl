# verify_systems.jl -- independent checks of Sections 3, 5 and 6 of the paper.
#
# Words of length m are integers 0 .. 2^m - 1 (bit i-1 = i-th letter, 1 = N, 0 = E), and
# B(x, y) is the parity of the number of positions i with x_i = y_i and w(x_{<i}) = w(y_{<i}).
#
#  1. Corollary 1.3: skeletons of [m] correspond to nonnegative +-1 paths of length m (free point
#     or opening of an arc = up step, closing = down step); both are counted for m <= 22 by
#     dynamic programming and equal C(m, floor(m/2)); the map is checked to be a bijection for m <= 14.
#  2. Section 3: for every skeleton system of [m], m <= 9, the sets B_i^0 and B_i^1 obtained by
#     deleting the last letter give G_0 = G_1, and this is the skeleton system of [m-1] predicted by
#     the proof (m a free point, or m joined to the last free point).
#  3. Proposition 5.1 for k <= 4: depth-first search over all groupings of {0,1}^k into singletons
#     and pairs with (G1)-(G3), written from the definition of admissibility; exactly two exist.
#  4. Theorem 1.1, the easy direction: for n <= 7 the C_n families F_M are distinct, have 2^n
#     paths each, and any two of their paths share an even number of edges (counted as edges).
#
# Prints ALL OK when every check passes.

const FAILS = String[]
check(ok, what) = ok || (push!(FAILS, what); println("FAIL: ", what))

function B(x::Int, y::Int, m::Int)
    s = 0; d = 0
    for i in 0:m-1
        xi = (x >> i) & 1; yi = (y >> i) & 1
        (d == 0 && xi == yi) && (s ⊻= 1)
        d += xi - yi
    end
    s
end
wt(x) = count_ones(x)

# skeletons as (arcs, free) with 0-based positions
function skeletons(m)
    out = Tuple{Vector{Tuple{Int,Int}},Vector{Int}}[]
    function rec(pos, stack, arcs, free)
        if pos == m
            isempty(stack) && push!(out, (copy(arcs), copy(free)))
            return
        end
        if length(stack) + 1 <= m - pos - 1
            push!(stack, pos); rec(pos + 1, stack, arcs, free); pop!(stack)
        end
        if !isempty(stack)
            p = pop!(stack); push!(arcs, (p, pos)); rec(pos + 1, stack, arcs, free); pop!(arcs); push!(stack, p)
        else
            push!(free, pos); rec(pos + 1, stack, arcs, free); pop!(free)
        end
    end
    rec(0, Int[], Tuple{Int,Int}[], Int[])
    out
end

function system(m, arcs, free)
    k = length(free); h = length(arcs)
    S = Set{Set{Int}}()
    for a in 0:(1 << k)-1
        C = Set{Int}()
        for o in 0:(1 << h)-1
            x = 0
            for j in 1:k
                ((a >> (j - 1)) & 1 == 1) && (x |= 1 << free[j])
            end
            for t in 1:h
                p, q = arcs[t]
                x |= 1 << (((o >> (t - 1)) & 1 == 1) ? p : q)
            end
            push!(C, x)
        end
        push!(S, C)
    end
    S
end

# ---- 1. skeletons and ballot paths
println("== Corollary 1.3: skeletons and nonnegative paths")
for m in 0:22
    # dp[h+1] = number of prefixes ending with h open arcs; a free point needs h = 0
    dp = zeros(BigInt, m + 2); dp[1] = 1
    ballot = zeros(BigInt, m + 2); ballot[1] = 1
    for _ in 1:m
        nd = zeros(BigInt, m + 2); nb = zeros(BigInt, m + 2)
        for h in 0:m
            dp[h+1] == 0 && ballot[h+1] == 0 && continue
            nd[h+2] += dp[h+1]                 # open an arc
            h > 0 && (nd[h] += dp[h+1])        # close an arc
            h == 0 && (nd[1] += dp[h+1])       # free point
            nb[h+2] += ballot[h+1]             # up step
            h > 0 && (nb[h] += ballot[h+1])    # down step
        end
        dp, ballot = nd, nb
    end
    nsk = dp[1]; nbal = sum(ballot)
    check(nsk == binomial(BigInt(m), m ÷ 2) == nbal, "count of skeletons, m=$m")
    m % 4 == 2 && println("m=$m  skeletons=$nsk  nonnegative paths=$nbal  C(m,floor(m/2))=$(binomial(BigInt(m), m ÷ 2))")
end
for m in 0:14
    images = Set{Vector{Int}}()
    sks = skeletons(m)
    for (arcs, free) in sks
        steps = zeros(Int, m)
        for p in free; steps[p+1] = 1; end
        for (p, q) in arcs; steps[p+1] = 1; steps[q+1] = -1; end
        check(all(cumsum(steps) .>= 0), "image is nonnegative, m=$m")
        push!(images, steps)
    end
    check(length(images) == length(sks) == binomial(m, m ÷ 2), "bijection with nonnegative paths, m=$m")
end
println("skeleton -> nonnegative path is a bijection for m <= 14")

# ---- 2. the induction step on skeleton systems
println("== Section 3: deleting the last letter")
for m in 1:9
    for (arcs, free) in skeletons(m)
        A = system(m, arcs, free)
        last = 1 << (m - 1)
        G0 = Set{Set{Int}}(); G1 = Set{Set{Int}}(); pairs = 0
        for C in A
            B0 = Set(x for x in C if x & last == 0); B1 = Set(x - last for x in C if x & last != 0)
            !isempty(B0) && push!(G0, B0); !isempty(B1) && push!(G1, B1)
            if !isempty(B0) && !isempty(B1)
                push!(G0, B1); push!(G1, B0); pairs += 1
                check(length(B0) == length(B1), "|B_i^0| = |B_i^1|")
            end
        end
        check(G0 == G1, "G_0 = G_1, m=$m")
        # predicted skeleton of [m-1]
        if !isempty(free) && free[end] == m - 1
            pred = system(m - 1, arcs, free[1:end-1]); check(pairs == 0, "no pairs when m is free")
        else
            a = arcs[findfirst(t -> t[2] == m - 1, arcs)]
            others = [t for t in arcs if t != a]
            pred = system(m - 1, others, sort(vcat(free, [a[1]])))
            check(a[1] == maximum(vcat(free, [a[1]])), "m is joined to the last free point")
            check(pairs == length(A), "all classes are pairs")
        end
        check(G0 == pred, "G_0 is the predicted skeleton system, m=$m")
    end
end
println("G_0 = G_1 = predicted skeleton system for every skeleton of [m], m <= 9")

# ---- 3. groupings by depth-first search
println("== Proposition 5.1: groupings by depth-first search")
for k in 0:4
    U = collect(0:(1 << k)-1); m = k + 1
    # the classes of the extended system are sets of words of length k+1 = word + last letter * 2^k
    item(c, e) = c + e * (1 << k)
    function admissible(classes)
        for (i, P) in enumerate(classes)
            length(unique(wt.(P))) == 1 || return false
            all(B(x, y, m) == (m & 1) for x in P, y in P) || return false
            for (j, Q) in enumerate(classes)
                i == j && continue
                length(unique(B(x, y, m) for x in P, y in Q)) == 1 || return false
            end
        end
        true
    end
    sols = Vector{Vector{Tuple{Int,Int}}}()
    function dfs(rest, classes, pairs)
        if isempty(rest)
            admissible(classes) && push!(sols, sort(pairs))
            return
        end
        c = rest[1]; r = rest[2:end]
        # c as a singleton: two classes c0 and c1
        cl = vcat(classes, [[item(c, 0)], [item(c, 1)]])
        admissible(cl) && dfs(r, cl, pairs)
        # c in a pair (a, b) with class a0 u b1
        for d in r
            for (a, b) in ((c, d), (d, c))
                wt(a) == wt(b) + 1 || continue
                cl = vcat(classes, [[item(a, 0), item(b, 1)]])
                admissible(cl) && dfs(filter(!=(d), r), cl, vcat(pairs, [(a, b)]))
            end
        end
    end
    dfs(U, Vector{Vector{Int}}(), Tuple{Int,Int}[])
    canon = sort([(u | (1 << (k - 1)), u) for u in 0:(1 << max(k - 1, 0))-1 if k > 0])
    expect = k == 0 ? [Tuple{Int,Int}[]] : [Tuple{Int,Int}[], canon]
    check(sort(sols) == sort(expect), "groupings, k=$k")
    println("k=$k  groupings found=$(length(sols))  (none, all canonical): $(sort(sols) == sort(expect))")
end

# ---- 4. the families F_M
println("== Theorem 1.1: the families F_M")
function edgeset(x, m)
    E = Set{Tuple{Int,Int,Int}}(); X = 0; Y = 0
    for i in 0:m-1
        s = (x >> i) & 1; push!(E, (X, Y, s)); s == 1 ? (Y += 1) : (X += 1)
    end
    E
end
for n in 1:7
    m = 2n
    fams = Set{Set{Int}}()
    for (arcs, free) in skeletons(m)
        isempty(free) || continue
        F = only(system(m, arcs, free))
        check(length(F) == 2^n && all(wt(x) == n for x in F), "|F_M| = 2^n, n=$n")
        Es = Dict(x => edgeset(x, m) for x in F)
        check(all(iseven(length(intersect(Es[x], Es[y]))) for x in F, y in F), "F_M even, n=$n")
        push!(fams, F)
    end
    check(length(fams) == binomial(2n, n) ÷ (n + 1), "C_n distinct families, n=$n")
    println("n=$n  families=$(length(fams))  C_n=$(binomial(2n, n) ÷ (n + 1))")
end

if isempty(FAILS)
    println("ALL OK")
else
    println("FAILED: ", length(FAILS)); exit(1)
end
