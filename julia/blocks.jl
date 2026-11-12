# blocks.jl -- monotone paths in Z^d (words over d letters).
#
#  1. Block families: the concatenations of r blocks, the blocks being ab and ba for the pairs
#     of letters {a, b} and cc for the single letters c, pairwise share an even number of edges.
#     With the pairs {0,1}, {2,3}, ... (and the last letter single when d is odd) there are d^r
#     of them; checked for d = 3 (r <= 4), d = 4 (r <= 3), d = 5 (r <= 3), d = 6 (r <= 2) and for
#     other choices of pairs and single letters.
#  2. The weighted inequality  sum_p n_p^2 w^p <= (w_0 + ... + w_(d-1))^m,  n_p the number of words
#     with Parikh vector p, for families of words of length m in which any two share a number of
#     edges congruent to m modulo 2: all such families for (d, m) = (3, 2) and (2, 4), and maximal
#     families obtained greedily from pseudo-random orders for (d, m) = (3, 4), (4, 3), (4, 4);
#     exact rational arithmetic.

include(joinpath(@__DIR__, "common.jl"))

function block_words(pairs, singles, r)
    bl = vcat([[a, b] for (a, b) in pairs], [[b, a] for (a, b) in pairs], [[c, c] for c in singles])
    W = [Int[]]
    for _ in 1:r
        W = [vcat(b, w) for b in bl for w in W]
    end
    W
end

println("== block families")
for (d, rmax) in ((2, 5), (3, 4), (4, 3), (5, 3), (6, 2)), r in 1:rmax
    pairs = [(2j, 2j + 1) for j in 0:d÷2-1]; singles = isodd(d) ? [d - 1] : Int[]
    W = block_words(pairs, singles, r)
    check(length(W) == d^r && all(length(w) == 2r for w in W) && pairwise_parity(W, 0),
          "d=$d, r=$r: $(d^r) words of length $(2r), pairwise even")
end
for (pairs, singles, r) in (([(0, 1)], [2, 3], 3), (Tuple{Int,Int}[], [0, 1, 2], 3), ([(0, 2)], [1], 3), ([(0, 3), (1, 2)], Int[], 3))
    W = block_words(pairs, singles, r)
    check(length(Set(W)) == (2 * length(pairs) + length(singles))^r && pairwise_parity(W, 0),
          "pairs $pairs, single letters $singles, r=$r: $(length(W)) words, pairwise even")
end
# largest class of the cube: words with n letters of each kind, d = 3, n = 2 (r = 3)
let W = block_words([(0, 1)], [2], 3)
    cls = Dict{Vector{Int},Int}()
    for w in W
        p = [count(==(c), w) for c in 0:2]; cls[p] = get(cls, p, 0) + 1
    end
    check(cls[[2, 2, 2]] == 12, "d=3: 12 block words end at (2,2,2)")
    check(sum(v^2 for v in values(cls)) <= 3^6, "d=3, r=3: sum of squares of class sizes <= 3^6")
end

println("== weighted inequality")
allwords(d, m) = [digits(x; base=d, pad=m) for x in 0:d^m-1]
const WEIGHTS = Dict(2 => [[1 // 1, 1 // 1], [1 // 1, 3 // 1], [2 // 5, 7 // 3]],
    3 => [[1 // 1, 1 // 1, 1 // 1], [1 // 1, 2 // 1, 3 // 1], [1 // 2, 1 // 1, 4 // 1]],
    4 => [[1 // 1, 1 // 1, 1 // 1, 1 // 1], [1 // 1, 2 // 1, 3 // 1, 4 // 1], [1 // 3, 1 // 1, 5 // 2, 7 // 1]])
function inequality_holds(F, d, m)
    cls = Dict{Vector{Int},Int}()
    for w in F
        p = [count(==(c), w) for c in 0:d-1]; cls[p] = get(cls, p, 0) + 1
    end
    all(sum(big(n)^2 * prod(big.(om) .^ p) for (p, n) in cls; init=big(0) // 1) <= sum(big.(om))^m for om in WEIGHTS[d])
end
# exhaustive over all families for small cases
for (d, m) in ((3, 2), (2, 4))
    L = allwords(d, m); N = length(L)
    comp = [common(L[i], L[j]) % 2 == m % 2 for i in 1:N, j in 1:N]
    nfam = 0; ok = true
    function rec(start, F)
        nfam += 1
        ok &= inequality_holds([L[i] for i in F], d, m)
        for i in start:N
            all(comp[i, j] for j in F) && rec(i + 1, vcat(F, i))
        end
    end
    rec(1, Int[])
    check(ok, "d=$d, m=$m: the inequality holds for all $nfam families")
end
# maximal families from pseudo-random orders (linear congruential generator, fixed seed)
mutable struct LCG; s::UInt64; end
next!(g::LCG) = (g.s = g.s * 6364136223846793005 + 1442695040888963407; g.s >> 33)
function shuffle!(g::LCG, v)
    for i in length(v):-1:2
        j = Int(next!(g) % i) + 1; v[i], v[j] = v[j], v[i]
    end
    v
end
for (d, m, trials) in ((3, 4, 300), (4, 3, 300), (4, 4, 100))
    L = allwords(d, m); g = LCG(0x2545f4914f6cdd1d); ok = true; largest = 0
    for _ in 1:trials
        shuffle!(g, L); F = Vector{Int}[]
        for w in L
            all(common(w, v) % 2 == m % 2 for v in F) && push!(F, w)
        end
        largest = max(largest, length(F))
        ok &= inequality_holds(F, d, m)
    end
    check(ok, "d=$d, m=$m: the inequality holds for $trials greedy maximal families (largest has $largest words)")
end

summary()
