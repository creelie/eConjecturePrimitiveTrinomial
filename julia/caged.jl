# caged.jl -- caged subsequences of permutations.
#
# For a permutation p of [n] and positions i < j, c[i,j] is the number of k in [i,j] with p(k)
# between p(i) and p(j) (inclusive), and c(p) is the maximum; a pair with c[i,j] = c(p) is maximal.
#
#  1. c(6 7 2 1 5 9 8 3 4) = 3 with exactly 16 maximal pairs.
#  2. Exhaustive search for 5 <= n <= 10: the minimum of c is floor(n/5) + 2; the numbers of
#     permutations attaining it, and of n-cycles among them, are as stated; for n = 9 there are
#     exactly 2, namely 6 7 2 1 5 9 8 3 4 and its complement, and none is a 9-cycle.
#  3. For n = 5k + 4, k <= 5, and every arrangement mu of the middle block: beta(mu) has
#     c = k + 2, exactly 2(k+1)(k+3) maximal pairs, and contains the 4-cycle (1, 3k+3, n, 2k+2).
#  4. The five-term inequality c[i0,j0] + c[1,j0] + c[1,i0] + c[i0,n] + c[j0,n] >= n + 6 when the
#     value 1 stands before the value n, for all permutations with n <= 8.
#  5. n-cycles: for 8 <= n <= 60, n not in {10, 11, 15}, the construction is an n-cycle with
#     c <= floor(n/5) + 3, with equality for n = 5k + 4; the ten explicit n-cycles of the paper
#     (n = 5, ..., 16, n not 9, 14) have c = floor(n/5) + 2.
#  6. For 5 <= n <= 14, by backtracking: no permutation has c < floor(n/5) + 2, and the numbers
#     of extremal permutations, of their orbits under the eight symmetries of the square, and of
#     extremal n-cycles are those of the table.

include(joinpath(@__DIR__, "common.jl"))

function cage(p, i, j)
    lo, hi = minmax(p[i], p[j]); c = 0
    @inbounds for k in i:j
        (lo <= p[k] <= hi) && (c += 1)
    end
    c
end
"(c(p), number of maximal pairs)"
function cval(p)
    n = length(p); best = 0; cnt = 0
    @inbounds for i in 1:n-1, j in i+1:n
        v = cage(p, i, j)
        v > best ? (best = v; cnt = 1) : (v == best && (cnt += 1))
    end
    best, cnt
end
function ncycles(p)
    n = length(p); seen = falses(n); c = 0
    for i in 1:n
        seen[i] && continue
        c += 1; x = i
        while !seen[x]; seen[x] = true; x = p[x]; end
    end
    c
end

println("== the example for n = 9")
const EX = [6, 7, 2, 1, 5, 9, 8, 3, 4]
check(cval(EX) == (3, 16), "c(6 7 2 1 5 9 8 3 4) = 3 with exactly 16 maximal pairs")

println("== exhaustive search")
const EXPECT = Dict(5 => (60, 16), 6 => (140, 30), 7 => (230, 38), 8 => (196, 18), 9 => (2, 0), 10 => (42604, 5178))
for n in 5:10
    target = n ÷ 5 + 2; below = 0; ext = 0; cyc = 0; found = Vector{Int}[]
    eachperm(n) do p
        c = cval(p)[1]
        c < target && (below += 1)
        if c == target
            ext += 1; ncycles(p) == 1 && (cyc += 1)
            n == 9 && push!(found, copy(p))
        end
    end
    check(below == 0, "c(p) >= floor(n/5) + 2 = $target for all permutations, n=$n")
    check((ext, cyc) == EXPECT[n], "n=$n: $ext permutations with c = $target, of which $cyc are n-cycles")
    if n == 9
        check(sort(found) == sort([EX, 10 .- EX]), "n=9: the two extremal permutations are 6 7 2 1 5 9 8 3 4 and its complement")
        check(all(cval(p)[2] == 16 for p in found), "n=9: both have 16 maximal pairs")
    end
end

println("== the permutations beta(mu), n = 5k + 4")
function beta(k, mu)        # mu = arrangement of 1..k
    n = 5k + 4
    vcat(collect(3k+3:4k+3), collect(k+1:-1:1), [2k + 2 + x for x in mu], collect(5k+4:-1:4k+4), collect(k+2:2k+2))
end
for k in 1:5
    n = 5k + 4; ok = true; cnt = 0
    eachperm(k) do mu
        p = beta(k, mu); cnt += 1
        ok &= sort(p) == collect(1:n) && cval(p) == (k + 2, 2 * (k + 1) * (k + 3)) && cval(n + 1 .- p) == (k + 2, 2 * (k + 1) * (k + 3))
        ok &= p[1] == 3k + 3 && p[3k+3] == n && p[n] == 2k + 2 && p[2k+2] == 1
    end
    check(ok, "k=$k, n=$n: all $cnt arrangements give c = $(k+2), $(2*(k+1)*(k+3)) maximal pairs and the 4-cycle")
end
check(beta(1, [1]) == EX, "beta for k = 1 is 6 7 2 1 5 9 8 3 4")

println("== the five-term inequality")
for n in 2:8
    ok = true; eqok = true
    eachperm(n) do p
        i0 = findfirst(==(1), p); j0 = findfirst(==(n), p)
        i0 < j0 || return
        s = cage(p, i0, j0) + cage(p, 1, j0) + cage(p, 1, i0) + cage(p, i0, n) + cage(p, j0, n)
        ok &= s >= n + 6
        eqok &= (s == n + 6) == all(p[n] < p[k] < p[1] for k in i0+1:j0-1)
    end
    check(ok && eqok, "five-term inequality and its equality case, n=$n")
end

println("== n-cycles")
function cycle_construction(n)
    K = n ÷ 5 + 1; m = n - 4K
    m >= 0 || return nothing
    mid = m == 0 ? Int[] : vcat(collect(2K+2:2K+m), 2K + 1)
    b = vcat(collect(2K+m+1:3K+m), collect(K:-1:1), mid, collect(n:-1:3K+m+1), collect(K+1:2K))
    tau = collect(1:n)
    swap(x, y) = (tau[x] = y; tau[y] = x)
    for q in 1:K-1
        isodd(q) ? swap(2K + m + q, 2K + m + q + 1) : swap(n - q, n + 1 - q)
    end
    m >= 1 && swap(2K, 2K + 1)
    [tau[v] for v in b]
end
for n in 8:60
    p = cycle_construction(n)
    if p === nothing
        check(n in (10, 11, 15), "n=$n: the construction does not apply (n in {10, 11, 15})")
        continue
    end
    c = cval(p)[1]
    check(sort(p) == collect(1:n) && ncycles(p) == 1 && c <= n ÷ 5 + 3 && (n % 5 != 4 || c == n ÷ 5 + 3),
          "n=$n: an n-cycle with c = $c <= floor(n/5) + 3 = $(n ÷ 5 + 3)")
end
const CYCLES = [[2, 3, 5, 1, 4], [2, 3, 6, 5, 1, 4], [2, 5, 7, 1, 6, 3, 4], [3, 6, 2, 8, 1, 7, 4, 5],
                [2, 6, 9, 10, 1, 7, 8, 3, 4, 5], [3, 7, 2, 10, 11, 1, 8, 9, 4, 5, 6],
                [4, 3, 8, 2, 11, 12, 1, 9, 10, 5, 6, 7], [5, 4, 9, 3, 12, 13, 6, 11, 1, 2, 10, 7, 8],
                [4, 3, 9, 2, 10, 14, 15, 1, 11, 13, 12, 5, 6, 7, 8],
                [5, 4, 10, 3, 2, 11, 15, 16, 1, 12, 14, 13, 6, 7, 8, 9]]
for p in CYCLES
    n = length(p)
    check(sort(p) == collect(1:n) && ncycles(p) == 1 && cval(p)[1] == n ÷ 5 + 2,
          "the $n-cycle $(join(p, ' ')) has c = $(n ÷ 5 + 2)")
end
p9 = cycle_construction(9)
check(p9 == [7, 6, 2, 1, 4, 9, 8, 3, 5] && cval(p9)[1] == 4, "n=9: the construction gives the 9-cycle 7 6 2 1 4 9 8 3 5 with c = 4")

println("== extremal permutations for 5 <= n <= 14, by backtracking over positions")
"all p in S_n with c(p) <= t; c[i,j] is final once positions i..j are filled"
function below(n, t)
    p = zeros(Int, n); used = falses(n); out = Vector{Vector{Int}}()
    function rec(j)
        j > n && (push!(out, copy(p)); return)
        for v in 1:n
            used[v] && continue
            p[j] = v
            all(cage(p, i, j) <= t for i in 1:j-1) || continue
            used[v] = true; rec(j + 1); used[v] = false
        end
    end
    rec(1); out
end
inverse(p) = (q = similar(p); for i in eachindex(p); q[p[i]] = i; end; q)
symmetries(p) = (n = length(p); r = reverse(p); c = n + 1 .- p; rc = n + 1 .- r;
                 [p, r, c, rc, inverse(p), inverse(r), inverse(c), inverse(rc)])
const TABLE = Dict(5 => (60, 11, 16), 6 => (140, 21, 30), 7 => (230, 33, 38), 8 => (196, 28, 18),
                   9 => (2, 1, 0), 10 => (42604, 5433, 5178), 11 => (64890, 8152, 6706),
                   12 => (50568, 6454, 3856), 13 => (788, 100, 44), 14 => (4, 1, 0))
for n in 5:14
    t = n ÷ 5 + 2
    E = below(n, t); S = Set(E)
    check(isempty(below(n, t - 1)), "n=$n: no permutation has c < $t")
    seen = Set{Vector{Int}}(); orbits = 0; closed = true
    for p in E
        p in seen && continue
        orbits += 1
        for q in symmetries(p); closed &= q in S; push!(seen, q); end
    end
    row = (length(E), orbits, count(p -> ncycles(p) == 1, E))
    check(closed && row == TABLE[n], "n=$n: $(row[1]) extremal permutations in $(row[2]) orbits, $(row[3]) of them n-cycles")
end

summary()
