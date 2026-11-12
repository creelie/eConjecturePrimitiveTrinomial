# odd_families.jl -- explicit families of paths with pairwise odd, or pairwise even, numbers of
# common edges. Words: 1 = N, 0 = E.
#
#  1. The families of data/best7.txt, data/best8.txt, data/best9.txt (first line = number of
#     paths) consist of 23, 31, 36 distinct paths in the squares of side 7, 8, 9 that pairwise
#     share an odd number of edges (edges are also compared as sets).
#  2. Three rows: for even a, 4 <= a <= 60, the family T_a has 2a - 2 paths from (0,0) to (a,3)
#     (9 paths for a = 6), pairwise with an even number of common edges.
#  3. The square: the family F_n, 1 <= n <= 30, consists of paths from (0,0) to (n,n) that pairwise
#     share an odd number of edges; |F_n| = n^2/2 - 3n/2 for n = 0 (mod 4), n^2/2 - 2n + 3 for
#     n = 2 (mod 4) (n >= 10), |F_n| = |F_(n-1)| for odd n, and |F_n| >= n^2/2 - 3n.

include(joinpath(@__DIR__, "common.jl"))

println("== families found by search")
for (n, k) in ((7, 23), (8, 31), (9, 36))
    L = split(read(joinpath(@__DIR__, "data", "best$n.txt"), String))
    W = [[c == '1' ? 1 : 0 for c in w] for w in L[2:end]]
    check(parse(Int, L[1]) == k && length(W) == k && length(Set(W)) == k, "side $n: $k distinct words")
    check(all(length(w) == 2n && sum(w) == n for w in W), "side $n: paths from (0,0) to ($n,$n)")
    check(pairwise_parity(W, 1), "side $n: pairwise odd numbers of common edges")
    check(all(isodd(common_edges(W[i], W[j])) for i in 1:k for j in i+1:k), "side $n: the same with edges compared as sets")
end

println("== three rows")
"E^i1 N E^(i2-i1) N E^(i3-i2) N E^(a-i3)"
function triple_word(t, a)
    w = Int[]; prev = 0
    for i in t
        append!(w, zeros(Int, i - prev)); push!(w, 1); prev = i
    end
    append!(w, zeros(Int, a - prev)); w
end
function three_rows(a)
    T = vcat([(0, 1, z) for z in 1:2:a-1], [(2, 3, z) for z in 4:2:a-2],
             [(z, a - 1, a) for z in 1:2:a-1], [(z, a - 3, a - 2) for z in 2:2:a-4], [(0, 0, 0), (a, a, a)])
    [triple_word(t, a) for t in unique(T)]
end
for a in 4:2:60
    T = three_rows(a)
    ok = length(T) == (a == 6 ? 9 : 2a - 2) && all(length(w) == a + 3 && sum(w) == 3 for w in T) && pairwise_parity(T, 0)
    (a <= 12 || a % 10 == 0) ? check(ok, "T_$a: $(length(T)) paths to ($a,3), pairwise even") : (ok || check(false, "T_$a"))
end
check(all(a -> (T = three_rows(a); length(T) == (a == 6 ? 9 : 2a - 2) && pairwise_parity(T, 0)), 4:2:60),
      "T_a is an even family of size 2a-2 (9 for a = 6) for every even a, 4 <= a <= 60")
check(all(iseven(common_edges(x, y)) for a in 4:2:16 for x in three_rows(a) for y in three_rows(a) if x != y),
      "the same with edges compared as sets, a <= 16")

println("== the square")
const SMALL = Dict(1 => ["10"], 2 => ["0110", "0011"], 3 => ["010011", "000111", "010110"],
    4 => ["00001111", "00011011", "00111001", "01110100", "10110001", "11100001"],
    5 => ["0000011111", "0000110111", "0000111101", "0001101011", "0011100101",
          "0101001110", "0101111000", "0110101100", "0111011000", "0111110000"])
function square(n)
    n <= 5 && return [[c == '1' ? 1 : 0 for c in w] for w in SMALL[n]]
    isodd(n) && return [vcat(1, w, 0) for w in square(n - 1)]
    T = [1 .- w for w in three_rows(n - 2)]            # paths from (0,0) to (3, n-2)
    F = Vector{Int}[]
    for j in 0:4:n-3, t in T                           # windows [j, j+3]
        push!(F, vcat(zeros(Int, j), 1, t, 1, zeros(Int, n - 3 - j)))
    end
    if n % 4 == 2                                      # one more window of width 1
        j = n - 2
        for k in 0:2:n-2
            push!(F, vcat(zeros(Int, j), 1, ones(Int, k), 0, ones(Int, n - 2 - k), 1, zeros(Int, n - 1 - j)))
        end
    end
    F
end
for n in 1:30
    F = square(n)
    ok = all(length(w) == 2n && sum(w) == n for w in F) && pairwise_parity(F, 1)
    check(ok, "F_$n: $(length(F)) paths in the square of side $n, pairwise odd")
    check(2 * length(F) >= n^2 - 6n, "|F_$n| = $(length(F)) >= n^2/2 - 3n = $(n^2 / 2 - 3n)")
    if n >= 10 && iseven(n)
        check(length(F) == (n % 4 == 0 ? n^2 ÷ 2 - 3n ÷ 2 : n^2 ÷ 2 - 2n + 3), "|F_$n| is given by the formula")
    end
end
check(all(isodd(common_edges(x, y)) for n in 6:14 for x in square(n) for y in square(n) if x != y),
      "F_n pairwise odd with edges compared as sets, 6 <= n <= 14")
check(all(length(square(n)) > (n ÷ 2)^2 for n in 10:2:30), "|F_n| > (n/2)^2 for even n, 10 <= n <= 30")

summary()
