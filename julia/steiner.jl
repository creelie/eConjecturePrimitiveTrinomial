# steiner.jl -- the 2-Steiner distance matrix of the path P_n.
#
# The matrix is indexed by e_1, f_1, e_2, ..., f_(n-2), e_(n-1), e_i = {i, i+1}, f_i = {i, i+2},
# with entry max(p u q) - min(p u q); chi(x) = det(x - M) = sum a_i x^i has degree 2n - 3.
#
#  1. chi for 3 <= n <= 60 by the division-free method of Samuelson and Berkowitz; for n <= 16
#     also by the Faddeev-LeVerrier recursion; a_0 = -(n-1) (so det M = n-1), trace = 3n-5.
#  2. a_(2n-5) = -(n-1)(n-2)(2n^2+6n-15)/6 for 3 <= n <= 60.
#  3. The largest of |a_0|, ..., |a_(2n-4)| is attained at exactly one index l(n) for
#     6 <= n <= 60, and l(n) = n-1, n, n+1, n+2, n+3, n+4 on 6..15, 16..24, 25..34, 35..43,
#     44..52, 53..60.

include(joinpath(@__DIR__, "common.jl"))

function steiner_matrix(n)
    Bs = Tuple{Int,Int}[]
    for i in 1:n-1
        push!(Bs, (i, i + 1)); i <= n - 2 && push!(Bs, (i, i + 2))
    end
    BigInt[max(p[2], q[2]) - min(p[1], q[1]) for p in Bs, q in Bs]
end

"coefficients of det(x - A) from the highest, without divisions"
function charpoly_berkowitz(A)
    N = size(A, 1); p = BigInt[1]
    for k in 1:N
        M = A[1:k-1, 1:k-1]; R = A[k, 1:k-1]; C = A[1:k-1, k]
        t = BigInt[1, -A[k, k]]
        v = C
        for _ in 1:k-1
            push!(t, -sum(R .* v; init=big(0))); v = M * v
        end
        q = zeros(BigInt, k + 1)
        for i in 1:k+1, j in 1:min(i, length(p))
            q[i] += t[i-j+1] * p[j]
        end
        p = q
    end
    p
end

"the same by Faddeev-LeVerrier (exact integer divisions)"
function charpoly_faddeev(A)
    N = size(A, 1); c = BigInt[1]; Mk = zeros(BigInt, N, N); Id = BigInt[i == j for i in 1:N, j in 1:N]
    for k in 1:N
        Mk = A * Mk + c[end] * Id
        AM = A * Mk
        tr = sum(AM[i, i] for i in 1:N)
        @assert tr % k == 0
        push!(c, -tr ÷ k)
    end
    c
end

println("== characteristic polynomials")
const NMAX = 60
const CP = Dict{Int,Vector{BigInt}}()
for n in 3:NMAX
    CP[n] = reverse(charpoly_berkowitz(steiner_matrix(n)))      # a_0, ..., a_(2n-3)
end
check(all(length(CP[n]) == 2n - 2 && CP[n][end] == 1 for n in 3:NMAX), "degree 2n-3 and leading coefficient 1, 3 <= n <= 60")
check(all(reverse(charpoly_faddeev(steiner_matrix(n))) == CP[n] for n in 3:16), "Berkowitz = Faddeev-LeVerrier, 3 <= n <= 16")
check(all(CP[n][1] == -(n - 1) for n in 3:NMAX), "a_0 = -(n-1), 3 <= n <= 60")
check(all(det_bareiss(steiner_matrix(n)) == n - 1 for n in 3:30), "det M = n-1 by elimination, 3 <= n <= 30")
check(all(CP[n][end-1] == -(3n - 5) for n in 3:NMAX), "a_(2n-4) = -(3n-5), 3 <= n <= 60")
for n in 3:NMAX
    lhs = CP[n][2n-5+1]
    check(6 * lhs == -(n - 1) * (n - 2) * (2n^2 + 6n - 15), "a_(2n-5) = -(n-1)(n-2)(2n^2+6n-15)/6 = $lhs, n=$n")
end

println("== peak of |a_0|, ..., |a_(2n-4)|")
function peak(n)
    a = abs.(CP[n][1:2n-3]); m = maximum(a)
    [i - 1 for i in eachindex(a) if a[i] == m]
end
for n in 6:15
    check(peak(n) == [n - 1], "peak index is n-1 = $(n-1), n=$n")
end
for n in 16:NMAX
    pk = peak(n)
    check(length(pk) == 1 && pk[1] != n - 1, "peak index is $(pk[1]), not n-1 = $(n-1), n=$n")
end
check(all(peak(n) == [n] for n in 16:24), "peak index is n for 16 <= n <= 24")
ell(n) = n <= 15 ? n - 1 : n <= 24 ? n : n <= 34 ? n + 1 : n <= 43 ? n + 2 : n <= 52 ? n + 3 : n + 4
check(all(peak(n) == [ell(n)] for n in 6:NMAX), "unique peak index l(n) as in Theorem steiner-peak, 6 <= n <= 60")
check(abs.(CP[16][15:18]) == parse.(BigInt, ["766504605632", "939602445008", "956326515118", "802497798666"]),
      "n=16: |a_14|, |a_15|, |a_16|, |a_17| = 766504605632, 939602445008, 956326515118, 802497798666")
# unimodality of the absolute values
check(all(begin a = abs.(CP[n][1:2n-3]); k = argmax(a); issorted(a[1:k]) && issorted(a[k:end]; rev=true) end for n in 3:NMAX),
      "|a_0|, ..., |a_(2n-4)| is unimodal, 3 <= n <= 60")

summary()
