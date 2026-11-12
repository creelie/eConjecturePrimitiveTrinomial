# dumont.jl -- the sets D_(2n-1, j): permutations s of [2n-1] with s(i) <= i for even i and
# s(i) >= i for odd i >= 2(n-j) + 1; a(n, j) is their number, 0 <= j <= n.
#
#  1. a(n, j) by enumeration (backtracking over the positions) for n <= 7, against
#     a(n, 0) = (n!)^2 and a(n, j) = (n-j)! (n-j+1)! G_j(n-j), where G_1 = 1 and
#     G_(j+1)(x) = (x+1) ((x+2) G_j(x+1) - x G_j(x)).
#  2. The same numbers from the transfer recursion
#     u_h -> (h+1) (u_(h-1) + 2(h+1) u_h + (h+1)(h+2) u_(h+1)),  G_j(x) = sum_h u_h x(x-1)...(x-h+1),
#     for n <= 12, and the table for n <= 8.
#  3. a(n+1, j+1) = a(n+1, j) - (n-j)(n-j+1) a(n, j) for n <= 11.
#  4. The explicit polynomials G_2, ..., G_6 and the closed forms for j <= 4.
#  5. First letter: the number of s in D_(2n-1, j) with s(1) = r is ceil(r/2) a(n-1, j) for
#     j >= 1 and r <= 2(n-j), n <= 6.

include(joinpath(@__DIR__, "common.jl"))

"number of permutations in D_(2n-1, j); with first >= 1 only those with s(1) = first"
function brute(n, j; first=0)
    N = 2n - 1; used = falses(N); total = 0
    # positions are filled from N down to 1; an even position i takes a value <= i
    function rec(i)
        if i == 0
            total += 1; return
        end
        lo, hi = iseven(i) ? (1, i) : (i >= 2 * (n - j) + 1 ? (i, N) : (1, N))
        (i == 1 && first > 0) && ((lo, hi) = (max(lo, first), min(hi, first)))
        for v in lo:hi
            used[v] && continue
            used[v] = true; rec(i - 1); used[v] = false
        end
    end
    rec(N)
    total
end

G(j, x) = j == 1 ? big(1) : (x + 1) * ((x + 2) * G(j - 1, x + 1) - x * G(j - 1, x))
formula(n, j) = j == 0 ? factorial(big(n))^2 : factorial(big(n - j)) * factorial(big(n - j + 1)) * G(j, big(n - j))

"coefficients u_0, u_1, ... of G_j in the basis of falling factorials"
function ucoef(j)
    u = BigInt[1]
    for _ in 2:j
        g(h) = 0 <= h < length(u) ? u[h+1] : big(0)
        u = BigInt[(h + 1) * (g(h - 1) + 2 * (h + 1) * g(h) + (h + 1) * (h + 2) * g(h + 1)) for h in 0:length(u)]
    end
    u
end
falling(x, h) = prod(big(x) - i for i in 0:h-1; init=big(1))
transfer(n, j) = j == 0 ? factorial(big(n))^2 :
    factorial(big(n - j)) * factorial(big(n - j + 1)) * sum(u * falling(n - j, h - 1) for (h, u) in enumerate(ucoef(j)))

const TABLE = Dict(1 => [1, 1], 2 => [4, 2, 2], 3 => [36, 12, 8, 8], 4 => [576, 144, 72, 56, 56],
    5 => [14400, 2880, 1152, 720, 608, 608], 6 => [518400, 86400, 28800, 14976, 10656, 9440, 9440],
    7 => [25401600, 3628800, 1036800, 460800, 281088, 217152, 198272, 198272],
    8 => [1625702400, 203212800, 50803200, 19699200, 10483200, 7110144, 5807232, 5410688, 5410688])

println("== enumeration against the formula")
for n in 1:7
    b = [brute(n, j) for j in 0:n]
    check(b == [formula(n, j) for j in 0:n], "a($n, j), j = 0..$n, by enumeration = formula: $b")
end
# the definition, checked directly on all permutations for n <= 5
for n in 1:5
    N = 2n - 1; cnt = zeros(Int, n + 1)
    eachperm(N) do s
        all(s[i] <= i for i in 2:2:N) || return
        for j in 0:n
            all(s[i] >= i for i in 2*(n-j)+1:2:N) && (cnt[j+1] += 1)
        end
    end
    check(cnt == [formula(n, j) for j in 0:n], "a($n, j) by filtering all permutations of [$N]")
end

println("== transfer recursion, table, recurrence")
check(all(transfer(n, j) == formula(n, j) for n in 1:12 for j in 0:n), "transfer recursion = formula, n <= 12")
check(all([formula(n, j) for j in 0:n] == TABLE[n] for n in 1:8), "the table of a(n, j) for n <= 8")
check(all(formula(n + 1, j + 1) == formula(n + 1, j) - (n - j) * (n - j + 1) * formula(n, j) for n in 1:11 for j in 0:n),
      "a(n+1, j+1) = a(n+1, j) - (n-j)(n-j+1) a(n, j), n <= 11")
check(all(all(>=(0), ucoef(j)) for j in 1:12), "the coefficients u_h are nonnegative, j <= 12")

println("== explicit polynomials")
check(all(G(2, x) == 2 * (x + 1) && G(3, x) == 2 * (x + 1) * (3x + 4) && G(4, x) == 8 * (x + 1) * (3x^2 + 9x + 7) &&
          G(5, x) == 8 * (x + 1) * (15x^3 + 75x^2 + 129x + 76) &&
          G(6, x) == 16 * (x + 1) * (45x^4 + 330x^3 + 933x^2 + 1200x + 590) for x in big.(0:12)),
      "G_2, ..., G_6 at x = 0..12 (more points than the degrees)")
check([G(j, big(0)) for j in 1:6] == [1, 2, 8, 56, 608, 9440], "G_j(0) = a(j, j) = 1, 2, 8, 56, 608, 9440")
fa(n) = factorial(big(n))
check(all(formula(n, 1) == fa(n) * fa(n - 1) for n in 1:15) && all(formula(n, 2) == 2 * fa(n - 1)^2 for n in 2:15) &&
      all(formula(n, 3) == (6n - 10) * fa(n - 2)^2 for n in 3:15) &&
      all(formula(n, 4) == 8 * (3n^2 - 15n + 19) * fa(n - 3) * fa(n - 4) * (n - 3) for n in 4:15),
      "closed forms of a(n, 1), a(n, 2), a(n, 3), a(n, 4), n <= 15")

println("== first letter")
for n in 2:6
    ok = all(brute(n, j; first=r) == cld(r, 2) * formula(n - 1, j) for j in 1:n-1 for r in 1:2*(n-j))
    check(ok, "number with s(1) = r is ceil(r/2) a(n-1, j) for 1 <= j < n, r <= 2(n-j), n=$n")
end
check(all(brute(n, 0; first=r) == cld(r, 2) * fa(n - 1)^2 for n in 2:5 for r in 1:2n-1), "j = 0: ceil(r/2) ((n-1)!)^2, n <= 5")

summary()
