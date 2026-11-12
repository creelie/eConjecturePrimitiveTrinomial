# eulerian.jl -- Eulerian polynomials of even and odd permutations.
#
#  1. For n <= 8, by enumeration of S_n: the descent and excedance distributions are the Eulerian
#     numbers; Mantaci's identity  sum sgn(pi) t^exc(pi) = (1-t)^(n-1);  the identity of
#     Desarmenien and Foata  sum sgn(pi) t^des(pi) = (1-t)^floor(n/2) A_ceil(n/2)(t);  hence the
#     descent polynomials B_n, C_n and the excedance polynomials P_n, Q_n of the even and odd
#     permutations are (A_n +- D_n)/2 and (A_n +- (1-t)^(n-1))/2.
#  2. 4 P_5 = (2t^2 + 11t + 2)^2 + 15 t^2, so P_5 has no real root.
#  3. Exact numbers of real roots by Sturm sequences (integer arithmetic) for 2 <= n <= 60:
#     B_n, C_n, P_n, Q_n have only real roots except P_3, P_4, Q_4, P_5.
#
# Polynomials are vectors of BigInt coefficients, constant term first.

include(joinpath(@__DIR__, "common.jl"))

trim(p) = (q = copy(p); while !isempty(q) && q[end] == 0; pop!(q); end; q)
deg(p) = length(trim(p)) - 1
function padd(p, q)
    r = zeros(BigInt, max(length(p), length(q)))
    r[1:length(p)] .+= p; r[1:length(q)] .+= q; r
end
pscale(c, p) = BigInt[c * x for x in p]
function pmul(p, q)
    (isempty(p) || isempty(q)) && return BigInt[]
    r = zeros(BigInt, length(p) + length(q) - 1)
    for i in eachindex(p), j in eachindex(q)
        r[i+j-1] += p[i] * q[j]
    end
    r
end
ppow(p, m) = m == 0 ? BigInt[1] : pmul(p, ppow(p, m - 1))
pder(p) = BigInt[(i - 1) * p[i] for i in 2:length(p)]
peq(p, q) = trim(p) == trim(q)

# Eulerian polynomials: A(n,k) = (k+1) A(n-1,k) + (n-k) A(n-1,k-1)
const EUL = Dict{Int,Vector{BigInt}}(0 => BigInt[1], 1 => BigInt[1])
function eulerian(n)
    get!(EUL, n) do
        a = eulerian(n - 1)
        BigInt[(k + 1) * get(a, k + 1, big(0)) + (n - k) * (k == 0 ? big(0) : a[k]) for k in 0:n-1]
    end
end
Dpoly(n) = pmul(ppow(BigInt[1, -1], n ÷ 2), eulerian(n - n ÷ 2))
Epoly(n) = ppow(BigInt[1, -1], n - 1)
half(p) = (@assert all(iseven, p); BigInt[x ÷ 2 for x in p])
fourpolys(n) = (B = half(padd(eulerian(n), Dpoly(n))), C = half(padd(eulerian(n), pscale(-1, Dpoly(n)))),
                P = half(padd(eulerian(n), Epoly(n))), Q = half(padd(eulerian(n), pscale(-1, Epoly(n)))))

println("== Eulerian numbers and the signed identities by enumeration")
# the second recurrence A_n = (1 + (n-1)t) A_(n-1) + t(1-t) A_(n-1)'
check(all(peq(eulerian(n), padd(pmul(BigInt[1, n - 1], eulerian(n - 1)), pmul(BigInt[0, 1, -1], pder(eulerian(n - 1)))))
          for n in 2:60), "the two recurrences for A_n agree, n <= 60")
check(all(sum(eulerian(n)) == factorial(big(n)) for n in 1:60), "A_n(1) = n!, n <= 60")
for n in 1:8
    dd = zeros(BigInt, n); de = zeros(BigInt, n); sd = zeros(BigInt, n); se = zeros(BigInt, n)
    Bn = zeros(BigInt, n); Cn = zeros(BigInt, n); Pn = zeros(BigInt, n); Qn = zeros(BigInt, n)
    eachperm(n) do p
        d = count(i -> p[i] > p[i+1], 1:n-1); e = count(i -> p[i] > i, 1:n); s = permsign(p)
        dd[d+1] += 1; de[e+1] += 1; sd[d+1] += s; se[e+1] += s
        s > 0 ? (Bn[d+1] += 1; Pn[e+1] += 1) : (Cn[d+1] += 1; Qn[e+1] += 1)
    end
    f = fourpolys(n)
    check(peq(dd, eulerian(n)) && peq(de, eulerian(n)), "descents and excedances are Eulerian, n=$n")
    check(peq(se, Epoly(n)), "Mantaci: signed excedance polynomial = (1-t)^(n-1), n=$n")
    check(peq(sd, Dpoly(n)), "Desarmenien-Foata: signed descent polynomial, n=$n")
    check(peq(Bn, f.B) && peq(Cn, f.C) && peq(Pn, f.P) && peq(Qn, f.Q), "B_n, C_n, P_n, Q_n from the identities, n=$n")
end

println("== P_5")
P5 = fourpolys(5).P
check(P5 == BigInt[1, 11, 36, 11, 1], "P_5 = 1 + 11t + 36t^2 + 11t^3 + t^4")
check(peq(pscale(4, P5), padd(pmul(BigInt[2, 11, 2], BigInt[2, 11, 2]), BigInt[0, 0, 15])),
      "4 P_5 = (2t^2 + 11t + 2)^2 + 15 t^2")
check(11^2 - 4 * 34 < 0, "discriminant of u^2 + 11u + 34 is negative")
check(fourpolys(3).P == BigInt[1, 1, 1] && trim(fourpolys(4).P) == BigInt[1, 4, 7] &&
      fourpolys(4).Q == BigInt[0, 7, 4, 1] && trim(fourpolys(5).Q) == BigInt[0, 15, 30, 15],
      "P_3 = 1+t+t^2, P_4 = 1+4t+7t^2, Q_4 = t(7+4t+t^2), Q_5 = 15t(1+t)^2")

println("== Sturm sequences")
content(p) = reduce(gcd, p; init=big(0))
"-(remainder of a by b), multiplied by a positive integer and made primitive"
function negrem(a, b)
    r = copy(a); db = length(b) - 1; lb = b[end]; flip = 1
    while length(r) - 1 >= db && !isempty(r)
        k = length(r) - 1 - db; lr = r[end]
        r = pscale(lb, r)
        for i in 0:db
            r[i+1+k] -= lr * b[i+1]
        end
        lb < 0 && (flip = -flip)
        r = trim(r)
    end
    isempty(r) && return r
    c = content(r)
    BigInt[-flip * x ÷ c for x in r]
end
"(number of distinct real roots, number of distinct complex roots) of a nonzero polynomial"
function rootcounts(p)
    p = trim(p); d = length(p) - 1
    d == 0 && return (0, 0)
    chain = [p, trim(pder(p))]
    while true
        r = negrem(chain[end-1], chain[end])
        isempty(r) && break
        push!(chain, r)
    end
    sp = [sign(q[end]) for q in chain]                              # signs at +infinity
    sm = [sign(q[end]) * (isodd(length(q) - 1) ? -1 : 1) for q in chain]   # signs at -infinity
    var(s) = count(i -> s[i] != s[i+1], 1:length(s)-1)
    (var(sm) - var(sp), d - (length(chain[end]) - 1))
end
realrooted(p) = ((r, c) = rootcounts(p); r == c)
# tests of the root counter
check(rootcounts(BigInt[-6, 11, -6, 1]) == (3, 3), "Sturm test: (t-1)(t-2)(t-3)")
check(rootcounts(BigInt[1, 0, 1]) == (0, 2), "Sturm test: t^2 + 1")
check(rootcounts(pmul(pmul(BigInt[-1, 1], BigInt[-1, 1]), BigInt[1, 0, 1])) == (1, 3), "Sturm test: (t-1)^2 (t^2+1)")
check(rootcounts(pmul(ppow(BigInt[3, 1], 4), BigInt[-2, 0, 1])) == (3, 3), "Sturm test: (t+3)^4 (t^2-2)")
check(rootcounts(BigInt[2, 0, -3, 0, 1]) == (4, 4) && rootcounts(BigInt[2, 0, 3, 0, 1]) == (0, 4), "Sturm test: t^4 -+ 3t^2 + 2")
check(rootcounts(P5) == (0, 4), "P_5 has no real root")

failures = Tuple{Int,Symbol}[]
for n in 2:60
    f = fourpolys(n)
    for name in (:B, :C, :P, :Q)
        realrooted(getfield(f, name)) || push!(failures, (n, name))
    end
    n % 10 == 0 && println("   n <= $n done")
end
println("   polynomials with a non-real root: ", failures)
check(failures == [(3, :P), (4, :P), (4, :Q), (5, :P)],
      "B_n, C_n, P_n, Q_n have only real roots for 2 <= n <= 60 except P_3, P_4, Q_4, P_5")
check(all(all(>=(0), getfield(fourpolys(n), name)) for n in 2:60 for name in (:B, :C, :P, :Q)),
      "all coefficients are nonnegative, so the real roots are <= 0")

summary()
