# canon.jl -- descent polynomials of 321-avoiding lattice words, and lattice words on four letters.
#
#  1. The descent polynomials Q_k(x) = sum x^des(w) over the 321-avoiding words of L_3^k, by a
#     transfer over prefixes (state: letter counts, phase, last letter), for k <= KMAX; the values
#     Q_k(1) agree with the list of hankel.jl, Q_3(x) = 1 + 10x + 16x^2 + 6x^3, and every Q_k(x)
#     has a log-concave coefficient sequence.
#  2. The number of nonreal zeros of Q_k(x) for k <= 45, by exact Sturm sequences (primitive
#     pseudo-remainders over the integers): 0 for k <= 10, then 2, 4, 6, 8 on the blocks
#     11-19, 20-29, 30-39, 40-45.
#  3. Lattice words on four letters for k <= 6: for every word the set M(w) of patterns of S_4 it
#     contains, by a transfer that keeps the set of subsequences with distinct letters; the number
#     of distinct sets M(w), the counts for single patterns (Table of Section 9), the classes of
#     forbidden sets and their sequences; on three letters the same procedure gives the six
#     sequences of Shankar's classification.
#
# KMAX defaults to 110 (about ten minutes); `julia canon.jl 60` runs a shorter check.

include(joinpath(@__DIR__, "common.jl"))
using Base.Iterators: product

const KMAX = isempty(ARGS) ? 110 : parse(Int, ARGS[1])
const QLIST = parse.(BigInt, split("""1 1 5 33 234 1706 12618 94157 706878 5330403 40332881 306023196
2327290506 17734226120 135376087792 1035065812309 7925664456804 60771825678389 466587436417569
3586731522598141 27604168028694252 212685629040409758 1640473066548280308 12666272996480868428
97894846717057492194"""))

"descent polynomial of the 321-avoiding words of L_3^k (coefficient vector, index 1 = x^0)"
function qpoly(k)
    # phase 0: no 3 yet; 1: a 3 has occurred; 2: a 3 and later a 2 (no further 1 allowed)
    cur = Dict{NTuple{5,Int},Vector{BigInt}}((1, 0, 0, 0, 1) => BigInt[1])
    for n in 2:3k
        nxt = Dict{NTuple{5,Int},Vector{BigInt}}()
        for ((a, b, c, ph, l), p) in cur
            for (x, ok, nph) in ((1, a < k && ph < 2, ph), (2, b < a, ph >= 1 ? 2 : 0), (3, c < b, max(ph, 1)))
                ok || continue
                key = x == 1 ? (a+1, b, c, nph, 1) : x == 2 ? (a, b+1, c, nph, 2) : (a, b, c+1, nph, 3)
                d = l > x ? 1 : 0
                q = get!(() -> BigInt[], nxt, key)
                while length(q) < length(p) + d; push!(q, BigInt(0)); end
                for i in eachindex(p); Base.GMP.MPZ.add!(q[i+d], p[i]); end
            end
        end
        cur = nxt
    end
    tot = BigInt[]
    for p in values(cur)
        while length(tot) < length(p); push!(tot, BigInt(0)); end
        for i in eachindex(p); tot[i] += p[i]; end
    end
    while length(tot) > 1 && tot[end] == 0; pop!(tot); end
    tot
end

# --- exact Sturm sequences over the integers -------------------------------------------------
trimp(p) = (q = copy(p); while length(q) > 1 && q[end] == 0; pop!(q); end; q)
deriv(p) = [i * p[i+1] for i in 1:length(p)-1]
function prim(p)
    g = foldl(gcd, p; init=BigInt(0)); g == 0 ? p : p .÷ g
end
function sturm_real_roots(p)
    length(trimp(p)) == 1 && return 0
    # Sturm chain with signs: p0 = p, p1 = p', p_{i+1} = -rem(p_{i-1}, p_i) up to positive factors
    chain = [prim(trimp(p)), prim(trimp(deriv(p)))]
    while length(chain[end]) > 1
        f, g = chain[end-1], chain[end]
        dg = length(g) - 1; df = length(f) - 1
        lg = g[end]
        s = lg > 0 || iseven(df - dg + 1) ? 1 : -1      # sign of lg^(df-dg+1)
        r = BigInt.(f)
        while length(r) - 1 >= dg && any(!iszero, r)
            dr = length(r) - 1; lr = r[end]
            r = lg .* r
            for i in 0:dg; r[dr-dg+i+1] -= lr * g[i+1]; end
            pop!(r); r = trimp(isempty(r) ? BigInt[0] : r)
        end
        all(iszero, r) && break
        push!(chain, prim(-s .* r))
    end
    @assert length(chain[end]) == 1 "polynomial is not squarefree"
    var(vals) = (v = filter(!iszero, vals); count(i -> sign(v[i]) != sign(v[i+1]), 1:length(v)-1))
    atinf(q, neg) = (d = length(q) - 1; neg && isodd(d) ? -q[end] : q[end])
    var([atinf(q, true) for q in chain]) - var([atinf(q, false) for q in chain])
end

println("== descent polynomials of Q_k, k <= $KMAX")
t = @elapsed P = [qpoly(k) for k in 1:KMAX]
println("   computed in ", round(t; digits=1), " s")
check(all(sum(P[k]) == QLIST[k+1] for k in 1:min(KMAX, 24)), "Q_k(1) agrees with the list of hankel.jl for k <= 24")
check(P[3] == BigInt[1, 10, 16, 6], "Q_3(x) = 1 + 10x + 16x^2 + 6x^3")
check(all(all(p[i]^2 >= p[i-1] * p[i+1] for i in 2:length(p)-1) for p in P),
      "the coefficients of Q_k(x) are log-concave for every k <= $KMAX")

println("== nonreal zeros of Q_k(x), k <= 45")
expect(k) = k <= 10 ? 0 : k <= 19 ? 2 : k <= 29 ? 4 : k <= 39 ? 6 : 8
nr = [length(P[k]) - 1 - sturm_real_roots(P[k]) for k in 1:min(45, KMAX)]
check(nr == [expect(k) for k in 1:min(45, KMAX)], "number of nonreal zeros: $(nr)")

println("== lattice words on four letters")
function setup(n)
    seqs = Vector{Vector{Int}}()
    for L in 1:n, s in product(fill(1:n, L)...)
        v = collect(s); allunique(v) && push!(seqs, v)
    end
    idx = Dict(s => i for (i, s) in enumerate(seqs))
    full = [s for s in seqs if length(s) == n]
    trans = [Tuple{Int,Int}[] for _ in 1:n]
    for x in 1:n, s in seqs
        length(s) < n && !(x in s) && push!(trans[x], (idx[s] - 1, idx[vcat(s, x)] - 1))
    end
    seqs, idx, full, trans
end
"multiset of the pattern sets M(w), w in L_n^k, as a dictionary bitmask => number of words"
function pattern_sets(n, k, idx, full, trans)
    cur = Dict{Tuple{NTuple{4,Int},UInt64},Int}((ntuple(i -> i == 1 ? 1 : 0, 4), UInt64(1) << (idx[[1]] - 1)) => 1)
    for step in 2:n*k
        nxt = Dict{Tuple{NTuple{4,Int},UInt64},Int}()
        for ((cnt, m), v) in cur, x in 1:n
            (cnt[x] < k && (x == 1 || cnt[x] < cnt[x-1])) || continue
            nm = m | (UInt64(1) << (idx[[x]] - 1))
            for (s, d) in trans[x]
                (m >> s) & 1 == 1 && (nm |= UInt64(1) << d)
            end
            key = (ntuple(i -> i == x ? cnt[i] + 1 : cnt[i], 4), nm)
            nxt[key] = get(nxt, key, 0) + v
        end
        cur = nxt
    end
    res = Dict{UInt32,Int}()
    for ((cnt, m), v) in cur
        M = UInt32(0)
        for (j, s) in enumerate(full)
            (m >> (idx[s] - 1)) & 1 == 1 && (M |= UInt32(1) << (j - 1))
        end
        res[M] = get(res, M, 0) + v
    end
    res
end
function classify(n, K)
    seqs, idx, full, trans = setup(n)
    R = [pattern_sets(n, k, idx, full, trans) for k in 1:K]
    single = Dict(join(string.(s)) => [sum((v for (M, v) in r if (M >> (j - 1)) & 1 == 0); init=0) for r in R]
                  for (j, s) in enumerate(full))
    Ms = sort(collect(keys(R[K])))
    classes = Dict{BitVector,UInt32}()
    for Ω in UInt32(0):UInt32((1 << length(full)) - 1)
        key = BitVector([M & Ω == 0 for M in Ms])
        haskey(classes, key) || (classes[key] = Ω)
    end
    seqset = Set([[sum((v for (M, v) in r if M & Ω == 0); init=0) for r in R] for Ω in values(classes)])
    R, single, length(classes), seqset
end
R3, single3, ncl3, seq3 = classify(3, 6)
check(seq3 == Set([zeros(Int, 6), ones(Int, 6), [1, 2, 5, 14, 42, 132], [1, 4, 21, 121, 728, 4488],
                   [1, 5, 33, 234, 1706, 12618], [1, 5, 42, 462, 6006, 87516]]),
      "three letters, k <= 6: the forbidden sets give exactly the six sequences 0, 1, C_k, B_k, Q_k, |L_3^k|")
R4, single4, ncl4, seq4 = classify(4, 6)
check([length(r) for r in R4] == [1, 14, 54, 92, 92, 92], "four letters: 1, 14, 54, 92, 92, 92 distinct sets M(w) for k = 1, ..., 6")
check(Set(keys(R4[4])) == Set(keys(R4[5])) == Set(keys(R4[6])), "four letters: the family of sets M(w) is the same for k = 4, 5, 6")
check(all(issubset(Set(keys(R4[k])), Set(keys(R4[6]))) for k in 1:3), "four letters: the families for k <= 3 lie in that family")
check([sum(values(r)) for r in R4] == [1, 14, 462, 24024, 1662804, 140229804], "|L_4^k| for k <= 6")
check((ncl4, length(seq4)) == (146, 95), "four letters: 146 classes of forbidden sets carrying 95 sequences")
TABLE = Dict("1234" => [0, 0, 0, 0, 0, 0], "1324" => [1, 4, 25, 196, 1764, 17424],
             "1243" => [1, 5, 42, 462, 6006, 87516], "2134" => [1, 5, 42, 462, 6006, 87516],
             "2143" => [1, 9, 102, 1308, 18463, 281411], "3142" => [1, 13, 319, 9411, 293707, 9361968],
             "4231" => [1, 14, 446, 20507, 1123561, 67346038], "4321" => [1, 14, 462, 22007, 1231705, 74690663])
for (ps, v) in (("1342 1423 2314 3124", [1, 10, 168, 3528, 84018, 2170740]),
                ("2341 2413 3412 4123", [1, 13, 341, 12012, 492252, 22064130]),
                ("1432 3214", [1, 14, 321, 8938, 278891, 9407065]),
                ("3241 4132", [1, 14, 419, 16950, 785866, 39117335]),
                ("2431 3421 4213 4312", [1, 14, 426, 17782, 862398, 45465438]))
    for p in split(ps); TABLE[p] = v; end
end
check(length(TABLE) == 24 && all(single4[p] == v for (p, v) in TABLE), "the table of single patterns of S_4, k <= 6")
C(k) = binomial(2k, k) ÷ (k + 1)
named = [zeros(Int, 6), ones(Int, 6), [C(k) for k in 1:6], [2C(k) - 1 for k in 1:6], [C(k)^2 for k in 1:6],
         [1, 5, 42, 462, 6006, 87516], [1, 4, 21, 121, 728, 4488], [1, 5, 33, 234, 1706, 12618],
         [1, 14, 462, 24024, 1662804, 140229804]]
check(all(s in seq4 for s in named), "the nine sequences of Proposition canon-four occur among the 95")

summary()
