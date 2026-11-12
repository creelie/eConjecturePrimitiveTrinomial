# hankel.jl -- the numbers Q_k and their Hankel determinants.
#
# Q_k is the number of words with k letters 1, k letters 2 and k letters 3 in which every prefix
# has at least as many 1 as 2 and at least as many 2 as 3, and which contain no subsequence 3 2 1.
#
#  1. Q_k for k <= 5 by enumeration of all words.
#  2. Q_0, ..., Q_24 by two dynamic programmes (forward over prefixes, backward with a memo) and
#     by Shankar's multisum (Theorem 7.1 of arXiv:2608.30002).
#  3. det(Q_(i+j+1))_{0<=i,j<12} and det(Q_(i+j))_{0<=i,j<13} are negative; both are computed by
#     Gaussian elimination over the rationals and by fraction-free elimination over the integers.
#  4. The smaller leading Hankel determinants are positive.
#  5. For H = (Q_(i+j+1))_{12x12} and v the last column of the adjugate of H, v^T H v < 0.

include(joinpath(@__DIR__, "common.jl"))

const QLIST = parse.(BigInt, split("""1 1 5 33 234 1706 12618 94157 706878 5330403 40332881 306023196
2327290506 17734226120 135376087792 1035065812309 7925664456804 60771825678389 466587436417569
3586731522598141 27604168028694252 212685629040409758 1640473066548280308 12666272996480868428
97894846717057492194"""))

"enumeration: state = (a, b, c, s), s = 0 no 3 yet, 1 a 3 has occurred, 2 a 3 and later a 2"
function Qbrute(k)
    total = 0
    w = Int[]
    function avoids321(w)
        for i in 1:length(w), j in i+1:length(w), l in j+1:length(w)
            (w[i] == 3 && w[j] == 2 && w[l] == 1) && return false
        end
        true
    end
    function rec(a, b, c)
        if a == k && b == k && c == k
            avoids321(w) && (total += 1); return
        end
        if a < k; push!(w, 1); rec(a + 1, b, c); pop!(w); end
        if b < a; push!(w, 2); rec(a, b + 1, c); pop!(w); end
        if c < b; push!(w, 3); rec(a, b, c + 1); pop!(w); end
    end
    rec(0, 0, 0)
    total
end

function Qforward(k)
    cur = Dict((0, 0, 0, 0) => big(1))
    for _ in 1:3k
        nxt = Dict{NTuple{4,Int},BigInt}()
        for ((a, b, c, s), v) in cur
            add(key) = (nxt[key] = get(nxt, key, big(0)) + v)
            (a < k && s != 2) && add((a + 1, b, c, s))
            b < a && add((a, b + 1, c, s >= 1 ? 2 : 0))
            c < b && add((a, b, c + 1, max(s, 1)))
        end
        cur = nxt
    end
    sum(values(cur))
end

function Qbackward(k)
    memo = Dict{NTuple{4,Int},BigInt}()
    function f(a, b, c, s)
        (a == k && b == k && c == k) && return big(1)
        get!(memo, (a, b, c, s)) do
            t = big(0)
            (a < k && s < 2) && (t += f(a + 1, b, c, s))
            b < a && (t += f(a, b + 1, c, s >= 1 ? 2 : 0))
            c < b && (t += f(a, b, c + 1, max(s, 1)))
            t
        end
    end
    f(0, 0, 0, 0)
end

println("== Q_k")
check([Qbrute(k) for k in 0:5] == QLIST[1:6], "Q_0..Q_5 = 1, 1, 5, 33, 234, 1706 by enumeration of words")
check([Qforward(k) for k in 0:24] == QLIST, "Q_0..Q_24 by the forward dynamic programme")
check([Qbackward(k) for k in 0:24] == QLIST, "Q_0..Q_24 by the backward dynamic programme")

"Shankar's multisum: Q_k = C_k + sum over 1 <= b <= k-1, 0 <= c <= b <= r <= k-1 of T(b,c,r)"
function qmultisum(k)
    k == 0 && return big(1)
    bin(n, j) = (0 <= j <= n) ? binomial(big(n), big(j)) : big(0)
    s = binomial(big(2k), big(k)) // (k + 1)
    for b in 1:k-1, c in 0:b, r in b:k-1
        n1 = 2k - b - c; n2 = r + b - 1; n3 = k - 1 - r + c
        s += (b - c + 1) // (k - c + 1) * bin(n1, k - b) * (r - b + 2) // (r + 1) * bin(n2, b - 1) * bin(n3, c)
    end
    @assert denominator(s) == 1
    numerator(s)
end
check([qmultisum(k) for k in 0:24] == QLIST, "Q_0..Q_24 by Shankar's multisum")

println("== Hankel determinants")
hankel(n, s) = [QLIST[i+j+s+1] for i in 0:n-1, j in 0:n-1]
const D1 = parse(BigInt, "-16871599970737005465806167716982557747256")
const D0 = parse(BigInt, "-169232977731413820207351628133858712800869482")
check(det_rational(hankel(12, 1)) == D1, "det (Q_(i+j+1))_{12x12} = $D1 (rational elimination)")
check(det_bareiss(hankel(12, 1)) == D1, "det (Q_(i+j+1))_{12x12} (fraction-free elimination)")
check(det_rational(hankel(13, 0)) == D0, "det (Q_(i+j))_{13x13} = $D0 (rational elimination)")
check(det_bareiss(hankel(13, 0)) == D0, "det (Q_(i+j))_{13x13} (fraction-free elimination)")
check(D1 < 0 && D0 < 0, "both determinants are negative")
check(all(det_rational(hankel(n, 0)) > 0 for n in 1:12), "det (Q_(i+j))_{n x n} > 0 for n <= 12")
check(all(det_rational(hankel(n, 1)) > 0 for n in 1:11), "det (Q_(i+j+1))_{n x n} > 0 for n <= 11")

# explicit witness: v = last column of adj(H) = det(H) * H^(-1) e_n, by Cramer's rule
let n = 12, H = hankel(12, 1)
    v = BigInt[]
    for r in 1:n
        minor = H[[i for i in 1:n if i != n], [j for j in 1:n if j != r]]
        push!(v, (-1)^(r + n) * det_bareiss(minor))
    end
    val = sum(v[i] * H[i, j] * v[j] for i in 1:n, j in 1:n)
    check(H * v == [i == n ? D1 : big(0) for i in 1:n], "H v = det(H) e_12 for the integer vector v")
    check(val == D1 * det_bareiss(hankel(11, 1)) && val < 0, "v^T H v = det(H) det(H_11) < 0")
end

summary()
