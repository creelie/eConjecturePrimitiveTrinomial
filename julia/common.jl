# common.jl -- helpers shared by the verification scripts (standard library only).

const NPASS = Ref(0)
const NFAIL = Ref(0)

"record one check and print a PASS or FAIL line"
function check(ok::Bool, what)
    if ok
        NPASS[] += 1; println("PASS: ", what)
    else
        NFAIL[] += 1; println("FAIL: ", what)
    end
    flush(stdout)
    ok
end

"print the summary line of a script and set the exit code"
function summary()
    println("SUMMARY: $(NPASS[]) passed, $(NFAIL[]) failed")
    exit(NFAIL[] == 0 ? 0 : 1)
end

"number of common edges of two words over the letters 0, 1, ..., d-1 (monotone paths in Z^d)"
function common(x, y)
    c = 0; nz = 0
    diff = zeros(Int, max(maximum(x; init=0), maximum(y; init=0)) + 1)
    @inbounds for i in eachindex(x)
        s = x[i]; t = y[i]
        if s == t
            nz == 0 && (c += 1)
        else
            diff[s+1] == 0 && (nz += 1); diff[s+1] += 1; diff[s+1] == 0 && (nz -= 1)
            diff[t+1] == 0 && (nz += 1); diff[t+1] -= 1; diff[t+1] == 0 && (nz -= 1)
        end
    end
    c
end

"number of common edges of two 0/1 words, counted as sets of edges of lattice paths (1 = N, 0 = E)"
function common_edges(x, y)
    function edges(w)
        E = Set{NTuple{3,Int}}(); X = 0; Y = 0
        for s in w
            push!(E, (X, Y, s)); s == 1 ? (Y += 1) : (X += 1)
        end
        E
    end
    length(intersect(edges(x), edges(y)))
end

"all pairs i < j of the family satisfy common(x, y) = parity (mod 2), and the words are distinct"
function pairwise_parity(F, parity)
    length(Set(F)) == length(F) || return false
    for i in 1:length(F), j in i+1:length(F)
        common(F[i], F[j]) % 2 == parity || return false
    end
    true
end

"call f(p) for every permutation p of 1:n (p is reused; copy it to keep it)"
function eachperm(f, n)
    p = collect(1:n)
    function rec(k)
        if k > n
            f(p); return
        end
        for i in k:n
            p[k], p[i] = p[i], p[k]
            rec(k + 1)
            p[k], p[i] = p[i], p[k]
        end
    end
    rec(1)
end

"sign of a permutation of 1:n"
function permsign(p)
    n = length(p); seen = falses(n); s = 1
    for i in 1:n
        seen[i] && continue
        j = i; L = 0
        while !seen[j]
            seen[j] = true; j = p[j]; L += 1
        end
        iseven(L) && (s = -s)
    end
    s
end

"determinant of an integer matrix by fraction-free elimination (Bareiss), exact"
function det_bareiss(M)
    A = BigInt.(M); n = size(A, 1); sgn = 1; prev = big(1)
    n == 0 && return big(1)
    for i in 1:n-1
        if A[i, i] == 0
            r = findfirst(r -> A[r, i] != 0, i+1:n)
            r === nothing && return big(0)
            r += i
            A[i, :], A[r, :] = A[r, :], A[i, :]; sgn = -sgn
        end
        for r in i+1:n, c in i+1:n
            A[r, c] = div(A[r, c] * A[i, i] - A[r, i] * A[i, c], prev)
        end
        prev = A[i, i]
    end
    sgn * A[n, n]
end

"determinant by Gaussian elimination over the rationals, exact"
function det_rational(M)
    A = Rational{BigInt}.(M); n = size(A, 1); d = one(Rational{BigInt})
    for i in 1:n
        r = findfirst(r -> A[r, i] != 0, i:n)
        r === nothing && return zero(Rational{BigInt})
        r += i - 1
        if r != i
            A[i, :], A[r, :] = A[r, :], A[i, :]; d = -d
        end
        d *= A[i, i]
        for r2 in i+1:n
            f = A[r2, i] / A[i, i]
            f == 0 && continue
            for c in i:n
                A[r2, c] -= f * A[i, c]
            end
        end
    end
    d
end
