/-
  Enumerative.lean -- Lean 4 kernel checks (core Lean only, no Mathlib) of finite statements on
  Eulerian polynomials of even and odd permutations, caged permutations, deformed Dumont
  permutations, the sequence Q_k and its Hankel determinants, and the 2-Steiner distance matrix
  of a path.

  Polynomials are lists of integer coefficients. Every theorem is proved by `decide +kernel`,
  so the kernel evaluates the definitions itself.

  * `eulerian_des`, `eulerian_exc` : for n ≤ 7 the numbers of permutations of [n] with k descents,
                         and with k excedances, are the Eulerian numbers (computed by their recurrence).
  * `mantaci`          : for n ≤ 7, Σ sgn(π) t^exc(π) = (1 - t)^(n-1).
  * `desarmenien_foata`: for n ≤ 7, Σ sgn(π) t^des(π) = (1 - t)^⌊n/2⌋ A_⌈n/2⌉(t).
  * `small_even_odd`   : the excedance polynomials P_3 = 1 + t + t², P_4 = 1 + 4t + 7t²,
                         Q_4 = 7t + 4t² + t³ and P_5 = 1 + 11t + 36t² + 11t³ + t⁴ by enumeration.
  * `p5_identity`      : 2 P_5 = A_5 + (1 - t)^4 and 4 P_5 = (2t² + 11t + 2)² + 15t², so P_5(t) > 0
                         for every real t.
  * `caged_example`    : the permutation 6 7 2 1 5 9 8 3 4 has c = 3 and exactly 16 maximal pairs.
  * `dumont_small`     : for n ≤ 4 and 0 ≤ j ≤ n the number of σ in S_(2n-1) with σ(i) ≤ i for even i
                         and σ(i) ≥ i for odd i ≥ 2(n-j)+1 is (n!)² for j = 0 and
                         (n-j)! (n-j+1)! G_j(n-j) for j ≥ 1.
  * `q_values`         : Q_0, ..., Q_24 computed by dynamic programming from the definition.
  * `hankel_shifted`, `hankel_unshifted` : det(Q_(i+j+1))_{12×12} and det(Q_(i+j))_{13×13} are the
                         stated negative integers, by fraction-free elimination and, independently,
                         as the constant term of the characteristic polynomial computed without
                         divisions.
  * `hankel_minors_positive` : the smaller leading Hankel determinants are positive.
  * `steiner_path`     : for 3 ≤ n ≤ 10 the characteristic polynomial of the 2-Steiner distance matrix
                         of the path P_n has a_(2n-4) = -(3n-5), 6 a_(2n-5) = -(n-1)(n-2)(2n²+6n-15)
                         and a_0 = -(n-1).
  * `steiner_peak`     : for 6 ≤ n ≤ 10 the largest |a_i|, i ≤ 2n-4, is attained at i = n-1 only.
-/

/-! ## Permutations -/

def insertAll (x : Nat) : List Nat → List (List Nat)
  | [] => [[x]]
  | y :: ys => (x :: y :: ys) :: (insertAll x ys).map (y :: ·)

/-- the permutations of 0, ..., n-1 in one-line notation -/
def perms : Nat → List (List Nat)
  | 0 => [[]]
  | n + 1 => (perms n).flatMap (insertAll n)

def des : List Nat → Nat
  | x :: y :: r => (if y < x then 1 else 0) + des (y :: r)
  | _ => 0

/-- excedances of the part of a permutation that starts at position `i` -/
def excFrom : Nat → List Nat → Nat
  | _, [] => 0
  | i, x :: r => (if i < x then 1 else 0) + excFrom (i + 1) r

def exc (p : List Nat) : Nat := excFrom 0 p

def inv : List Nat → Nat
  | [] => 0
  | x :: r => (r.filter (· < x)).length + inv r

def isEven (p : List Nat) : Bool := inv p % 2 == 0
def sgn (p : List Nat) : Int := if isEven p then 1 else -1

def addAt : Nat → Int → List Int → List Int
  | _, _, [] => []
  | 0, v, x :: xs => (x + v) :: xs
  | k + 1, v, x :: xs => x :: addAt k v xs

/-- Σ weight(π) t^stat(π) over the permutations of [n], as a list of n coefficients -/
def distr (n : Nat) (stat : List Nat → Nat) (weight : List Nat → Int) : List Int :=
  (perms n).foldl (fun acc p => addAt (stat p) (weight p) acc) (List.replicate n 0)

/-! ## Polynomials -/

def padd : List Int → List Int → List Int
  | [], q => q
  | p, [] => p
  | a :: as, b :: bs => (a + b) :: padd as bs

def pmul : List Int → List Int → List Int
  | [], _ => []
  | a :: as, q => padd (q.map (a * ·)) (0 :: pmul as q)

def ppow (p : List Int) : Nat → List Int
  | 0 => [1]
  | m + 1 => pmul p (ppow p m)

/-- from A_n to A_(n+1): A(n+1,k) = (k+1) A(n,k) + (n+1-k) A(n,k-1) -/
def eulerianStep (n : Nat) (A : List Int) : List Int :=
  (List.range (n + 1)).map fun (k : Nat) =>
    ((k : Int) + 1) * A.getD k 0 + ((n : Int) + 1 - k) * (if k == 0 then 0 else A.getD (k - 1) 0)

/-- the Eulerian polynomial A_n (A_0 = A_1 = 1) -/
def eulerian : Nat → List Int
  | 0 => [1]
  | n + 1 => eulerianStep n (eulerian n)

theorem eulerian_des :
    [1, 2, 3, 4, 5, 6, 7].all (fun n => distr n des (fun _ => 1) == eulerian n) = true := by
  decide +kernel

theorem eulerian_exc :
    [1, 2, 3, 4, 5, 6, 7].all (fun n => distr n exc (fun _ => 1) == eulerian n) = true := by
  decide +kernel

theorem mantaci :
    [1, 2, 3, 4, 5, 6, 7].all (fun n => distr n exc sgn == ppow [1, -1] (n - 1)) = true := by
  decide +kernel

theorem desarmenien_foata :
    [1, 2, 3, 4, 5, 6, 7].all
      (fun n => distr n des sgn == pmul (ppow [1, -1] (n / 2)) (eulerian (n - n / 2))) = true := by
  decide +kernel

def evenW (p : List Nat) : Int := if isEven p then 1 else 0
def oddW (p : List Nat) : Int := if isEven p then 0 else 1

theorem small_even_odd :
    distr 3 exc evenW = [1, 1, 1] ∧ distr 4 exc evenW = [1, 4, 7, 0] ∧
    distr 4 exc oddW = [0, 7, 4, 1] ∧ distr 5 exc evenW = [1, 11, 36, 11, 1] ∧
    distr 5 exc oddW = [0, 15, 30, 15, 0] := by decide +kernel

theorem p5_identity :
    eulerian 5 = [1, 26, 66, 26, 1] ∧
    padd (eulerian 5) (ppow [1, -1] 4) = [1, 11, 36, 11, 1].map (2 * ·) ∧
    [1, 11, 36, 11, 1].map (4 * ·) = padd (pmul [2, 11, 2] [2, 11, 2]) [0, 0, 15] := by
  decide +kernel

/-! ## Caged permutations -/

/-- number of positions k in [i, j] with p(k) between p(i) and p(j) -/
def cage (p : List Nat) (i j : Nat) : Nat :=
  let a := p.getD i 0
  let b := p.getD j 0
  ((List.range (j + 1)).filter fun k =>
    i ≤ k && min a b ≤ p.getD k 0 && p.getD k 0 ≤ max a b).length

def positionPairs (n : Nat) : List (Nat × Nat) :=
  (List.range n).flatMap fun i => ((List.range n).filter (i < ·)).map fun j => (i, j)

theorem caged_example :
    (positionPairs 9).all (fun t => cage [6, 7, 2, 1, 5, 9, 8, 3, 4] t.1 t.2 ≤ 3) = true ∧
    ((positionPairs 9).filter fun t => cage [6, 7, 2, 1, 5, 9, 8, 3, 4] t.1 t.2 == 3).length = 16 := by
  decide +kernel

/-! ## Deformed Dumont permutations -/

/-- σ(i) ≤ i for even i and σ(i) ≥ i for odd i ≥ 2(n-j)+1; `i` is the position (from 1) of the
head of the list, and the values in the list are 0, ..., 2n-2 -/
def dumontOK (n j : Nat) : Nat → List Nat → Bool
  | _, [] => true
  | i, v :: vs =>
    (if i % 2 == 0 then v + 1 ≤ i else (i < 2 * (n - j) + 1 || i ≤ v + 1)) && dumontOK n j (i + 1) vs

def dumontCount (n j : Nat) : Nat := ((perms (2 * n - 1)).filter (dumontOK n j 1)).length

/-- `G j x` is G_(j+1)(x): G_1 = 1, G_(j+1)(x) = (x+1) ((x+2) G_j(x+1) - x G_j(x)) -/
def G : Nat → Int → Int
  | 0, _ => 1
  | j + 1, x => (x + 1) * ((x + 2) * G j (x + 1) - x * G j x)

def fact : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * fact n

def dumontFormula (n j : Nat) : Int :=
  if j == 0 then (fact n : Int) * fact n
  else (fact (n - j) : Int) * fact (n - j + 1) * G (j - 1) ((n - j : Nat) : Int)

theorem dumont_small :
    [1, 2, 3, 4].all (fun n => (List.range (n + 1)).all fun j =>
      (dumontCount n j : Int) == dumontFormula n j) = true := by decide +kernel

theorem dumont_table :
    (List.range 5).map (dumontFormula 4) = [576, 144, 72, 56, 56] ∧
    (List.range 9).map (dumontFormula 8) =
      [1625702400, 203212800, 50803200, 19699200, 10483200, 7110144, 5807232, 5410688, 5410688] := by
  decide +kernel

/-! ## The numbers Q_k

Q_k is the number of words with k letters 1, k letters 2 and k letters 3 in which every prefix has
at least as many 1 as 2 and at least as many 2 as 3, and no letter 1 comes after a subword 3 2.
`f(a, b, c, s)` is the number of ways to complete a prefix with a, b, c letters 1, 2, 3 in the
state s (0: no 3 yet; 1: a 3 has occurred; 2: a 3 followed later by a 2 has occurred). A cell holds
the three values s = 0, 1, 2; a slice holds the cells (b, c) for one value of a. -/

abbrev Cell := Nat × Nat × Nat

def zcell : Cell := (0, 0, 0)

/-- the cells c, c+1, ..., k of the row b of the slice a; `u` is the same row of the slice a + 1
and `r` the row b + 1 of the slice a -/
def rowGo (k a b : Nat) : Nat → List Cell → List Cell → List Cell
  | c, u :: us, r :: rs =>
    match rowGo k a b (c + 1) us rs with
    | rest =>
      (if c ≤ b then
        if a == k && b == k && c == k then (1, 1, 1)
        else
          let ua := if a < k then u else zcell
          let ra := if b < a then r else zcell
          let na := if c < b then rest.headD zcell else zcell
          (ua.1 + ra.1 + na.2.1, ua.2.1 + ra.2.2 + na.2.1, ra.2.2 + na.2.2)
      else zcell) :: rest
  | _, _, _ => []

def sliceGo (k a : Nat) (zrow : List Cell) : Nat → List (List Cell) → List (List Cell)
  | b, u :: us =>
    match sliceGo k a zrow (b + 1) us with
    | rest => (if b ≤ a then rowGo k a b 0 u (rest.headD zrow) else zrow) :: rest
  | _, [] => []

/-- `slice k j` is the slice a = k - j -/
def slice (k : Nat) : Nat → List (List Cell)
  | 0 => sliceGo k k (List.replicate (k + 1) zcell) 0
      (List.replicate (k + 1) (List.replicate (k + 1) zcell))
  | j + 1 => sliceGo k (k - (j + 1)) (List.replicate (k + 1) zcell) 0 (slice k j)

def Q (k : Nat) : Nat := (((slice k k).headD []).headD zcell).1

def Qlist : List Int :=
  [1, 1, 5, 33, 234, 1706, 12618, 94157, 706878, 5330403, 40332881, 306023196, 2327290506,
   17734226120, 135376087792, 1035065812309, 7925664456804, 60771825678389, 466587436417569,
   3586731522598141, 27604168028694252, 212685629040409758, 1640473066548280308,
   12666272996480868428, 97894846717057492194]

theorem q_values : (List.range 25).map (fun k => (Q k : Int)) = Qlist := by decide +kernel

/-! ## Determinants -/

/-- one step of fraction-free elimination: pivot `piv`, rest of the pivot row `prow`, previous
pivot `prev` -/
def bareissStep (prev piv : Int) (prow : List Int) (rows : List (List Int)) : List (List Int) :=
  rows.map fun r =>
    match r with
    | [] => []
    | r0 :: rt => List.zipWith (fun x p => (x * piv - r0 * p) / prev) rt prow

/-- determinant by fraction-free elimination without row exchanges; `none` if a pivot is 0 -/
def bareiss : Nat → Int → List (List Int) → Option Int
  | _, _, [[x]] => some x
  | f + 1, prev, (piv :: prow) :: rows =>
    if piv == 0 then none else bareiss f piv (bareissStep prev piv prow rows)
  | _, _, _ => none

def det (M : List (List Int)) : Option Int := bareiss M.length 1 M

def dot (u v : List Int) : Int := (List.zipWith (· * ·) u v).foldl (· + ·) 0

def matVec (M : List (List Int)) (v : List Int) : List Int := M.map (dot · v)

/-- R v, R M v, R M² v, ... (j terms) -/
def krylov (M : List (List Int)) (R : List Int) : Nat → List Int → List Int
  | 0, _ => []
  | j + 1, v => dot R v :: krylov M R j (matVec M v)

/-- from the characteristic polynomial `p` of the leading k × k block (coefficients from the
highest) to that of the leading (k+1) × (k+1) block, without divisions (Samuelson, Berkowitz) -/
def charStep (A : List (List Int)) (k : Nat) (p : List Int) : List Int :=
  let M := (A.take k).map (·.take k)
  let R := (A.getD k []).take k
  let C := (A.take k).map (·.getD k 0)
  let a := (A.getD k []).getD k 0
  (pmul (1 :: (-a) :: (krylov M R k C).map (- ·)) p).take (k + 2)

def charPolyTo (A : List (List Int)) : Nat → List Int
  | 0 => [1]
  | k + 1 => charStep A k (charPolyTo A k)

/-- coefficients of det(x - A), from the highest -/
def charPoly (A : List (List Int)) : List Int := charPolyTo A A.length

/-- determinant as (-1)^N times the constant term of the characteristic polynomial -/
def detChar (A : List (List Int)) : Int :=
  (if A.length % 2 == 0 then 1 else -1) * (charPoly A).getD A.length 0

def hankel (n s : Nat) : List (List Int) :=
  (List.range n).map fun i => (List.range n).map fun j => Qlist.getD (i + j + s) 0

theorem hankel_shifted :
    det (hankel 12 1) = some (-16871599970737005465806167716982557747256) ∧
    detChar (hankel 12 1) = -16871599970737005465806167716982557747256 := by decide +kernel

theorem hankel_unshifted :
    det (hankel 13 0) = some (-169232977731413820207351628133858712800869482) ∧
    detChar (hankel 13 0) = -169232977731413820207351628133858712800869482 := by decide +kernel

theorem hankel_minors_positive :
    (List.range 12).all (fun n => match det (hankel (n + 1) 0) with | some d => 0 < d | none => false) = true ∧
    (List.range 11).all (fun n => match det (hankel (n + 1) 1) with | some d => 0 < d | none => false) = true := by
  decide +kernel

/-! ## The 2-Steiner distance matrix of the path P_n -/

/-- e_1, f_1, e_2, ..., f_(n-2), e_(n-1) with e_i = {i, i+1}, f_i = {i, i+2} -/
def steinerBasis (n : Nat) : List (Nat × Nat) :=
  (List.range (n - 1)).flatMap fun i =>
    if i + 2 < n then [(i + 1, i + 2), (i + 1, i + 3)] else [(i + 1, i + 2)]

def steinerMatrix (n : Nat) : List (List Int) :=
  (steinerBasis n).map fun p => (steinerBasis n).map fun q =>
    ((max p.2 q.2 - min p.1 q.1 : Nat) : Int)

/-- the coefficient of x^(2n-3-i) is the entry i of `charPoly (steinerMatrix n)` -/
def steinerOK (n : Nat) : Bool :=
  let c := charPoly (steinerMatrix n)
  c.length == 2 * n - 2 &&
  c.getD 1 0 == -(3 * (n : Int) - 5) &&
  6 * c.getD 2 0 == -(((n : Int) - 1) * ((n : Int) - 2) * (2 * (n : Int) * n + 6 * n - 15)) &&
  c.getD (2 * n - 3) 0 == -((n : Int) - 1)

theorem steiner_path : [3, 4, 5, 6, 7, 8, 9, 10].all steinerOK = true := by decide +kernel

/-- among a_0, ..., a_(2n-4) the largest absolute value is at a_(n-1) only (entry n - 2 of the list) -/
def steinerPeak (n : Nat) : Bool :=
  let c := charPoly (steinerMatrix n)
  (List.range (2 * n - 3)).all fun i =>
    i + 1 == n - 2 || (c.getD (i + 1) 0).natAbs < (c.getD (n - 2) 0).natAbs

theorem steiner_peak : [6, 7, 8, 9, 10].all steinerPeak = true := by decide +kernel

#print axioms eulerian_des
#print axioms eulerian_exc
#print axioms mantaci
#print axioms desarmenien_foata
#print axioms small_even_odd
#print axioms p5_identity
#print axioms caged_example
#print axioms dumont_small
#print axioms dumont_table
#print axioms q_values
#print axioms hankel_shifted
#print axioms hankel_unshifted
#print axioms hankel_minors_positive
#print axioms steiner_path
#print axioms steiner_peak
