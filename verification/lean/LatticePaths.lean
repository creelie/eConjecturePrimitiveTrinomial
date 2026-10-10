/-
  LatticePaths.lean -- Lean 4 kernel checks (core Lean only, no Mathlib) for
  "Even lattice paths and the Catalan numbers".

  A word of length k is a natural number below 2^k: bit i - 1 holds the i-th letter (1 = N, 0 = E).
  `B k x y` is the parity of the number of positions i with x_i = y_i and w(x_{<i}) = w(y_{<i}),
  which is the parity of the number of common edges of the two lattice paths. Every theorem is
  proved by `decide +kernel`, so the kernel evaluates the definitions itself.

  * `star_lemma`       : Lemma 4.1 for every k ≤ 6: the pairs (a, b) with w(a) = w(b) + 1,
                         B(a, b) = k + 1 (mod 2) and B(a, c) = B(b, c) for every c of another weight
                         are exactly the pairs (u1, u0) and, for odd k ≥ 3, (1(10)^j, 0(01)^j).
  * `canonical_pairs`  : Lemma 5.2 for every k ≤ 7: B(u1, c) + B(u0, c) = [w(c_{<k}) = w(u)].
  * `skeleton_identity`: Proposition 2.2 for every m ≤ 6: for each skeleton (M, S) of [m], words
                         x ∈ C_a and y ∈ C_{a'} satisfy B_m(x, y) = B_k(a, a') and w(x) = |M| + w(a).
  * `skeleton_count`   : Corollary 1.3: [m] has C(m, ⌊m/2⌋) skeletons for every m ≤ 12.
  * `shankar_n1` .. `shankar_n3` : Theorem 1.1 for n ≤ 3: among the paths from (0,0) to (n,n) there
                         are exactly C_n families of 2^n paths with pairwise even common edges and
                         none of 2^n + 1 paths; the C_n families F_M are among them, so they are all.
-/

/-- `B` with `i` letters left, current weights `wx`, `wy` -/
def BAux : Nat → Nat → Nat → Nat → Nat → Bool
  | 0, _, _, _, _ => false
  | i + 1, x, y, wx, wy =>
    xor (x % 2 == y % 2 && wx == wy) (BAux i (x / 2) (y / 2) (wx + x % 2) (wy + y % 2))

def B (k x y : Nat) : Bool := BAux k x y 0 0

/-- weight of the first `k` letters -/
def wt : Nat → Nat → Nat
  | 0, _ => 0
  | k + 1, x => x % 2 + wt k (x / 2)

/-- 1(10)^j as a word of length k = 2j + 1 (bits 0, 1, 3, 5, ...) -/
def excA : Nat → Nat
  | 0 => 0
  | i + 1 => excA i + (if i == 0 || i % 2 == 1 then 2 ^ i else 0)

/-- 0(01)^j as a word of length k = 2j + 1 (bits 2, 4, 6, ...) -/
def excB : Nat → Nat
  | 0 => 0
  | i + 1 => excB i + (if i != 0 && i % 2 == 0 then 2 ^ i else 0)

def canonical (k a b : Nat) : Bool := b < 2 ^ (k - 1) && a == b + 2 ^ (k - 1)

def exceptional (k a b : Nat) : Bool := k % 2 == 1 && 3 ≤ k && a == excA k && b == excB k

/-- the hypotheses of the star lemma -/
def star (k a b : Nat) : Bool :=
  wt k a == wt k b + 1 && B k a b == ((k + 1) % 2 == 1) &&
    (List.range (2 ^ k)).all fun c => wt k c == wt k a || wt k c == wt k b || B k a c == B k b c

/-- the star pairs are exactly the canonical pairs and the exceptional pair -/
def starExact (k : Nat) : Bool :=
  (List.range (2 ^ k)).all fun a => (List.range (2 ^ k)).all fun b =>
    star k a b == (canonical k a b || exceptional k a b)

theorem star_lemma : (List.range 7).all (fun k => k == 0 || starExact k) = true := by decide +kernel

/-- B(u1, c) + B(u0, c) = [w(c_{<k}) = w(u)] -/
def canonicalFormula (k : Nat) : Bool :=
  (List.range (2 ^ (k - 1))).all fun u => (List.range (2 ^ k)).all fun c =>
    xor (B k (u + 2 ^ (k - 1)) c) (B k u c) == (wt (k - 1) c == wt (k - 1) u)

theorem canonical_pairs : (List.range 8).all (fun k => k == 0 || canonicalFormula k) = true := by
  decide +kernel

/-- skeletons of [m] as (arcs, free points), positions 0-based; `r` positions remain -/
def gen : Nat → Nat → List Nat → List (Nat × Nat) → List Nat → List (List (Nat × Nat) × List Nat)
  | 0, _, stack, arcs, free => if stack.isEmpty then [(arcs, free)] else []
  | r + 1, pos, stack, arcs, free =>
    gen r (pos + 1) (pos :: stack) arcs free ++
      match stack with
      | [] => gen r (pos + 1) [] arcs (free ++ [pos])
      | p :: st => gen r (pos + 1) st ((p, pos) :: arcs) free

def skeletons (m : Nat) : List (List (Nat × Nat) × List Nat) := gen m 0 [] [] []

/-- letters of `a` placed at the free points -/
def place : List Nat → Nat → Nat
  | [], _ => 0
  | s :: ss, a => (if a % 2 == 1 then 2 ^ s else 0) + place ss (a / 2)

/-- orientation `o` of the arcs: bit t chooses N at the first or at the second end of arc t -/
def orient : List (Nat × Nat) → Nat → Nat
  | [], _ => 0
  | (p, q) :: rest, o => (if o % 2 == 1 then 2 ^ p else 2 ^ q) + orient rest (o / 2)

def skeletonOK (m : Nat) (sk : List (Nat × Nat) × List Nat) : Bool :=
  let (arcs, free) := sk
  let k := free.length
  let h := arcs.length
  let W := List.range (2 ^ k)
  let O := List.range (2 ^ h)
  W.all fun a => O.all fun o =>
    let x := place free a + orient arcs o
    wt m x == h + wt k a &&
      W.all fun a' => O.all fun o' => B m x (place free a' + orient arcs o') == B k a a'

theorem skeleton_identity :
    (List.range 7).all (fun m => (skeletons m).all (skeletonOK m)) = true := by decide +kernel

def binom : Nat → Nat → Nat
  | _, 0 => 1
  | 0, _ + 1 => 0
  | n + 1, r + 1 => binom n r + binom n (r + 1)

theorem skeleton_count :
    (List.range 13).all (fun m => (skeletons m).length == binom m (m / 2)) = true := by decide +kernel

/-! Shankar's conjecture for n ≤ 3 -/

def paths (n : Nat) : List Nat := (List.range (2 ^ (2 * n))).filter fun x => wt (2 * n) x == n

/-- number of cliques of size `s` in the even-intersection graph on the list (fuel `f` ≥ length) -/
def cliques (n : Nat) : Nat → List Nat → Nat → Nat
  | _, _, 0 => 1
  | 0, _, _ + 1 => 0
  | _ + 1, [], _ + 1 => 0
  | f + 1, v :: vs, s + 1 =>
    cliques n f (vs.filter fun x => !B (2 * n) v x) s + cliques n f vs (s + 1)

def evenCount (n s : Nat) : Nat := cliques n (paths n).length (paths n) s

/-- the families F_M for the perfect matchings among the skeletons of [2n] -/
def catalanFamilies (n : Nat) : List (List Nat) :=
  ((skeletons (2 * n)).filter fun sk => sk.2.isEmpty).map fun sk =>
    (List.range (2 ^ n)).map fun o => orient sk.1 o

def familiesOK (n : Nat) : Bool :=
  let fams := catalanFamilies n
  fams.length == binom (2 * n) n / (n + 1) &&
  fams.all (fun F => F.all fun x => wt (2 * n) x == n && F.all fun y => x == y || !B (2 * n) x y) &&
  -- distinct: two families are different when some word of one is missing from the other
  (List.range fams.length).all fun i => (List.range fams.length).all fun j =>
    i == j || (fams.getD i []).any fun x => !(fams.getD j []).contains x

theorem shankar_n1 : evenCount 1 2 = 1 ∧ evenCount 1 3 = 0 ∧ familiesOK 1 = true := by decide +kernel
theorem shankar_n2 : evenCount 2 4 = 2 ∧ evenCount 2 5 = 0 ∧ familiesOK 2 = true := by decide +kernel
theorem shankar_n3 : evenCount 3 8 = 5 ∧ evenCount 3 9 = 0 ∧ familiesOK 3 = true := by decide +kernel

#print axioms star_lemma
#print axioms canonical_pairs
#print axioms skeleton_identity
#print axioms skeleton_count
#print axioms shankar_n1
#print axioms shankar_n2
#print axioms shankar_n3
