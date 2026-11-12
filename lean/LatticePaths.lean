/-
  LatticePaths.lean -- Lean 4 kernel checks (core Lean only, no Mathlib) for
  "Parity Families of Lattice Paths and Real-Rooted Signed Eulerian Polynomials".

  A word of length k is a natural number below 2^k: bit i - 1 holds the i-th letter (1 = N, 0 = E).
  `B k x y` is the parity of the number of positions i with x_i = y_i and w(x_{<i}) = w(y_{<i}),
  which is the parity of the number of common edges of the two lattice paths. Every theorem is
  proved by `decide +kernel`, so the kernel evaluates the definitions itself.

  * `star_lemma`       : Lemma 3.9 for every k ≤ 6: the pairs (a, b) with w(a) = w(b) + 1,
                         B(a, b) = k + 1 (mod 2) and B(a, c) = B(b, c) for every c of another weight
                         are exactly the pairs (u1, u0) and, for odd k ≥ 3, (1(10)^j, 0(01)^j).
  * `canonical_pairs`  : Lemma 3.11 for every k ≤ 7: B(u1, c) + B(u0, c) = [w(c_{<k}) = w(u)].
  * `skeleton_identity`: Proposition 3.4 for every m ≤ 6: for each skeleton (M, S) of [m], words
                         x ∈ C_a and y ∈ C_{a'} satisfy B_m(x, y) = B_k(a, a') and w(x) = |M| + w(a).
  * `skeleton_count`   : Proposition 3.13: [m] has C(m, ⌊m/2⌋) skeletons for every m ≤ 12.
  * `shankar_n1` .. `shankar_n3` : Theorem A for n ≤ 3: among the paths from (0,0) to (n,n) there
                         are exactly C_n families of 2^n paths with pairwise even common edges and
                         none of 2^n + 1 paths; the C_n families F_M are among them, so they are all.
  * `three_rows_even`  : for a = 4, 8, 10, 12 the family T_a consists of 2a - 2 paths from (0,0) to
                         (a,3) that pairwise share an even number of edges.
  * `square_odd`       : the families F_10 and F_12 built from T_8 and T_10 consist of 33 and 54
                         paths in the square that pairwise share an odd number of edges.
  * `odd_family_7`, `odd_family_8` : explicit families of 23 paths in the 7 × 7 square and of 31
                         paths in the 8 × 8 square that pairwise share an odd number of edges.
  * `block_families_dim3` .. `block_families_dim5` : for words over d letters (monotone paths in
                         Z^d), the d^r concatenations of r blocks ab, ba, cc pairwise share an even
                         number of edges (d = 3, 4 with r ≤ 3; d = 5 with r ≤ 2).
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

/-! ## Further families of paths -/

/-- the word with the given letters (first letter first; 1 = N, 0 = E) -/
def ofDigits : List Nat → Nat
  | [] => 0
  | d :: ds => d + 2 * ofDigits ds

/-- `p x y` for every pair of entries `x` before `y` -/
def pairwise {α : Type} (p : α → α → Bool) : List α → Bool
  | [] => true
  | x :: xs => xs.all (p x) && pairwise p xs

/-- distinct words of length `m` and weight `w` that pairwise share an even number of edges -/
def evenFamily (m w : Nat) (F : List Nat) : Bool :=
  F.all (fun x => x < 2 ^ m && wt m x == w) && pairwise (fun x y => x != y && !B m x y) F

/-- distinct words of length `m` and weight `w` that pairwise share an odd number of edges -/
def oddFamily (m w : Nat) (F : List Nat) : Bool :=
  F.all (fun x => x < 2 ^ m && wt m x == w) && pairwise (fun x y => x != y && B m x y) F

/-! Three rows: the path (i₁, i₂, i₃) from (0,0) to (a,3) has its north steps on the lines
x = i₁ ≤ i₂ ≤ i₃, so its letters N are at the positions i₁, i₂ + 1, i₃ + 2 (counted from 0). -/

def tripleWord (t : Nat × Nat × Nat) : Nat := 2 ^ t.1 + 2 ^ (t.2.1 + 1) + 2 ^ (t.2.2 + 2)

/-- the family T_a: A_z = (0,1,z), B_z = (2,3,z), C_z = (z,a-1,a), D_z = (z,a-3,a-2), O, O' -/
def threeRows (a : Nat) : List Nat :=
  (((List.range a).filter fun z => z % 2 == 1).map fun z => tripleWord (0, 1, z)) ++
  (((List.range (a - 1)).filter fun z => z % 2 == 0 && 4 ≤ z).map fun z => tripleWord (2, 3, z)) ++
  (((List.range a).filter fun z => z % 2 == 1).map fun z => tripleWord (z, a - 1, a)) ++
  (((List.range (a - 3)).filter fun z => z % 2 == 0 && 2 ≤ z).map fun z => tripleWord (z, a - 3, a - 2)) ++
  [tripleWord (0, 0, 0), tripleWord (a, a, a)]

/-- T_a has 2a - 2 paths from (0,0) to (a,3), pairwise with an even number of common edges -/
theorem three_rows_even :
    [4, 8, 10, 12].all (fun a => (threeRows a).length == 2 * a - 2 && evenFamily (a + 3) 3 (threeRows a))
      = true := by decide +kernel

/-! The family F_n in the square, n even: for the windows j = 0, 4, 8, ... the words
E^j N t N E^(n-3-j) with t the transpose of a path of T_(n-2), and for n = 2 (mod 4) the words
E^(n-2) N N^k E N^(n-2-k) N E with k even. -/

def squareFamily (n : Nat) : List Nat :=
  (((List.range (n - 2)).filter fun j => j % 4 == 0).flatMap fun j =>
    (threeRows (n - 2)).map fun t => 2 ^ j + (2 ^ (n + 1) - 1 - t) * 2 ^ (j + 1) + 2 ^ (j + n + 2)) ++
  (if n % 4 == 2 then
    ((List.range (n - 1)).filter fun k => k % 2 == 0).map fun k =>
      (2 ^ (n + 1) - 1) * 2 ^ (n - 2) - 2 ^ (n - 2 + k + 1)
   else [])

/-- F_10 and F_12 have 33 and 54 paths, pairwise with an odd number of common edges -/
theorem square_odd :
    (squareFamily 10).length = 33 ∧ oddFamily 20 10 (squareFamily 10) = true ∧
    (squareFamily 12).length = 54 ∧ oddFamily 24 12 (squareFamily 12) = true := by decide +kernel

/-! Explicit odd families in the squares of side 7 and 8 -/

def odd7 : List Nat := [
  ofDigits [0,1,0,0,1,1,0,1,1,0,1,0,1,0],
  ofDigits [0,1,1,1,1,0,0,1,1,0,0,0,1,0],
  ofDigits [0,1,1,1,1,1,0,0,1,1,0,0,0,0],
  ofDigits [0,0,0,0,0,0,1,1,0,1,1,1,1,1],
  ofDigits [0,1,0,1,0,0,0,1,1,1,1,0,1,0],
  ofDigits [0,0,0,0,1,1,0,1,0,1,0,1,1,1],
  ofDigits [0,0,0,0,0,0,0,1,1,1,1,1,1,1],
  ofDigits [0,1,1,1,1,1,0,0,1,0,0,1,0,0],
  ofDigits [1,1,1,1,1,0,0,1,0,0,0,0,0,1],
  ofDigits [1,1,0,1,1,0,0,1,1,0,0,0,0,1],
  ofDigits [0,0,0,0,0,0,1,1,1,1,0,1,1,1],
  ofDigits [0,0,0,0,0,1,1,0,1,1,1,0,1,1],
  ofDigits [1,0,1,0,0,0,1,1,0,1,0,1,0,1],
  ofDigits [0,0,0,1,1,0,1,1,1,1,0,1,0,0],
  ofDigits [0,0,0,0,0,1,1,0,1,0,1,1,1,1],
  ofDigits [0,1,0,0,1,1,0,0,1,1,1,0,1,0],
  ofDigits [0,1,1,1,1,0,0,1,1,0,1,0,0,0],
  ofDigits [0,1,1,1,1,0,1,1,1,0,0,0,0,0],
  ofDigits [1,1,1,1,0,0,0,1,1,0,0,0,0,1],
  ofDigits [1,0,1,0,0,1,1,0,1,0,0,1,0,1],
  ofDigits [1,1,1,0,1,1,0,0,1,0,0,0,0,1],
  ofDigits [0,1,1,0,1,0,0,0,1,0,1,0,1,1],
  ofDigits [0,1,1,0,0,1,1,0,0,0,1,0,1,1]]

def odd8 : List Nat := [
  ofDigits [1,1,1,1,0,1,0,1,1,0,0,0,0,0,0,1],
  ofDigits [0,0,0,1,0,0,1,1,0,0,1,0,1,1,1,1],
  ofDigits [1,0,1,0,0,0,1,1,1,0,1,1,0,0,0,1],
  ofDigits [0,0,0,0,0,1,0,1,0,1,1,1,0,1,1,1],
  ofDigits [0,1,1,1,1,1,1,1,0,0,0,1,0,0,0,0],
  ofDigits [0,1,1,1,0,1,1,1,1,0,1,0,0,0,0,0],
  ofDigits [0,0,0,0,0,0,1,1,0,1,0,1,1,1,1,1],
  ofDigits [1,0,1,0,0,0,1,1,0,1,1,0,0,1,0,1],
  ofDigits [1,0,1,0,0,1,0,0,1,1,1,1,0,0,0,1],
  ofDigits [0,1,0,1,1,0,1,0,0,0,1,1,1,0,1,0],
  ofDigits [1,0,1,0,0,0,1,0,1,0,1,1,0,1,0,1],
  ofDigits [0,0,0,0,1,0,0,1,1,0,0,1,1,1,1,1],
  ofDigits [1,0,1,0,0,1,1,0,1,1,0,1,0,0,0,1],
  ofDigits [0,0,0,1,0,0,1,0,0,0,1,1,1,1,1,1],
  ofDigits [0,0,1,0,0,0,0,1,1,0,0,1,1,1,1,1],
  ofDigits [1,1,1,1,1,0,1,1,0,0,0,0,0,0,0,1],
  ofDigits [1,1,1,1,1,1,1,0,0,0,0,0,0,0,0,1],
  ofDigits [0,0,0,1,0,0,0,1,1,0,1,1,0,1,1,1],
  ofDigits [0,1,1,1,0,1,0,1,1,0,1,0,1,0,0,0],
  ofDigits [0,1,1,1,1,1,0,1,1,0,1,0,0,0,0,0],
  ofDigits [0,0,0,1,0,1,0,0,0,1,1,0,1,1,1,1],
  ofDigits [0,1,1,1,1,1,1,1,0,1,0,0,0,0,0,0],
  ofDigits [1,1,0,1,0,1,0,1,1,0,1,0,0,0,0,1],
  ofDigits [0,1,1,1,0,1,0,1,1,0,1,0,0,0,1,0],
  ofDigits [1,0,1,0,1,0,0,1,1,0,0,1,0,1,0,1],
  ofDigits [0,0,0,0,0,1,1,1,0,0,0,1,1,1,1,1],
  ofDigits [0,0,0,0,0,1,1,0,1,1,0,0,1,1,1,1],
  ofDigits [1,1,1,1,0,1,0,1,0,0,1,0,0,0,0,1],
  ofDigits [1,1,1,0,1,1,1,1,0,0,0,0,0,0,0,1],
  ofDigits [1,0,1,1,1,1,1,1,0,0,0,0,0,0,0,1],
  ofDigits [0,1,0,1,1,0,0,0,1,1,0,1,1,0,1,0]]

theorem odd_family_7 : odd7.length = 23 ∧ oddFamily 14 7 odd7 = true := by decide +kernel
theorem odd_family_8 : odd8.length = 31 ∧ oddFamily 16 8 odd8 = true := by decide +kernel

/-! ## Words over d letters: block families -/

def countLetter (c : Nat) : List Nat → Nat
  | [] => 0
  | x :: xs => (if x == c then 1 else 0) + countLetter c xs

/-- number of common edges of two monotone paths in Z^d; `p`, `q` are the reversed prefixes -/
def commonD (d : Nat) : List Nat → List Nat → List Nat → List Nat → Nat
  | x :: xs, y :: ys, p, q =>
    (if x == y && (List.range d).all (fun c => countLetter c p == countLetter c q) then 1 else 0) +
      commonD d xs ys (x :: p) (y :: q)
  | _, _, _, _ => 0

/-- the d blocks ab, ba for the pairs of letters {2j, 2j+1}, and cc for the last letter when d is odd -/
def blocks (d : Nat) : List (List Nat) :=
  ((List.range (d / 2)).map fun j => [2 * j, 2 * j + 1]) ++
  ((List.range (d / 2)).map fun j => [2 * j + 1, 2 * j]) ++
  (if d % 2 == 1 then [[d - 1, d - 1]] else [])

def blockWords (d : Nat) : Nat → List (List Nat)
  | 0 => [[]]
  | r + 1 => (blocks d).flatMap fun b => (blockWords d r).map fun w => b ++ w

/-- the d^r concatenations of r blocks pairwise share an even number of edges -/
def blockFamilyOK (d r : Nat) : Bool :=
  (blockWords d r).length == d ^ r &&
    pairwise (fun x y => x != y && commonD d x y [] [] % 2 == 0) (blockWords d r)

theorem block_families_dim3 : [1, 2, 3].all (fun r => blockFamilyOK 3 r) = true := by decide +kernel
theorem block_families_dim4 : [1, 2, 3].all (fun r => blockFamilyOK 4 r) = true := by decide +kernel
theorem block_families_dim5 : [1, 2].all (fun r => blockFamilyOK 5 r) = true := by decide +kernel

#print axioms three_rows_even
#print axioms square_odd
#print axioms odd_family_7
#print axioms odd_family_8
#print axioms block_families_dim3
#print axioms block_families_dim4
#print axioms block_families_dim5
