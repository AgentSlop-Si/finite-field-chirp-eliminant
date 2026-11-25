/-
  FiniteFieldChirpEliminant.lean

  Zero-dependency Lean 4 formal verification companion to:
  "A Nonvanishing Phase Eliminant for Exact Finite-Field Chirp Recognition"
  by Daniyar Kuttymbek, Adilkhan Kuttymbek, Dayana Kuttymbek,
  Amina Kolpenova, and Mukhammadali Kottumbekov.

  Uses Lean 4 core (`Init`) only -- no Mathlib or external dependencies required.
  Verify with: `lean FiniteFieldChirpEliminant.lean`

  Contents:
    Part 1: Symbolic proofs for Theorems 1.1, 1.3, and Proposition 6.1 (zero `sorry`):
      - Section 2 (Theorem 1.1): 2*f(d) = d*(d-1) >= 0 and d*(d-1) = 0 <-> d = 0 \/ d = 1.
      - Section 2: Exact permutation exponent identity 2*f(i-j) = i^2 + j^2 - 2ij - (i - j).
      - Section 2: Exact reversal degree sum 3 * sum_{i=0}^r 2*f(2i - r) = r*(r+1)*(r+2)
        (i.e. sum_{i=0}^r f(2i - r) = binom(r + 2, 3)) for ALL r : Nat.
      - Section 2, Eq. (2.1): Exact quadratic phase-cancellation identity
        a*(c + i - j)^2 - 2*a*f(i - j) = a*c^2 + a*(2c + 1)*(i - j) for ALL a, c, i, j : Int.
      - Section 1: Even-length half-phase absorption 2 | (j^2 - j) for ALL j : Int.
      - Section 5, Eq. (5.1): Blocked integer-binomial identity
        2*a*j = a*(a - 1) + (j + 1)*j - (a - j)*(a - j - 1) for ALL a, j : Int.
      - Section 6, Proposition 6.1(3): Even-length Gauss-row shift invariance mod 2q
        when A is odd and w0 === q (mod 2).
    Part 2: Pure-kernel finite certificates (`decide` / `decide +kernel`, zero `native_decide`):
      - Levinson predictor determinant vs. direct Leibniz determinant in F_p[z]/(z^{D+1})
        across r in {1, 2} and p in {2, 5, 7, 17}, plus true-phase root verification.
      - Exhaustive exact recognition & dense DFT check across ALL 625 vectors of F_5^4
        (N = 4, p = 5, omega = 2, r = 1; 33 accepted vectors).
      - Complete Gauss-row reduction (Proposition 6.1) verified against direct summation
        across ALL phases 0 <= a < N for N in {3, 4, 5, 6, 8, 9, 10, 12}.
-/

namespace FiniteFieldChirpEliminant

/-! ## Part 1: Symbolic Proofs -/

/-- Section 2 (Theorem 1.1): For every integer `d`, `2 * f(d) = d * (d - 1) ≥ 0`,
    and `d * (d - 1) = 0 ↔ d = 0 ∨ d = 1` (so `A(0)` is lower bidiagonal with diagonal `x_c`). -/
theorem f_nonneg_and_zero_iff (d : Int) :
    0 ≤ d * (d - 1) ∧ (d * (d - 1) = 0 ↔ d = 0 ∨ d = 1) := by
  constructor
  · by_cases h1 : 1 ≤ d
    · exact Int.mul_nonneg (by omega) (by omega)
    · by_cases h0 : d ≤ 0
      · have hneg : (0 - d) * (1 - d) ≥ 0 := Int.mul_nonneg (by omega) (by omega)
        have heq : d * (d - 1) = (0 - d) * (1 - d) := by
          rw [Int.mul_sub, Int.sub_mul, Int.zero_mul, Int.mul_sub, Int.mul_one]
          omega
        omega
      · omega
  · constructor
    · intro hzero
      by_cases hd0 : d = 0
      · exact Or.inl hd0
      · by_cases hd1 : d = 1
        · exact Or.inr hd1
        · exfalso
          by_cases hgt : 2 ≤ d
          · have : 2 * 1 ≤ d * (d - 1) := Int.mul_le_mul hgt (by omega) (by omega) (by omega)
            omega
          · have hlt : d ≤ -1 := by omega
            have : (0 - d) * (1 - d) ≥ 1 * 2 :=
              Int.mul_le_mul (by omega) (by omega) (by omega) (by omega)
            have heq : d * (d - 1) = (0 - d) * (1 - d) := by
              rw [Int.mul_sub, Int.sub_mul, Int.zero_mul, Int.mul_sub, Int.mul_one]
              omega
            omega
    · intro h
      rcases h with rfl | rfl <;> decide

/-- Section 2: Exact expansion `2 * f(i - j) = (i^2 + j^2 - 2ij) - (i - j)`. -/
theorem f_pair_identity (i j : Int) :
    (i - j) * (i - j - 1) = i * i + j * j - 2 * (i * j) - (i - j) := by
  rw [Int.mul_sub, Int.mul_one, Int.sub_mul, Int.mul_sub, Int.mul_sub]
  have hc : j * i = i * j := Int.mul_comm j i
  omega

/-- Section 2: Exact reversal-permutation exponent sum `revSum2 r = ∑_{i=0}^r 2 f(2i - r)`
    satisfies `3 * revSum2 r = r * (r + 1) * (r + 2)` (i.e. `∑ f(2i - r) = C(r + 2, 3)`)
    for EVERY `r : Nat`. -/
def revSum2Aux (r : Nat) : Nat → Int
  | 0 => (-(r : Int)) * (-(r : Int) - 1)
  | k + 1 => revSum2Aux r k + (2 * ((k + 1 : Nat) : Int) - (r : Int)) * (2 * ((k + 1 : Nat) : Int) - (r : Int) - 1)

def revSum2 (r : Nat) : Int := revSum2Aux r r

theorem revSum2Aux_shift (r : Nat) :
    ∀ k : Nat, revSum2Aux (r + 2) (k + 1) = revSum2Aux r k + ((r : Int) + 2) * ((r : Int) + 3) := by
  intro k
  induction k with
  | zero =>
    unfold revSum2Aux
    unfold revSum2Aux
    have h0 : (-((r + 2 : Nat) : Int)) * (-((r + 2 : Nat) : Int) - 1) = ((r : Int) + 2) * ((r : Int) + 3) := by
      have hc : ((r + 2 : Nat) : Int) = (r : Int) + 2 := by omega
      rw [hc]
      have hs : -((r : Int) + 2) - 1 = -((r : Int) + 3) := by omega
      calc (-((r : Int) + 2)) * (-((r : Int) + 2) - 1)
        _ = (-((r : Int) + 2)) * (-((r : Int) + 3)) := by rw [hs]
        _ = ((r : Int) + 2) * ((r : Int) + 3) := Int.neg_mul_neg _ _
    have h1 : (2 * ((0 + 1 : Nat) : Int) - ((r + 2 : Nat) : Int)) = -(r : Int) := by omega
    rw [h0, h1]
    omega
  | succ k' ih =>
    change revSum2Aux (r + 2) (k' + 1) +
           (2 * ((k' + 2 : Nat) : Int) - ((r + 2 : Nat) : Int)) *
           (2 * ((k' + 2 : Nat) : Int) - ((r + 2 : Nat) : Int) - 1)
         = (revSum2Aux r k' +
           (2 * ((k' + 1 : Nat) : Int) - (r : Int)) *
           (2 * ((k' + 1 : Nat) : Int) - (r : Int) - 1)) +
           ((r : Int) + 2) * ((r : Int) + 3)
    rw [ih]
    have harg : (2 * ((k' + 2 : Nat) : Int) - ((r + 2 : Nat) : Int))
              = (2 * ((k' + 1 : Nat) : Int) - (r : Int)) := by omega
    rw [harg]
    omega

theorem revSum2_step (r : Nat) :
    revSum2 (r + 2) = revSum2 r + 2 * ((r : Int) + 2) * ((r : Int) + 2) := by
  unfold revSum2
  change revSum2Aux (r + 2) (r + 1) +
         (2 * ((r + 2 : Nat) : Int) - ((r + 2 : Nat) : Int)) *
         (2 * ((r + 2 : Nat) : Int) - ((r + 2 : Nat) : Int) - 1)
       = revSum2Aux r r + 2 * ((r : Int) + 2) * ((r : Int) + 2)
  rw [revSum2Aux_shift r r]
  have harg : 2 * ((r + 2 : Nat) : Int) - ((r + 2 : Nat) : Int) = (r : Int) + 2 := by omega
  rw [harg]
  have hexp : ((r : Int) + 2) * ((r : Int) + 3) + ((r : Int) + 2) * (((r : Int) + 2) - 1)
            = 2 * ((r : Int) + 2) * ((r : Int) + 2) := by
    rw [← Int.mul_add]
    have hsum : ((r : Int) + 3) + (((r : Int) + 2) - 1) = 2 * ((r : Int) + 2) := by omega
    rw [hsum]
    ac_rfl
  omega

theorem reversal_degree_closed_form :
    ∀ r : Nat, 3 * revSum2 r = (r : Int) * ((r : Int) + 1) * ((r : Int) + 2) := by
  intro r
  suffices h : ∀ n : Nat,
      3 * revSum2 n = (n : Int) * ((n : Int) + 1) * ((n : Int) + 2) ∧
      3 * revSum2 (n + 1) = ((n + 1 : Nat) : Int) * (((n + 1 : Nat) : Int) + 1) * (((n + 1 : Nat) : Int) + 2) from
    (h r).1
  intro n
  induction n with
  | zero =>
    constructor <;> decide
  | succ k ih =>
    refine ⟨ih.2, ?_⟩
    rw [revSum2_step k]
    have hprev := ih.1
    have hc : ((k + 2 : Nat) : Int) = (k : Int) + 2 := by omega
    rw [hc]
    generalize (k : Int) = x at hprev ⊢
    have h1 : 3 * (revSum2 k + 2 * (x + 2) * (x + 2))
            = x * (x + 1) * (x + 2) + 6 * ((x + 2) * (x + 2)) := by
      have : 3 * (2 * (x + 2) * (x + 2)) = 6 * ((x + 2) * (x + 2)) := by
        calc 3 * (2 * (x + 2) * (x + 2)) = (3 * 2) * ((x + 2) * (x + 2)) := by ac_rfl
          _ = 6 * ((x + 2) * (x + 2)) := rfl
      omega
    have h2 : (x + 2) * (x + 2 + 1) * (x + 2 + 2)
            = x * (x + 1) * (x + 2) + 6 * ((x + 2) * (x + 2)) := by
      have a : (x + 2) * (x + 2 + 1) * (x + 2 + 2) = (x + 2) * ((x + 3) * (x + 4)) := by
        have e1 : x + 2 + 1 = x + 3 := by omega
        have e2 : x + 2 + 2 = x + 4 := by omega
        rw [e1, e2]; ac_rfl
      have b : x * (x + 1) * (x + 2) + 6 * ((x + 2) * (x + 2))
             = (x + 2) * (x * (x + 1) + 6 * (x + 2)) := by
        have p1 : x * (x + 1) * (x + 2) = (x + 2) * (x * (x + 1)) := by ac_rfl
        have p2 : 6 * ((x + 2) * (x + 2)) = (x + 2) * (6 * (x + 2)) := by ac_rfl
        rw [p1, p2, ← Int.mul_add]
      have c : (x + 3) * (x + 4) = x * (x + 1) + 6 * (x + 2) := by
        rw [Int.add_mul, Int.mul_add, Int.mul_add, Int.mul_add, Int.mul_add]
        omega
      rw [a, b, c]
    rw [h1, h2]

/-- Section 2, Eq. (2.1): Exact quadratic phase-cancellation identity for ALL `a, c, i, j : Int`:
    evaluating `x_{c+i-j} z^{f(i-j)}` at `z = ω^{-2a}` cancels `(i - j)^2` identically. -/
theorem chirp_factoring_exponent_identity (a c i j : Int) :
    a * ((c + (i - j)) * (c + (i - j))) - a * ((i - j) * ((i - j) - 1))
    = a * (c * c) + a * (2 * c + 1) * (i - j) := by
  generalize i - j = d
  have h1 : (c + d) * (c + d) - d * (d - 1) = c * c + (2 * c + 1) * d := by
    rw [Int.add_mul, Int.mul_add, Int.mul_add, Int.mul_sub, Int.mul_one, Int.add_mul, Int.one_mul]
    have hc : d * c = c * d := Int.mul_comm d c
    have h2 : 2 * c * d = c * d + c * d := by
      have : (2 : Int) * c = c + c := by omega
      rw [this, Int.add_mul]
    omega
  calc a * ((c + d) * (c + d)) - a * (d * (d - 1))
    _ = a * ((c + d) * (c + d) - d * (d - 1)) := (Int.mul_sub _ _ _).symm
    _ = a * (c * c + (2 * c + 1) * d) := by rw [h1]
    _ = a * (c * c) + a * ((2 * c + 1) * d) := Int.mul_add _ _ _
    _ = a * (c * c) + a * (2 * c + 1) * d := by rw [Int.mul_assoc]

/-- Section 1: Even-length half-phase absorption (`j^2 - j` is always even). -/
theorem even_N_phase_half_shift (j : Int) : (j * j - j) % 2 = 0 := by
  have hj : j % 2 = 0 ∨ j % 2 = 1 := by omega
  rcases hj with h0 | h1
  · have hsq : (j * j) % 2 = 0 := by rw [Int.mul_emod, h0]; rfl
    rw [Int.sub_emod, hsq, h0]; rfl
  · have hsq : (j * j) % 2 = 1 := by rw [Int.mul_emod, h1]; rfl
    rw [Int.sub_emod, hsq, h1]; rfl

/-- Section 5, Eq. (5.1): Exact blocked integer-binomial identity `aj = C(a,2) + C(j+1,2) - C(a-j,2)`
    (in denominator-free integer form, requiring no field halving). -/
theorem blocked_chirp_binomial_identity (a j : Int) :
    2 * (a * j) = a * (a - 1) + (j + 1) * j - (a - j) * (a - j - 1) := by
  rw [Int.mul_sub, Int.mul_one, Int.add_mul, Int.one_mul,
      Int.mul_sub, Int.mul_one, Int.sub_mul, Int.mul_sub, Int.mul_sub]
  have hc : j * a = a * j := Int.mul_comm j a
  omega

/-- Section 6, Proposition 6.1(3): Even-length Gauss-row shift invariance modulo `2q`:
    if `A` is odd and `w0 ≡ q (mod 2)`, then shifting `u ↦ u + q` leaves `A u^2 + w0 u`
    invariant modulo `2q`. -/
theorem gauss_even_shift_invariance (q A w0 u : Int)
    (hA : A % 2 = 1) (hw : (w0 - q) % 2 = 0) :
    ((A * ((u + q) * (u + q)) + w0 * (u + q)) - (A * (u * u) + w0 * u)) % (2 * q) = 0 := by
  have hdiff : (A * ((u + q) * (u + q)) + w0 * (u + q)) - (A * (u * u) + w0 * u)
             = q * (2 * A * u + (A * q + w0)) := by
    rw [Int.add_mul u q (u + q), Int.mul_add u u q, Int.mul_add q u q,
        Int.mul_add, Int.mul_add, Int.mul_add, Int.mul_add, Int.mul_add]
    have h1 : A * (u * q) = q * (A * u) := by ac_rfl
    have h2 : A * (q * u) = q * (A * u) := by ac_rfl
    have h3 : q * (2 * A * u) = q * (A * u) + q * (A * u) := by
      have : 2 * A * u = A * u + A * u := by
        have : (2 : Int) * A = A + A := by omega
        rw [this, Int.add_mul]
      rw [this, Int.mul_add]
    have h4 : A * (q * q) = q * (A * q) := by ac_rfl
    have h5 : w0 * q = q * w0 := Int.mul_comm w0 q
    rw [h1, h2, h3, h4, h5, Int.mul_add q (A * q) w0]
    omega
  have heven : (A * q + w0) % 2 = 0 := by
    have hq : q % 2 = 0 ∨ q % 2 = 1 := by omega
    rcases hq with hq0 | hq1
    · have hAq : (A * q) % 2 = 0 := by rw [Int.mul_emod, hA, hq0]; rfl
      have hw0 : w0 % 2 = 0 := by omega
      rw [Int.add_emod, hAq, hw0]; rfl
    · have hAq : (A * q) % 2 = 1 := by rw [Int.mul_emod, hA, hq1]; rfl
      have hw1 : w0 % 2 = 1 := by omega
      rw [Int.add_emod, hAq, hw1]; rfl
  have hdiv : ∃ k : Int, A * q + w0 = 2 * k := ⟨(A * q + w0) / 2, by omega⟩
  rcases hdiv with ⟨k, hk⟩
  rw [hdiff, hk]
  have hfac : q * (2 * A * u + 2 * k) = (2 * q) * (A * u + k) := by
    rw [Int.mul_add, Int.mul_add]
    have a : q * (2 * A * u) = 2 * q * (A * u) := by ac_rfl
    have b : q * (2 * k) = 2 * q * k := by ac_rfl
    rw [a, b]
  rw [hfac, Int.mul_emod_right]

/-! ## Part 2: Pure-Kernel Finite Certificates (`decide` / `decide +kernel`, zero `native_decide`) -/

def powMod (a n p : Nat) : Nat :=
  let rec go (fuel base exp acc : Nat) : Nat :=
    match fuel with
    | 0 => acc
    | f + 1 =>
      if exp == 0 then acc
      else
        let acc' := if exp % 2 == 1 then (acc * base) % p else acc
        go f ((base * base) % p) (exp / 2) acc'
  go 16 (a % p) n 1

/-- Truncated polynomial arithmetic in `F_p[z] / (z^lim)`. -/
def rAdd (p lim : Nat) (a b : List Nat) : List Nat :=
  (List.range lim).map fun i => (a.getD i 0 + b.getD i 0) % p

def rNeg (p lim : Nat) (a : List Nat) : List Nat :=
  (List.range lim).map fun i => (p - a.getD i 0 % p) % p

def rMul (p lim : Nat) (a b : List Nat) : List Nat :=
  (List.range lim).map fun k =>
    (List.range (k + 1)).foldl (fun acc i =>
      (acc + a.getD i 0 * b.getD (k - i) 0) % p) 0

def rInv (p lim : Nat) (e : List Nat) : List Nat :=
  let g0 := (List.range lim).map fun i => if i == 0 then powMod (e.getD 0 0) (p - 2) p else 0
  -- 4 Newton doublings reach precision 16 (more than enough for D+1 <= 11 at r <= 3)
  (List.range 4).foldl (fun g _ =>
    let eg := rMul p lim e g
    let twoMinus := (List.range lim).map fun i =>
      if i == 0 then (2 + p - eg.getD 0 0 % p) % p
      else (p - eg.getD i 0 % p) % p
    rMul p lim g twoMinus) g0

def fExpInt (d : Int) : Nat := (d * (d - 1) / 2).toNat

def polyEvalMod (p : Nat) (poly : List Nat) (x : Nat) : Nat :=
  poly.reverse.foldl (fun acc c => (acc * x + c) % p) 0

/-- Section 3 pivot-free Levinson eliminant in `F_p[z] / (z^{D+1})`. -/
def levinsonEliminant (p r c : Nat) (x : List Nat) : List Nat :=
  let D := r * (r + 1) * (r + 2) / 6
  let lim := D + 1
  let aPoly (d : Int) : List Nat :=
    let e := fExpInt d
    let idx := ((c : Int) + d).toNat
    (List.range lim).map fun i => if i == e then x.getD idx 0 % p else 0
  let oneR := (List.range lim).map fun i => if i == 0 then 1 else 0
  let a0 := aPoly 0
  let (_, _, _, detFinal) := (List.range r).foldl (fun (u, v, e, detAcc) kIdx =>
    let k := kIdx + 1
    let Ak := (List.range (k - 1)).foldl (fun acc jIdx =>
      let j := jIdx + 1
      rAdd p lim acc (rMul p lim (aPoly ((k - j : Nat) : Int)) (u.getD j []))) (aPoly (k : Int))
    let Bk := (List.range (k - 1)).foldl (fun acc jIdx =>
      let j : Nat := jIdx + 1
      rAdd p lim acc (rMul p lim (aPoly ((j : Int) - (k : Int))) (v.getD j []))) (aPoly (-(k : Int)))
    let eInv := rInv p lim e
    let alpha := rMul p lim (rNeg p lim Ak) eInv
    let beta := rMul p lim (rNeg p lim Bk) eInv
    let uNew := oneR :: ((List.range (k - 1)).map fun jIdx =>
      let j := jIdx + 1
      rAdd p lim (u.getD j []) (rMul p lim alpha (v.getD (k - j) []))) ++ [alpha]
    let vNew := oneR :: ((List.range (k - 1)).map fun jIdx =>
      let j := jIdx + 1
      rAdd p lim (v.getD j []) (rMul p lim beta (u.getD (k - j) []))) ++ [beta]
    let eNew := rAdd p lim e (rMul p lim alpha Bk)
    let detNew := rMul p lim detAcc eNew
    (uNew, vNew, eNew, detNew)) ([oneR], [oneR], a0, a0)
  detFinal

/-- Direct Leibniz determinant for `r = 1` (2x2) and `r = 2` (3x3) in `F_p[z]/(z^{D+1})`. -/
def leibnizEliminant (p r c : Nat) (x : List Nat) : List Nat :=
  let D := r * (r + 1) * (r + 2) / 6
  let lim := D + 1
  let perms : List (List Nat × Bool) :=
    if r == 1 then [([0, 1], true), ([1, 0], false)]
    else [([0, 1, 2], true), ([1, 2, 0], true), ([2, 0, 1], true),
          ([0, 2, 1], false), ([1, 0, 2], false), ([2, 1, 0], false)]
  perms.foldl (fun acc (perm, isEven) =>
    let (coeff, deg) := (List.range (r + 1)).foldl (fun (cf, dg) i =>
      let j := perm.getD i 0
      let d : Int := (i : Int) - (j : Int)
      let idx := ((c : Int) + d).toNat
      ((cf * x.getD idx 0) % p, dg + fExpInt d)) (if isEven then 1 else p - 1, 0)
    (List.range lim).map fun k =>
      if k == deg then (acc.getD k 0 + coeff) % p else acc.getD k 0) (List.replicate lim 0)

def checkLevinsonMatchesLeibniz (p r c : Nat) (x : List Nat) : Bool :=
  let e1 := levinsonEliminant p r c x
  let e2 := leibnizEliminant p r c x
  e1 == e2 && e1.getD 0 0 == powMod (x.getD c 0) (r + 1) p

/-- Pure-kernel verification of Levinson-vs.-Leibniz determinant, constant term `x_c^{r+1}`,
    and true-phase root vanishing across `r ∈ {1, 2}` and `p ∈ {2, 5, 7, 17}`. -/
theorem levinson_vs_leibniz_eliminant_small :
    checkLevinsonMatchesLeibniz 2 1 1 [1, 1, 0, 1] = true ∧
    checkLevinsonMatchesLeibniz 2 2 2 [1, 0, 1, 1, 0, 1, 1] = true ∧
    checkLevinsonMatchesLeibniz 5 1 1 [2, 3, 1, 4] = true ∧
    checkLevinsonMatchesLeibniz 7 2 2 [1, 3, 2, 5, 4, 6, 1] = true ∧
    checkLevinsonMatchesLeibniz 17 2 2 [3, 5, 2, 11, 7, 13, 4] = true ∧
    -- True chirp at N=8, p=17, w=2, a=3, freqs={1,6}, amps={5,11}: E(w^{-2a}) = 0!
    (let x := (List.range 8).map fun j =>
       (powMod 2 (3 * j * j) 17 * ((5 * powMod 2 j 17 + 11 * powMod 2 (6 * j) 17) % 17)) % 17
     let E := levinsonEliminant 17 2 2 x
     polyEvalMod 17 E (powMod 2 ((8 - (6 % 8)) % 8) 17) == 0 && E.getD 0 0 != 0) := by
  decide +kernel

/-- Exhaustive pure-kernel verification on ALL `5^4 = 625` vectors of `F_5^4`
    (`N = 4, p = 5, ω = 2, r = 1`): eliminant recognizer agrees 100% with the direct
    all-phase DFT oracle, accepts exactly 33 vectors, and matches the direct DFT via
    the Gauss-row formula on every accepted vector. -/
def gaussRowSmall (N a w p : Nat) : List Nat :=
  let a := a % N
  if a == 0 then (List.range N).map fun k => if k == 0 then N % p else 0
  else
    let d := Nat.gcd a N
    let m := N / d
    let A := a / d
    let xi := powMod w d p
    if m == 1 then (List.range N).map fun k => if k == 0 then N % p else 0
    else if m % 2 == 1 then
      let T0 := (List.range m).foldl (fun acc u => (acc + powMod xi (A * u * u) p) % p) 0
      let inv4A := ((List.range m).find? (fun t => ((4 * A) * t) % m == 1)).getD 0
      (List.range N).map fun k =>
        if k % d != 0 then 0
        else
          let wi := k / d
          let exp := (m - (wi * wi * inv4A) % m) % m
          (d * T0 % p * powMod xi exp p) % p
    else
      let q := m / 2
      let w0 := q % 2
      let Tw0 := (List.range m).foldl (fun acc u => (acc + powMod xi (A * u * u + w0 * u) p) % p) 0
      let invA := if q == 1 then 0 else ((List.range q).find? (fun t => (A * t) % q == 1)).getD 0
      (List.range N).map fun k =>
        if k % d != 0 then 0
        else
          let wi := k / d
          if wi % 2 != w0 then 0
          else
            let u := if q == 1 then 0 else (((wi - w0) / 2) * invA) % q
            let exp := (m - (A * u * u + w0 * u) % m) % m
            (d * Tw0 % p * powMod xi exp p) % p

def directDftMod (N w p : Nat) (x : List Nat) : List Nat :=
  (List.range N).map fun k =>
    (List.range N).foldl (fun acc j => (acc + x.getD j 0 * powMod w (k * j) p) % p) 0

def checkAll625_F5_4 : Nat × Bool :=
  (List.range 625).foldl (fun (accCnt, ok) code =>
    let x := [code % 5, (code / 5) % 5, (code / 25) % 5, (code / 125) % 5]
    -- Direct brute-force oracle for C_1 (N=4, L=2, w=2, p=5)
    let ora := [0, 1].any fun a =>
      let y := (List.range 4).map fun j => (x.getD j 0 * powMod 2 ((4 - (a * j * j) % 4) % 4) 5) % 5
      let nzFreqs := ((List.range 4).filter fun u =>
        let cf := (List.range 4).foldl (fun acc j =>
          (acc + y.getD j 0 * powMod 2 ((4 - (u * j) % 4) % 4) 5) % 5) 0
        cf != 0).length
      nzFreqs ≤ 1
    -- Eliminant-driven recognizer for r = 1
    let (recOk, dftOpt) :=
      if x.all (· == 0) then (true, some [0, 0, 0, 0])
      else
        match [1, 2].find? (fun c => x.getD c 0 != 0) with
        | none => (false, none)
        | some c =>
          let E := levinsonEliminant 5 1 c x
          -- eta = w^{-2} = 4 mod 5; phases a in {0, 1} give z = 1, 4
          let cands := [0, 1].filter fun a => polyEvalMod 5 E (if a == 0 then 1 else 4) == 0
          let found := cands.findSome? fun a =>
            let y := (List.range 4).map fun j => (x.getD j 0 * powMod 2 ((4 - (a * j * j) % 4) % 4) 5) % 5
            let y0 := y.getD 0 0
            if y0 == 0 then none
            else
              let lam := (y.getD 1 0 * powMod y0 3 5) % 5
              match [0, 1, 2, 3].find? (fun u => powMod 2 u 5 == lam) with
              | none => none
              | some u =>
                let synth := (List.range 4).map fun j => (y0 * powMod 2 (u * j) 5) % 5
                if synth == y then
                  let G := gaussRowSmall 4 a 2 5
                  some ((List.range 4).map fun k => (y0 * G.getD ((k + u) % 4) 0) % 5)
                else none
          match found with
          | none => (false, none)
          | some d => (true, some d)
    let dftOk := match dftOpt with
      | none => true
      | some d => d == directDftMod 4 2 5 x
    (accCnt + (if ora then 1 else 0), ok && (ora == recOk) && dftOk)) (0, true)

theorem exhaustive_chirp_recognition_F5_N4 : checkAll625_F5_4 = (33, true) := by
  decide +kernel

def checkGaussOrder (N p w : Nat) : Bool :=
  (List.range N).all fun a =>
    let fast := gaussRowSmall N a w p
    let direct := (List.range N).map fun k =>
      (List.range N).foldl (fun acc j => (acc + powMod w (a * j * j + k * j) p) % p) 0
    fast == direct

/-- Pure-kernel verification of Proposition 6.1 (all-length Gauss-row reduction) against direct
    summation across ALL phases `0 ≤ a < N` for `N ∈ {3, 4, 5, 6, 8, 9, 10, 12}`. -/
theorem gauss_row_exact_reduction_small :
    checkGaussOrder 3 7 2 = true ∧
    checkGaussOrder 4 5 2 = true ∧
    checkGaussOrder 5 11 4 = true ∧
    checkGaussOrder 6 7 3 = true ∧
    checkGaussOrder 8 17 2 = true ∧
    checkGaussOrder 9 19 4 = true ∧
    checkGaussOrder 10 11 2 = true ∧
    checkGaussOrder 12 13 2 = true := by
  decide +kernel

end FiniteFieldChirpEliminant
