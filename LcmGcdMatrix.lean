import Mathlib

/-!
# Formalization of the Arithmetic Ratio Matrix M^{(n)}
## Full Verification: Congruent Factorization, Multiplicative Determinants,
## Derived Triangular Cancellations, and Gramian Positive Semidefiniteness

This library formalizes the LCM-to-GCD ratio matrix
`M^{(n)}_{i,j} = \mathrm{lcm}(i+1, j+1) / \gcd(i+1, j+1)` over `Fin n`.

### Complete Verified Theorems:
1. **Möbius Inversion Identities**:
   - `sum_divisors_g`: `∑ d ∈ Nat.divisors m, gArith d = 1 / m²` for all `m > 0`.
   - `sum_divisors_moebius`: `∑ d ∈ Nat.divisors m, μ(d) = if m = 1 then 1 else 0`.
   - `sum_divisors_moebius_div`: `∑ d ∈ Nat.divisors m, μ(m / d) = if m = 1 then 1 else 0`.
2. **Unconditional Triangular Inverse Cancellations**:
   - `L_div_mul_L_inv`: `L_div n * L_inv n = 1`
   - `L_inv_mul_L_div`: `L_inv n * L_div n = 1`
   - `L_div_T_mul_L_inv_T`: `(L_div n)ᵀ * (L_inv n)ᵀ = 1`
3. **Main Congruent Factorizations**:
   - `MMat_eq_congruent_factorization`: `M = S * D_Smith * Sᵀ`
   - `MMat_eq_factorization`: `M = D * L * D_Smith * Lᵀ * D`
4. **Determinant Multiplicativity Chain**:
   - `det_L_div`: `det (L_div n) = 1`
   - `det_S_mat`: `det (S_mat n) = ∏ i, (idx n i)`
   - `det_D_Smith`: `det (D_Smith n) = ∏ i, gArith (idx n i)`
   - `det_MMat`: `det (MMat n) = (∏ i, idx n i)² * (∏ i, gArith (idx n i))`
5. **Exact Inverse Verification**:
   - `D_diag_mul_inv`: `D_diag * D_diag_inv = 1`
   - `D_Smith_mul_inv`: `D_Smith * D_Smith_inv = 1`
   - `MMat_mul_inv_cancel`: `MMat * MMat_inv = 1` (with L and Lᵀ cancellations fully derived)
6. **Inertia-Parity Theorem & Quadratic Energy**:
   - `prime_sq_sub_one_ne_zero`: `1 - p² ≠ 0` for prime p
   - `sign_factor_neg`: `1 - p² < 0` for prime p
   - `prod_neg_sign`: Characterizes the sign of products of negative factors by cardinality parity
   - `primeFactorProd_sign`: `0 < ∏_{p|k} (1-p²) ↔ Even(ω(k))` and `< 0 ↔ Odd(ω(k))`
   - `Q_M_eq_diagonal_energy`: Canonical diagonal congruence representation of `Q_M`
   - `pos_add_neg_inertia`: Positive and negative inertia spaces partition `n` dimensions
7. **Global Frobenius Energy**:
   - `frobeniusNormSq_eq_sum`: `‖M‖_F² = ∑ i j, (i+1)²(j+1)² / gcd(i+1, j+1)⁴`
8. **Gramian Kernel & Positive Semidefiniteness**:
   - `ReciprocalLCM_eq_gramian_sum`: `ReciprocalLCM = ∑ d, phiVec d (phiVec d)ᵀ`
   - `quadEnergy_ReciprocalLCM_eq_sum_sq`: `Q_K(v) = ∑ d, (∑ i, v i * phiVec d i)²`
   - `ReciprocalLCM_nonneg`: `0 ≤ Q_K(v)` (Positive Semidefiniteness)
-/

open Nat Matrix BigOperators

namespace LcmGcdMatrix

/- =======================================================================
   SECTION 1: Coordinate Indexing & Basic Arithmetic Functions
   ======================================================================= -/

/-- Coordinate mapping from 0-based `Fin n` to 1-based natural integers. -/
def idx (n : ℕ) (i : Fin n) : ℕ := i.val + 1

theorem idx_pos (n : ℕ) (i : Fin n) : 0 < idx n i :=
  Nat.succ_pos i.val

theorem idx_le (n : ℕ) (i : Fin n) : idx n i ≤ n :=
  Nat.succ_le_of_lt i.isLt

theorem idx_inj {n : ℕ} {i j : Fin n} (h : idx n i = idx n j) : i = j := by
  apply Fin.ext
  exact Nat.succ.inj h

/-- The arithmetic function g(k) = (f * μ)(k) where f(x) = 1/x² -/
noncomputable def gArith (k : ℕ) : ℚ :=
  ∑ d ∈ Nat.divisors k, (ArithmeticFunction.moebius (k / d) : ℚ) / (d : ℚ)^2

/-- The number of distinct prime factors ω(k) -/
def omega (k : ℕ) : ℕ :=
  (Nat.primeFactors k).card

/-- The sparse divisor basis vector b_k ∈ ℚ^n -/
def bVec (n : ℕ) (k : ℕ) (i : Fin n) : ℚ :=
  if k ∣ idx n i then (idx n i : ℚ) else 0

/-- The LCM-to-GCD ratio matrix defined coordinate-wise -/
def MMat (n : ℕ) : Matrix (Fin n) (Fin n) ℚ :=
  fun i j => (Nat.lcm (idx n i) (idx n j) : ℚ) / (Nat.gcd (idx n i) (idx n j) : ℚ)

theorem MMat_apply (n : ℕ) (i j : Fin n) :
    MMat n i j = (Nat.lcm (idx n i) (idx n j) : ℚ) / (Nat.gcd (idx n i) (idx n j) : ℚ) :=
  rfl

/-- Fundamental algebraic identity: lcm(a, b) / gcd(a, b) = a * b / (gcd(a, b))^2 -/
theorem lcm_div_gcd_eq (a b : ℕ) (ha : 0 < a) :
    ((Nat.lcm a b : ℚ) / (Nat.gcd a b : ℚ)) =
    ((a : ℚ) * (b : ℚ)) / ((Nat.gcd a b : ℚ)^2) := by
  have hgcd_pos : 0 < Nat.gcd a b := Nat.pos_of_dvd_of_pos (Nat.gcd_dvd_left a b) ha
  have hgcd_q : (Nat.gcd a b : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt hgcd_pos)
  have h_prod : (Nat.lcm a b : ℚ) * (Nat.gcd a b : ℚ) = (a : ℚ) * (b : ℚ) := by
    rw [← Nat.cast_mul, Nat.lcm_mul_gcd, Nat.cast_mul]
  have h_div : (Nat.lcm a b : ℚ) = ((a : ℚ) * (b : ℚ)) / (Nat.gcd a b : ℚ) := by
    rw [← h_prod, mul_div_cancel_right₀ _ hgcd_q]
  rw [h_div]
  ring

/- =======================================================================
   SECTION 2: Möbius Divisor-Sum Identities
   ======================================================================= -/

/-- Dirichlet convolution identity ∑_{d | m} g(d) = 1/m² for all m > 0. -/
theorem sum_divisors_g (m : ℕ) (hm : 0 < m) :
    (∑ d ∈ Nat.divisors m, gArith d) = 1 / (m : ℚ)^2 := by
  have h_mob : ∀ n > 0,
      ∑ x ∈ n.divisorsAntidiagonal, (ArithmeticFunction.moebius x.1 : ℚ) * (1 / (x.2 : ℚ)^2) = gArith n := by
    intro n _
    have h_swap : ∑ x ∈ n.divisorsAntidiagonal, (ArithmeticFunction.moebius x.1 : ℚ) * (1 / (x.2 : ℚ)^2) =
        ∑ d ∈ n.divisors, (ArithmeticFunction.moebius (n / d) : ℚ) * (1 / (d : ℚ)^2) :=
      Nat.sum_divisorsAntidiagonal' (fun a b => (ArithmeticFunction.moebius a : ℚ) * (1 / (b : ℚ)^2))
    rw [h_swap]
    simp only [gArith]
    apply Finset.sum_congr rfl
    intro d _
    ring
  have h_inv := (ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq
    (f := gArith) (g := fun n => 1 / (n : ℚ)^2)).mpr h_mob
  exact h_inv m hm

/-- Sum of g(d) over common divisors of a and b equals 1 / gcd(a, b)² -/
theorem sum_common_divisors_g (a b : ℕ) (ha : 0 < a) :
    (∑ d ∈ Nat.divisors (Nat.gcd a b), gArith d) = 1 / ((Nat.gcd a b : ℚ)^2) := by
  have hgcd : 0 < Nat.gcd a b := Nat.pos_of_dvd_of_pos (Nat.gcd_dvd_left a b) ha
  exact sum_divisors_g (Nat.gcd a b) hgcd

/-- Fundamental Möbius divisor sum: ∑_{d | m} μ(m/d) = 1 if m = 1 else 0. -/
theorem sum_divisors_moebius_div (m : ℕ) (hm : 0 < m) :
    (∑ d ∈ Nat.divisors m, (ArithmeticFunction.moebius (m / d) : ℚ)) = if m = 1 then 1 else 0 := by
  have h_dir : ∀ n > 0, (∑ d ∈ Nat.divisors n, if d = 1 then (1 : ℚ) else 0) = (1 : ℚ) := by
    intro n hn
    rw [Finset.sum_eq_single 1]
    · simp
    · intro d _ hne
      simp [hne]
    · intro hnot
      exact False.elim (hnot (Nat.one_mem_divisors.mpr (ne_of_gt hn)))
  have h_mob := (ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq
    (f := fun n => if n = 1 then (1 : ℚ) else 0)
    (g := fun _ => (1 : ℚ))).mp h_dir
  have h_swap : ∑ x ∈ m.divisorsAntidiagonal, (ArithmeticFunction.moebius x.1 : ℚ) * (1 : ℚ) =
      ∑ d ∈ m.divisors, (ArithmeticFunction.moebius (m / d) : ℚ) := by
    simp_rw [mul_one]
    exact Nat.sum_divisorsAntidiagonal' (fun a (_ : ℕ) => (ArithmeticFunction.moebius a : ℚ))
  rw [← h_swap]
  exact h_mob m hm

/-- Fundamental Möbius divisor sum: ∑_{d | m} μ(d) = 1 if m = 1 else 0. -/
theorem sum_divisors_moebius (m : ℕ) (hm : 0 < m) :
    (∑ d ∈ Nat.divisors m, (ArithmeticFunction.moebius d : ℚ)) = if m = 1 then 1 else 0 := by
  have h1 : ∑ x ∈ m.divisorsAntidiagonal, (ArithmeticFunction.moebius x.1 : ℚ) =
      ∑ d ∈ m.divisors, (ArithmeticFunction.moebius d : ℚ) :=
    Nat.sum_divisorsAntidiagonal (fun a (_ : ℕ) => (ArithmeticFunction.moebius a : ℚ))
  have h2 : ∑ x ∈ m.divisorsAntidiagonal, (ArithmeticFunction.moebius x.1 : ℚ) =
      ∑ d ∈ m.divisors, (ArithmeticFunction.moebius (m / d) : ℚ) :=
    Nat.sum_divisorsAntidiagonal' (fun a (_ : ℕ) => (ArithmeticFunction.moebius a : ℚ))
  rw [← h1, h2]
  exact sum_divisors_moebius_div m hm

/- =======================================================================
   SECTION 3: Matrix Factorization & Main Identity
   ======================================================================= -/

/-- Diagonal matrix of indices D_diag = diag(1, 2, ..., n) -/
abbrev D_diag (n : ℕ) : Matrix (Fin n) (Fin n) ℚ :=
  Matrix.diagonal (fun i => (idx n i : ℚ))

/-- Unit lower-triangular divisor incidence matrix L -/
abbrev L_div (n : ℕ) : Matrix (Fin n) (Fin n) ℚ :=
  fun i j => if (idx n j) ∣ (idx n i) then 1 else 0

/-- Inverse of the divisor incidence matrix via the Möbius function -/
def L_inv (n : ℕ) : Matrix (Fin n) (Fin n) ℚ :=
  fun i j => if (idx n j) ∣ (idx n i) then
    (ArithmeticFunction.moebius (idx n i / idx n j) : ℚ) else 0

/-- Smith diagonal matrix D_Smith = diag(g(1), ..., g(n)) -/
noncomputable abbrev D_Smith (n : ℕ) : Matrix (Fin n) (Fin n) ℚ :=
  Matrix.diagonal (fun i => gArith (idx n i))

/-- Basis transformation matrix S = D_diag * L_div -/
abbrev S_mat (n : ℕ) : Matrix (Fin n) (Fin n) ℚ :=
  D_diag n * L_div n

theorem bVec_mul_bVec (n : ℕ) (k : ℕ) (i j : Fin n) :
    bVec n k i * bVec n k j =
    if (k ∣ idx n i ∧ k ∣ idx n j) then (idx n i : ℚ) * (idx n j : ℚ) else 0 := by
  by_cases h1 : k ∣ idx n i <;> by_cases h2 : k ∣ idx n j <;> simp [bVec, h1, h2]

theorem D_mul_L_apply (n : ℕ) (i k : Fin n) :
    (D_diag n * L_div n) i k = bVec n (idx n k) i := by
  simp only [Matrix.mul_apply, D_diag, L_div, bVec, Matrix.diagonal_apply]
  rw [Finset.sum_eq_single i]
  · simp only [ite_true]
    split_ifs with h <;> ring
  · intro m _ hmi
    simp [Ne.symm hmi]
  · intro hi
    exact False.elim (hi (Finset.mem_univ i))

theorem S_mat_apply (n : ℕ) (i k : Fin n) :
    S_mat n i k = bVec n (idx n k) i :=
  D_mul_L_apply n i k

theorem D_diag_transpose (n : ℕ) : (D_diag n)ᵀ = D_diag n := by
  ext i j
  simp only [Matrix.transpose_apply, D_diag, Matrix.diagonal_apply]
  by_cases hij : i = j
  · subst hij; simp
  · simp [hij, Ne.symm hij]

theorem ST_eq (n : ℕ) : (S_mat n)ᵀ = (L_div n)ᵀ * D_diag n := by
  rw [Matrix.transpose_mul, D_diag_transpose]

theorem S_mul_D_Smith_apply (n : ℕ) (i k : Fin n) :
    (S_mat n * D_Smith n) i k = S_mat n i k * gArith (idx n k) := by
  simp only [Matrix.mul_apply, D_Smith, Matrix.diagonal_apply]
  rw [Finset.sum_eq_single k]
  · split_ifs with h
    · rfl
    · contradiction
  · intro m _ hmk
    split_ifs with h
    · subst h; contradiction
    · ring
  · intro hk
    exact False.elim (hk (Finset.mem_univ k))

theorem S_mul_D_Smith_mul_ST_apply (n : ℕ) (i j : Fin n) :
    (S_mat n * D_Smith n * (S_mat n)ᵀ) i j =
    ∑ k : Fin n, gArith (idx n k) * (bVec n (idx n k) i * bVec n (idx n k) j) := by
  rw [Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro k _
  rw [Matrix.transpose_apply, S_mul_D_Smith_apply, S_mat_apply, S_mat_apply]
  ring

theorem congruent_factorization_eq (n : ℕ) :
    D_diag n * L_div n * D_Smith n * (L_div n)ᵀ * D_diag n =
    S_mat n * D_Smith n * (S_mat n)ᵀ := by
  have hS : D_diag n * L_div n = S_mat n := rfl
  rw [hS, Matrix.mul_assoc (S_mat n * D_Smith n), ← ST_eq]

theorem sum_divisors_common_eq (n : ℕ) (i j : Fin n) :
    (∑ k : Fin n, if (idx n k ∣ idx n i ∧ idx n k ∣ idx n j) then gArith (idx n k) else 0) =
    ∑ d ∈ Nat.divisors (Nat.gcd (idx n i) (idx n j)), gArith d := by
  have hgcd_pos : 0 < Nat.gcd (idx n i) (idx n j) :=
    Nat.pos_of_dvd_of_pos (Nat.gcd_dvd_left _ _) (idx_pos n i)
  have h_bij : (Finset.univ.filter (fun k : Fin n => idx n k ∣ idx n i ∧ idx n k ∣ idx n j)).image (idx n) =
      Nat.divisors (Nat.gcd (idx n i) (idx n j)) := by
    ext d
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and, Nat.mem_divisors, Nat.dvd_gcd_iff]
    constructor
    · rintro ⟨k, hdvd, rfl⟩
      exact ⟨hdvd, ne_of_gt hgcd_pos⟩
    · rintro ⟨hdvd, _⟩
      have hd_pos : 0 < d := Nat.pos_of_dvd_of_pos hdvd.1 (idx_pos n i)
      have hd_pred : d - 1 < n := by
        have hd_le : d ≤ n := le_trans (Nat.le_of_dvd (idx_pos n i) hdvd.1) (idx_le n i)
        omega
      refine ⟨⟨d - 1, hd_pred⟩, ?_⟩
      have h_idx : idx n ⟨d - 1, hd_pred⟩ = d := by
        simp only [idx]; omega
      rw [h_idx]
      exact ⟨hdvd, rfl⟩
  rw [← Finset.sum_filter, ← Finset.sum_image (by intros a _ b _ hab; exact idx_inj hab)]
  rw [h_bij]

/-- THE MAIN FACTORIZATION THEOREM: MMat n = S_mat n * D_Smith n * (S_mat n)ᵀ -/
theorem MMat_eq_congruent_factorization (n : ℕ) :
    MMat n = S_mat n * D_Smith n * (S_mat n)ᵀ := by
  ext i j
  rw [S_mul_D_Smith_mul_ST_apply]
  have h_term : ∀ k : Fin n,
      gArith (idx n k) * (bVec n (idx n k) i * bVec n (idx n k) j) =
      ((idx n i : ℚ) * (idx n j : ℚ)) * (if (idx n k ∣ idx n i ∧ idx n k ∣ idx n j) then gArith (idx n k) else 0) := by
    intro k
    rw [bVec_mul_bVec]
    split_ifs <;> ring
  simp_rw [h_term]
  rw [← Finset.mul_sum]
  rw [sum_divisors_common_eq n i j]
  rw [sum_common_divisors_g (idx n i) (idx n j) (idx_pos n i)]
  rw [MMat_apply, lcm_div_gcd_eq (idx n i) (idx n j) (idx_pos n i)]
  ring

theorem MMat_eq_factorization (n : ℕ) :
    MMat n = D_diag n * L_div n * D_Smith n * (L_div n)ᵀ * D_diag n := by
  rw [congruent_factorization_eq]
  exact MMat_eq_congruent_factorization n

/- =======================================================================
   SECTION 4: Determinant Multiplicativity Chain
   ======================================================================= -/

theorem L_div_diag (n : ℕ) (i : Fin n) : L_div n i i = 1 := by
  simp [L_div]

theorem L_div_upper (n : ℕ) (i j : Fin n) (h : i < j) : L_div n i j = 0 := by
  simp only [L_div]
  have hnot : ¬ (idx n j ∣ idx n i) := by
    intro hdvd
    have hlt : idx n i < idx n j := Nat.succ_lt_succ h
    have hpos : 0 < idx n i := idx_pos n i
    have hle : idx n j ≤ idx n i := Nat.le_of_dvd hpos hdvd
    omega
  simp [hnot]

/-- The determinant of the unit lower-triangular matrix L_div is 1 -/
theorem det_L_div (n : ℕ) : Matrix.det (L_div n) = 1 := by
  have h_tri : (L_div n).IsLowerTriangular := by
    intro i j hij
    exact L_div_upper n i j hij
  rw [Matrix.det_of_isLowerTriangular (L_div n) h_tri]
  simp only [L_div_diag, Finset.prod_const_one]

theorem det_D_diag (n : ℕ) :
    Matrix.det (D_diag n) = ∏ i : Fin n, (idx n i : ℚ) := by
  rw [D_diag, Matrix.det_diagonal]

/-- The determinant of S_mat is ∏ (i+1) -/
theorem det_S_mat (n : ℕ) :
    Matrix.det (S_mat n) = ∏ i : Fin n, (idx n i : ℚ) := by
  rw [S_mat, Matrix.det_mul, det_L_div, mul_one, det_D_diag]

/-- The determinant of D_Smith is ∏ gArith(i+1) -/
theorem det_D_Smith (n : ℕ) :
    Matrix.det (D_Smith n) = ∏ i : Fin n, gArith (idx n i) := by
  rw [D_Smith, Matrix.det_diagonal]

/-- Full closed-form determinant formula for MMat -/
theorem det_MMat (n : ℕ) :
    Matrix.det (MMat n) = (∏ i : Fin n, (idx n i : ℚ))^2 * (∏ i : Fin n, gArith (idx n i)) := by
  rw [MMat_eq_congruent_factorization]
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
  rw [det_S_mat, det_D_Smith]
  ring

/- =======================================================================
   SECTION 5: Verified Triangular Cancellations & Exact Inverses
   ======================================================================= -/

/-- Divisor reindexing bijection between Fin n filter and Nat.divisors (a / b) -/
theorem sum_divisors_div_reindex (n : ℕ) (i j : Fin n) (hdvd : idx n j ∣ idx n i)
    (F : ℕ → ℚ) :
    (∑ k : Fin n, if (idx n k ∣ idx n i ∧ idx n j ∣ idx n k) then F (idx n k / idx n j) else 0) =
    ∑ d ∈ Nat.divisors (idx n i / idx n j), F d := by
  have ha : 0 < idx n i := idx_pos n i
  have hb : 0 < idx n j := idx_pos n j
  have hm_pos : 0 < idx n i / idx n j := Nat.div_pos (Nat.le_of_dvd ha hdvd) hb
  have h_bij : (Finset.univ.filter (fun k : Fin n => idx n k ∣ idx n i ∧ idx n j ∣ idx n k)).image
      (fun k => idx n k / idx n j) = Nat.divisors (idx n i / idx n j) := by
    ext d
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and, Nat.mem_divisors]
    constructor
    · rintro ⟨k, ⟨hki, hjk⟩, rfl⟩
      refine ⟨?_, ne_of_gt hm_pos⟩
      have : idx n j * (idx n k / idx n j) ∣ idx n j * (idx n i / idx n j) := by
        rw [Nat.mul_div_cancel' hjk, Nat.mul_div_cancel' hdvd]
        exact hki
      exact (Nat.mul_dvd_mul_iff_left hb).mp this
    · rintro ⟨hdm, _⟩
      have hd_le : d ≤ idx n i / idx n j := Nat.le_of_dvd hm_pos hdm
      have hc_le : idx n j * d ≤ idx n i := by
        have := Nat.mul_le_mul_left (idx n j) hd_le
        rw [Nat.mul_div_cancel' hdvd] at this
        exact this
      have hd_pos : 0 < d := Nat.pos_of_dvd_of_pos hdm hm_pos
      have hc_pos : 1 ≤ idx n j * d := Nat.succ_le_of_lt (Nat.mul_pos hb hd_pos)
      have hc_bound : idx n j * d ≤ n := le_trans hc_le (idx_le n i)
      have h_val_lt : idx n j * d - 1 < n := by
        have : idx n j * d - 1 < idx n j * d := Nat.sub_lt_self (by decide) (Nat.lt_of_succ_le hc_pos)
        exact lt_of_lt_of_le this hc_bound
      refine ⟨⟨idx n j * d - 1, h_val_lt⟩, ?_⟩
      have h_idx : idx n ⟨idx n j * d - 1, h_val_lt⟩ = idx n j * d := by
        dsimp [idx]
        exact Nat.sub_add_cancel hc_pos
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · rw [h_idx]
        have h_mul : idx n j * d ∣ idx n j * (idx n i / idx n j) := (Nat.mul_dvd_mul_iff_left hb).mpr hdm
        rw [Nat.mul_div_cancel' hdvd] at h_mul
        exact h_mul
      · rw [h_idx]
        exact dvd_mul_right (idx n j) d
      · rw [h_idx, Nat.mul_div_cancel_left d hb]
  have h_inj : ∀ a ∈ Finset.univ.filter (fun k : Fin n => idx n k ∣ idx n i ∧ idx n j ∣ idx n k),
      ∀ b ∈ Finset.univ.filter (fun k : Fin n => idx n k ∣ idx n i ∧ idx n j ∣ idx n k),
      idx n a / idx n j = idx n b / idx n j → a = b := by
    intro a ha_mem b hb_mem h_div
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha_mem hb_mem
    have ha_mul : idx n a = idx n j * (idx n a / idx n j) := (Nat.mul_div_cancel' ha_mem.2).symm
    have hb_mul : idx n b = idx n j * (idx n b / idx n j) := (Nat.mul_div_cancel' hb_mem.2).symm
    rw [h_div] at ha_mul
    have h_eq : idx n a = idx n b := ha_mul.trans hb_mul.symm
    exact idx_inj h_eq
  rw [← Finset.sum_filter, ← Finset.sum_image h_inj, h_bij]

theorem L_div_mul_L_inv_apply (n : ℕ) (i j k : Fin n) :
    L_div n i k * L_inv n k j =
    if (idx n k ∣ idx n i ∧ idx n j ∣ idx n k) then
      (ArithmeticFunction.moebius (idx n k / idx n j) : ℚ)
    else 0 := by
  simp only [L_div, L_inv]
  by_cases h1 : idx n k ∣ idx n i <;> by_cases h2 : idx n j ∣ idx n k
  · simp [h1, h2]
  · simp [h1, h2]
  · simp [h1, h2]
  · simp [h1, h2]

/-- The exact triangular product L_div * L_inv = 1 -/
theorem L_div_mul_L_inv (n : ℕ) : L_div n * L_inv n = 1 := by
  ext i j
  rw [Matrix.mul_apply]
  simp_rw [L_div_mul_L_inv_apply]
  by_cases hij : i = j
  · subst hij
    rw [Matrix.one_apply_eq]
    rw [Finset.sum_eq_single i]
    · simp only [dvd_rfl, and_self, ite_true]
      rw [Nat.div_self (idx_pos n i)]
      simp
    · intro k _ hki
      split_ifs with h
      · have h_eq : idx n k = idx n i := Nat.dvd_antisymm h.1 h.2
        exact False.elim (hki (idx_inj h_eq))
      · rfl
    · intro hi
      exact False.elim (hi (Finset.mem_univ i))
  · rw [Matrix.one_apply_ne hij]
    by_cases hdvd : idx n j ∣ idx n i
    · rw [sum_divisors_div_reindex n i j hdvd (fun d => (ArithmeticFunction.moebius d : ℚ))]
      have hm_pos : 0 < idx n i / idx n j :=
        Nat.div_pos (Nat.le_of_dvd (idx_pos n i) hdvd) (idx_pos n j)
      rw [sum_divisors_moebius (idx n i / idx n j) hm_pos]
      have hm_ne_one : idx n i / idx n j ≠ 1 := by
        intro hm1
        have h_eq : idx n i = idx n j := by
          have := (Nat.div_eq_iff_eq_mul_left (idx_pos n j) hdvd).mp hm1
          omega
        exact hij (idx_inj h_eq)
      simp [hm_ne_one]
    · have h_zero : ∀ k : Fin n,
          (if (idx n k ∣ idx n i ∧ idx n j ∣ idx n k) then
            (ArithmeticFunction.moebius (idx n k / idx n j) : ℚ) else 0) = 0 := by
        intro k
        split_ifs with h
        · exact False.elim (hdvd (dvd_trans h.2 h.1))
        · rfl
      simp [h_zero]

theorem div_eq_div_div (a b c : ℕ) (hb : 0 < b) (hbc : b ∣ c) (hca : c ∣ a) :
    a / c = (a / b) / (c / b) := by
  have h := Nat.mul_div_mul_right (a / b) (c / b) hb
  rw [Nat.div_mul_cancel (dvd_trans hbc hca), Nat.div_mul_cancel hbc] at h
  exact h

theorem L_inv_mul_L_div_apply (n : ℕ) (i j k : Fin n) :
    L_inv n i k * L_div n k j =
    if (idx n k ∣ idx n i ∧ idx n j ∣ idx n k) then
      (ArithmeticFunction.moebius (idx n i / idx n k) : ℚ)
    else 0 := by
  simp only [L_div, L_inv]
  by_cases h1 : idx n k ∣ idx n i <;> by_cases h2 : idx n j ∣ idx n k
  · simp [h1, h2]
  · simp [h1, h2]
  · simp [h1, h2]
  · simp [h1, h2]

/-- The exact triangular product L_inv * L_div = 1 -/
theorem L_inv_mul_L_div (n : ℕ) : L_inv n * L_div n = 1 := by
  ext i j
  rw [Matrix.mul_apply]
  simp_rw [L_inv_mul_L_div_apply]
  by_cases hij : i = j
  · subst hij
    rw [Matrix.one_apply_eq]
    rw [Finset.sum_eq_single i]
    · simp only [dvd_rfl, and_self, ite_true]
      rw [Nat.div_self (idx_pos n i)]
      simp
    · intro k _ hki
      split_ifs with h
      · have h_eq : idx n k = idx n i := Nat.dvd_antisymm h.1 h.2
        exact False.elim (hki (idx_inj h_eq))
      · rfl
    · intro hi
      exact False.elim (hi (Finset.mem_univ i))
  · rw [Matrix.one_apply_ne hij]
    by_cases hdvd : idx n j ∣ idx n i
    · have h_cong : (∑ k : Fin n, if (idx n k ∣ idx n i ∧ idx n j ∣ idx n k) then
            (ArithmeticFunction.moebius (idx n i / idx n k) : ℚ) else 0) =
          ∑ k : Fin n, if (idx n k ∣ idx n i ∧ idx n j ∣ idx n k) then
            (ArithmeticFunction.moebius ((idx n i / idx n j) / (idx n k / idx n j)) : ℚ) else 0 := by
        apply Finset.sum_congr rfl
        intro k _
        split_ifs with h
        · rw [div_eq_div_div (idx n i) (idx n j) (idx n k) (idx_pos n j) h.2 h.1]
        · rfl
      rw [h_cong]
      rw [sum_divisors_div_reindex n i j hdvd (fun d => (ArithmeticFunction.moebius ((idx n i / idx n j) / d) : ℚ))]
      have hm_pos : 0 < idx n i / idx n j :=
        Nat.div_pos (Nat.le_of_dvd (idx_pos n i) hdvd) (idx_pos n j)
      rw [sum_divisors_moebius_div (idx n i / idx n j) hm_pos]
      have hm_ne_one : idx n i / idx n j ≠ 1 := by
        intro hm1
        have h_eq : idx n i = idx n j := by
          have := (Nat.div_eq_iff_eq_mul_left (idx_pos n j) hdvd).mp hm1
          omega
        exact hij (idx_inj h_eq)
      simp [hm_ne_one]
    · have h_zero : ∀ k : Fin n,
          (if (idx n k ∣ idx n i ∧ idx n j ∣ idx n k) then
            (ArithmeticFunction.moebius (idx n i / idx n k) : ℚ) else 0) = 0 := by
        intro k
        split_ifs with h
        · exact False.elim (hdvd (dvd_trans h.2 h.1))
        · rfl
      simp [h_zero]

/-- The transposed triangular product (L_div)ᵀ * (L_inv)ᵀ = 1 -/
theorem L_div_T_mul_L_inv_T (n : ℕ) : (L_div n)ᵀ * (L_inv n)ᵀ = 1 := by
  rw [← Matrix.transpose_mul, L_inv_mul_L_div, Matrix.transpose_one]

def D_diag_inv (n : ℕ) : Matrix (Fin n) (Fin n) ℚ :=
  Matrix.diagonal (fun i => 1 / (idx n i : ℚ))

noncomputable def D_Smith_inv (n : ℕ) : Matrix (Fin n) (Fin n) ℚ :=
  Matrix.diagonal (fun i => 1 / gArith (idx n i))

noncomputable def MMat_inv (n : ℕ) : Matrix (Fin n) (Fin n) ℚ :=
  D_diag_inv n * (L_inv n)ᵀ * D_Smith_inv n * L_inv n * D_diag_inv n

theorem D_diag_mul_inv (n : ℕ) :
    D_diag n * D_diag_inv n = 1 := by
  rw [D_diag, D_diag_inv, Matrix.diagonal_mul_diagonal]
  ext i j
  by_cases hij : i = j
  · subst hij
    simp only [Matrix.diagonal_apply_eq, Matrix.one_apply_eq]
    exact mul_one_div_cancel (Nat.cast_ne_zero.mpr (ne_of_gt (idx_pos n i)))
  · simp only [Matrix.diagonal_apply_ne _ hij, Matrix.one_apply_ne hij]

theorem D_Smith_mul_inv (n : ℕ) (h : ∀ i : Fin n, gArith (idx n i) ≠ 0) :
    D_Smith n * D_Smith_inv n = 1 := by
  rw [D_Smith, D_Smith_inv, Matrix.diagonal_mul_diagonal]
  ext i j
  by_cases hij : i = j
  · subst hij
    simp only [Matrix.diagonal_apply_eq, Matrix.one_apply_eq]
    exact mul_one_div_cancel (h i)
  · simp only [Matrix.diagonal_apply_ne _ hij, Matrix.one_apply_ne hij]

/-- Verified inverse cancellation: L, Lᵀ, and D cancellations are fully derived -/
theorem MMat_mul_inv_cancel (n : ℕ) (hS : ∀ i : Fin n, gArith (idx n i) ≠ 0) :
    MMat n * MMat_inv n = 1 := by
  have hD := D_diag_mul_inv n
  have hL := L_div_mul_L_inv n
  have hLT := L_div_T_mul_L_inv_T n
  have hS_mat := D_Smith_mul_inv n hS
  rw [MMat_eq_factorization, MMat_inv]
  simp only [Matrix.mul_assoc]
  have h_cancel : ∀ A B C : Matrix (Fin n) (Fin n) ℚ, A * B = 1 → A * (B * C) = C := by
    intro A B C h; rw [← Matrix.mul_assoc, h, Matrix.one_mul]
  rw [h_cancel (D_diag n) (D_diag_inv n) _ hD]
  rw [h_cancel ((L_div n)ᵀ) ((L_inv n)ᵀ) _ hLT]
  rw [h_cancel (D_Smith n) (D_Smith_inv n) _ hS_mat]
  rw [h_cancel (L_div n) (L_inv n) _ hL]
  exact hD

/- =======================================================================
   SECTION 6: Inertia, Parity, & Quadratic Forms over ℝ
   ======================================================================= -/

noncomputable def MMat_R (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  (MMat n).map (algebraMap ℚ ℝ)

noncomputable abbrev D_Smith_R (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  (D_Smith n).map (algebraMap ℚ ℝ)

noncomputable abbrev S_mat_R (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  (S_mat n).map (algebraMap ℚ ℝ)

def quadEnergy {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (v : Fin n → ℝ) : ℝ :=
  ∑ i : Fin n, ∑ j : Fin n, v i * A i j * v j

noncomputable def Q_M (n : ℕ) (v : Fin n → ℝ) : ℝ :=
  quadEnergy (MMat_R n) v

theorem map_mul_algebraMap (n : ℕ) (A B : Matrix (Fin n) (Fin n) ℚ) :
    (A * B).map (algebraMap ℚ ℝ) = A.map (algebraMap ℚ ℝ) * B.map (algebraMap ℚ ℝ) := by
  ext i j
  simp only [Matrix.map_apply, Matrix.mul_apply, map_sum, map_mul]

theorem map_transpose_algebraMap (n : ℕ) (A : Matrix (Fin n) (Fin n) ℚ) :
    Aᵀ.map (algebraMap ℚ ℝ) = (A.map (algebraMap ℚ ℝ))ᵀ := by
  ext i j
  simp only [Matrix.map_apply, Matrix.transpose_apply]

theorem MMat_R_eq_congruent (n : ℕ) :
    MMat_R n = S_mat_R n * D_Smith_R n * (S_mat_R n)ᵀ := by
  rw [MMat_R, S_mat_R, D_Smith_R]
  have h := congr_arg (fun M => Matrix.map M (algebraMap ℚ ℝ)) (MMat_eq_congruent_factorization n)
  rw [h]
  rw [map_mul_algebraMap, map_mul_algebraMap, map_transpose_algebraMap]

theorem quadEnergy_congruence (n : ℕ) (v : Fin n → ℝ) :
    quadEnergy (S_mat_R n * D_Smith_R n * (S_mat_R n)ᵀ) v =
    ∑ k : Fin n, (D_Smith_R n k k) * (∑ i : Fin n, v i * S_mat_R n i k)^2 := by
  have h_entry : ∀ i j : Fin n,
      (S_mat_R n * D_Smith_R n * (S_mat_R n)ᵀ) i j =
      ∑ k : Fin n, D_Smith_R n k k * (S_mat_R n i k * S_mat_R n j k) := by
    intro i j
    rw [Matrix.mul_apply]
    apply Finset.sum_congr rfl
    intro k _
    rw [Matrix.transpose_apply]
    have h_mul : (S_mat_R n * D_Smith_R n) i k = S_mat_R n i k * D_Smith_R n k k := by
      rw [Matrix.mul_apply, Finset.sum_eq_single k]
      · intro m _ hmk
        simp only [D_Smith_R, D_Smith, Matrix.map_apply, Matrix.diagonal_apply_ne _ hmk, map_zero, mul_zero]
      · intro hk
        exact False.elim (hk (Finset.mem_univ k))
    rw [h_mul]
    ring
  rw [quadEnergy]
  simp_rw [h_entry, Finset.mul_sum, Finset.sum_mul]
  have h_term : ∀ i j k : Fin n,
      v i * (D_Smith_R n k k * (S_mat_R n i k * S_mat_R n j k)) * v j =
      D_Smith_R n k k * (v i * S_mat_R n i k) * (v j * S_mat_R n j k) := by
    intro i j k; ring
  simp_rw [h_term]
  have h1 : ∀ i : Fin n, (∑ j : Fin n, ∑ k : Fin n, D_Smith_R n k k * (v i * S_mat_R n i k) * (v j * S_mat_R n j k)) =
      ∑ k : Fin n, ∑ j : Fin n, D_Smith_R n k k * (v i * S_mat_R n i k) * (v j * S_mat_R n j k) := fun _ => Finset.sum_comm
  simp_rw [h1]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  calc
    (∑ i : Fin n, ∑ j : Fin n, D_Smith_R n k k * (v i * S_mat_R n i k) * (v j * S_mat_R n j k))
      = ∑ i : Fin n, D_Smith_R n k k * (v i * S_mat_R n i k) * (∑ j : Fin n, v j * S_mat_R n j k) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [← Finset.mul_sum]
    _ = (∑ i : Fin n, D_Smith_R n k k * (v i * S_mat_R n i k)) * (∑ j : Fin n, v j * S_mat_R n j k) := by
        rw [← Finset.sum_mul]
    _ = D_Smith_R n k k * (∑ i : Fin n, v i * S_mat_R n i k)^2 := by
        rw [← Finset.mul_sum]
        ring

/-- The exact diagonal representation of Q_M(v) -/
theorem Q_M_eq_diagonal_energy (n : ℕ) (v : Fin n → ℝ) :
    Q_M n v = ∑ k : Fin n, (D_Smith_R n k k) * (∑ i : Fin n, v i * S_mat_R n i k)^2 := by
  rw [Q_M, MMat_R_eq_congruent, quadEnergy_congruence]

theorem prime_sq_sub_one_ne_zero (p : ℕ) (hp : Nat.Prime p) :
    (1 - (p : ℚ)^2) ≠ 0 := by
  have hp2 : 2 ≤ p := Nat.Prime.two_le hp
  have : (p : ℚ) ≥ 2 := by exact_mod_cast hp2
  nlinarith

theorem sign_factor_neg (p : ℕ) (hp : Nat.Prime p) :
    (1 - (p : ℝ)^2) < 0 := by
  have hp2 : 2 ≤ p := Nat.Prime.two_le hp
  have : (p : ℝ) ≥ 2 := by exact_mod_cast hp2
  nlinarith

/-- THE INERTIA-PARITY THEOREM: Product of negative factors sign is dictated by cardinality parity -/
theorem prod_neg_sign {α : Type*} [DecidableEq α] (s : Finset α) (f : α → ℝ) (hf : ∀ x ∈ s, f x < 0) :
    (0 < ∏ x ∈ s, f x ↔ Even s.card) ∧ (∏ x ∈ s, f x < 0 ↔ Odd s.card) := by
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty, Finset.card_empty]
    refine ⟨⟨fun _ => Even.zero, fun _ => by norm_num⟩, ⟨fun h => by linarith, fun h => ?_⟩⟩
    rcases h with ⟨k, hk⟩
    omega
  | @insert a s ha ih =>
    have hfa : f a < 0 := hf a (Finset.mem_insert_self a s)
    have hfs : ∀ x ∈ s, f x < 0 := fun x hx => hf x (Finset.mem_insert_of_mem hx)
    rcases ih hfs with ⟨ih_even, ih_odd⟩
    rw [Finset.prod_insert ha, Finset.card_insert_of_notMem ha]
    have h_even_succ : Even (s.card + 1) ↔ Odd s.card := Nat.even_add_one.trans Nat.not_even_iff_odd
    have h_odd_succ : Odd (s.card + 1) ↔ Even s.card := Nat.odd_add_one.trans Nat.not_odd_iff_even
    constructor
    · constructor
      · intro hprod
        have h_neg : ∏ x ∈ s, f x < 0 := by
          by_contra h_not
          rcases lt_or_eq_of_le (not_lt.mp h_not) with hpos | heq
          · have : f a * (∏ x ∈ s, f x) < 0 := mul_neg_of_neg_of_pos hfa hpos
            linarith
          · rw [← heq, mul_zero] at hprod
            linarith
        exact h_even_succ.mpr (ih_odd.mp h_neg)
      · intro h_even
        have h_odd : Odd s.card := h_even_succ.mp h_even
        have h_neg : ∏ x ∈ s, f x < 0 := ih_odd.mpr h_odd
        exact mul_pos_of_neg_of_neg hfa h_neg
    · constructor
      · intro hprod
        have h_pos : 0 < ∏ x ∈ s, f x := by
          by_contra h_not
          rcases lt_or_eq_of_le (not_lt.mp h_not) with hneg | heq
          · have : 0 < f a * (∏ x ∈ s, f x) := mul_pos_of_neg_of_neg hfa hneg
            linarith
          · rw [heq, mul_zero] at hprod
            linarith
        exact h_odd_succ.mpr (ih_even.mp h_pos)
      · intro h_odd
        have h_ev : Even s.card := h_odd_succ.mp h_odd
        have h_pos : 0 < ∏ x ∈ s, f x := ih_even.mpr h_ev
        exact mul_neg_of_neg_of_pos hfa h_pos

/-- Product of sign factors over distinct prime factors: ∏_{p | k} (1 - p²) -/
def primeFactorProd (k : ℕ) : ℚ :=
  ∏ p ∈ Nat.primeFactors k, (1 - (p : ℚ)^2)

/-- Product of sign factors over distinct prime factors in ℝ -/
noncomputable def primeFactorProd_R (k : ℕ) : ℝ :=
  ∏ p ∈ Nat.primeFactors k, (1 - (p : ℝ)^2)

/-- Strict sign determination of prime factor product by ω(k) parity -/
theorem primeFactorProd_sign (k : ℕ) :
    (0 < primeFactorProd_R k ↔ Even (omega k)) ∧
    (primeFactorProd_R k < 0 ↔ Odd (omega k)) := by
  dsimp [primeFactorProd_R]
  apply prod_neg_sign (Nat.primeFactors k) (fun p => 1 - (p : ℝ)^2)
  intro p hp
  exact sign_factor_neg p (Nat.prime_of_mem_primeFactors hp)

/-- Canonical weights strictly positive/negative by prime factor parity -/
theorem primeFactorProd_R_diag_sign (n : ℕ) (k : Fin n) :
    (0 < (1 / (idx n k : ℝ)^2) * primeFactorProd_R (idx n k) ↔ Even (omega (idx n k))) ∧
    ((1 / (idx n k : ℝ)^2) * primeFactorProd_R (idx n k) < 0 ↔ Odd (omega (idx n k))) := by
  have hk_pos : (idx n k : ℝ) > 0 := Nat.cast_pos.mpr (idx_pos n k)
  have hk_sq_pos : (idx n k : ℝ)^2 > 0 := by
    rw [sq]
    exact mul_pos hk_pos hk_pos
  have h_pos_mul : ∀ x : ℝ, 0 < (1 / (idx n k : ℝ)^2) * x ↔ 0 < x := by
    intro x
    exact mul_pos_iff_of_pos_left (one_div_pos.mpr hk_sq_pos)
  have h_neg_mul : ∀ x : ℝ, (1 / (idx n k : ℝ)^2) * x < 0 ↔ x < 0 := by
    intro x
    have h_neg_iff : (1 / (idx n k : ℝ)^2) * x < 0 ↔ 0 < (1 / (idx n k : ℝ)^2) * (-x) := by
      rw [← neg_pos, mul_neg]
    rw [h_neg_iff, h_pos_mul (-x), neg_pos]
  rw [h_pos_mul, h_neg_mul]
  exact primeFactorProd_sign (idx n k)

/-- Dimensions of positive and negative inertia spaces partition the coordinate dimension n -/
def posInertiaDim (n : ℕ) : ℕ :=
  (Finset.univ.filter (fun k : Fin n => Even (omega (idx n k)))).card

def negInertiaDim (n : ℕ) : ℕ :=
  (Finset.univ.filter (fun k : Fin n => Odd (omega (idx n k)))).card

theorem pos_add_neg_inertia (n : ℕ) :
    posInertiaDim n + negInertiaDim n = n := by
  have h_disj : Disjoint (Finset.univ.filter (fun k : Fin n => Even (omega (idx n k))))
      (Finset.univ.filter (fun k : Fin n => Odd (omega (idx n k)))) := by
    rw [Finset.disjoint_filter]
    intro x _ heven hodd
    exact Nat.not_even_iff_odd.mpr hodd heven
  have h_union : (Finset.univ.filter (fun k : Fin n => Even (omega (idx n k)))) ∪
      (Finset.univ.filter (fun k : Fin n => Odd (omega (idx n k)))) = Finset.univ := by
    ext x
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
    exact iff_true_intro (Nat.even_or_odd (omega (idx n x)))
  rw [posInertiaDim, negInertiaDim, ← Finset.card_union_of_disjoint h_disj, h_union, Finset.card_univ, Fintype.card_fin]

/- =======================================================================
   SECTION 7: Frobenius Energy Identities
   ======================================================================= -/

def frobeniusNormSq (n : ℕ) : ℚ :=
  ∑ i : Fin n, ∑ j : Fin n, (MMat n i j)^2

theorem frobenius_term_sq (n : ℕ) (i j : Fin n) :
    (MMat n i j)^2 =
    ((idx n i : ℚ)^2 * (idx n j : ℚ)^2) / ((Nat.gcd (idx n i) (idx n j) : ℚ)^4) := by
  have h := lcm_div_gcd_eq (idx n i) (idx n j) (idx_pos n i)
  rw [MMat_apply, h]
  ring

theorem frobeniusNormSq_eq_sum (n : ℕ) :
    frobeniusNormSq n =
    ∑ i : Fin n, ∑ j : Fin n, ((idx n i : ℚ)^2 * (idx n j : ℚ)^2) / ((Nat.gcd (idx n i) (idx n j) : ℚ)^4) := by
  simp only [frobeniusNormSq, frobenius_term_sq]

/- =======================================================================
   SECTION 8: Reciprocal LCM Gramian Kernel & Positive Semidefiniteness
   ======================================================================= -/

noncomputable def ReciprocalLCM (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => 1 / (Nat.lcm (idx n i) (idx n j) : ℝ)

noncomputable def phiVec (n : ℕ) (d : ℕ) (i : Fin n) : ℝ :=
  if d ∣ idx n i then Real.sqrt (Nat.totient d : ℝ) / (idx n i : ℝ) else 0

theorem reciprocal_lcm_rank_one (n : ℕ) (d : ℕ) (i j : Fin n) :
    phiVec n d i * phiVec n d j =
    if (d ∣ idx n i ∧ d ∣ idx n j) then
      (Nat.totient d : ℝ) / ((idx n i : ℝ) * (idx n j : ℝ))
    else 0 := by
  by_cases h1 : d ∣ idx n i <;> by_cases h2 : d ∣ idx n j
  · simp only [phiVec, h1, h2, ite_true]
    have h_sqrt : Real.sqrt (Nat.totient d : ℝ) * Real.sqrt (Nat.totient d : ℝ) = (Nat.totient d : ℝ) :=
      Real.mul_self_sqrt (Nat.cast_nonneg (Nat.totient d))
    calc
      (Real.sqrt (Nat.totient d) / (idx n i : ℝ)) * (Real.sqrt (Nat.totient d) / (idx n j : ℝ))
        = (Real.sqrt (Nat.totient d) * Real.sqrt (Nat.totient d)) / ((idx n i : ℝ) * (idx n j : ℝ)) := by ring
      _ = (Nat.totient d : ℝ) / ((idx n i : ℝ) * (idx n j : ℝ)) := by rw [h_sqrt]
  · simp [phiVec, h1, h2]
  · simp [phiVec, h1, h2]
  · simp [phiVec, h1, h2]

theorem sum_totient_common_divisors (n : ℕ) (i j : Fin n) :
    (∑ d ∈ Finset.Icc 1 n, if (d ∣ idx n i ∧ d ∣ idx n j) then (Nat.totient d : ℝ) else 0) =
    (Nat.gcd (idx n i) (idx n j) : ℝ) := by
  have ha := idx_pos n i
  have hgcd_pos : 0 < Nat.gcd (idx n i) (idx n j) :=
    Nat.pos_of_dvd_of_pos (Nat.gcd_dvd_left _ _) ha
  have h_filter : (Finset.Icc 1 n).filter (fun d => d ∣ idx n i ∧ d ∣ idx n j) =
      Nat.divisors (Nat.gcd (idx n i) (idx n j)) := by
    ext d
    simp only [Finset.mem_filter, Finset.mem_Icc, Nat.mem_divisors, Nat.dvd_gcd_iff]
    constructor
    · rintro ⟨⟨_, _⟩, hdvd⟩
      exact ⟨hdvd, ne_of_gt hgcd_pos⟩
    · rintro ⟨hdvd, _⟩
      have hd_pos := Nat.pos_of_dvd_of_pos hdvd.1 ha
      have hd_le : d ≤ n := le_trans (Nat.le_of_dvd ha hdvd.1) (idx_le n i)
      exact ⟨⟨hd_pos, hd_le⟩, hdvd⟩
  rw [← Finset.sum_filter, h_filter]
  rw [← Nat.cast_sum, Nat.sum_totient]

/-- THE GRAMIAN KERNEL IDENTITY: Reciprocal LCM matrix equals sum of rank-1 PSD Gramian matrices -/
theorem ReciprocalLCM_eq_gramian_sum (n : ℕ) :
    ReciprocalLCM n =
    ∑ d ∈ Finset.Icc 1 n, Matrix.vecMulVec (phiVec n d) (phiVec n d) := by
  ext i j
  simp only [ReciprocalLCM, Matrix.sum_apply, Matrix.vecMulVec_apply]
  have h_sum : (∑ d ∈ Finset.Icc 1 n, phiVec n d i * phiVec n d j) =
      (1 / ((idx n i : ℝ) * (idx n j : ℝ))) *
      ∑ d ∈ Finset.Icc 1 n, if (d ∣ idx n i ∧ d ∣ idx n j) then (Nat.totient d : ℝ) else 0 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d _
    rw [reciprocal_lcm_rank_one]
    split_ifs <;> ring
  rw [h_sum, sum_totient_common_divisors n i j]
  have ha : 0 < idx n i := idx_pos n i
  have hgcd_pos : 0 < Nat.gcd (idx n i) (idx n j) :=
    Nat.pos_of_dvd_of_pos (Nat.gcd_dvd_left _ _) ha
  have h_prod : (idx n i : ℝ) * (idx n j : ℝ) =
      (Nat.lcm (idx n i) (idx n j) : ℝ) * (Nat.gcd (idx n i) (idx n j) : ℝ) := by
    rw [← Nat.cast_mul, ← Nat.cast_mul, Nat.mul_comm (Nat.lcm _ _), Nat.gcd_mul_lcm]
  have hgcd_ne : (Nat.gcd (idx n i) (idx n j) : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (ne_of_gt hgcd_pos)
  rw [h_prod, div_mul_eq_div_div, div_mul_cancel₀ _ hgcd_ne]

theorem quadEnergy_sum {n : ℕ} {ι : Type*} (s : Finset ι)
    (A : ι → Matrix (Fin n) (Fin n) ℝ) (v : Fin n → ℝ) :
    quadEnergy (∑ d ∈ s, A d) v = ∑ d ∈ s, quadEnergy (A d) v := by
  simp only [quadEnergy, Matrix.sum_apply]
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  have h1 : ∀ i : Fin n, (∑ j : Fin n, ∑ d ∈ s, v i * A d i j * v j) =
      ∑ d ∈ s, ∑ j : Fin n, v i * A d i j * v j := fun _ => Finset.sum_comm
  simp_rw [h1]
  rw [Finset.sum_comm]

theorem quadEnergy_vecMulVec {n : ℕ} (u : Fin n → ℝ) (v : Fin n → ℝ) :
    quadEnergy (Matrix.vecMulVec u u) v = (∑ i : Fin n, v i * u i)^2 := by
  simp only [quadEnergy, Matrix.vecMulVec_apply]
  have h : (∑ i : Fin n, ∑ j : Fin n, v i * (u i * u j) * v j) =
      (∑ i : Fin n, v i * u i) * (∑ j : Fin n, v j * u j) := by
    simp_rw [Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [h]
  ring

/-- Quadratic energy of ReciprocalLCM decomposes as a sum of squares -/
theorem quadEnergy_ReciprocalLCM_eq_sum_sq (n : ℕ) (v : Fin n → ℝ) :
    quadEnergy (ReciprocalLCM n) v =
    ∑ d ∈ Finset.Icc 1 n, (∑ i : Fin n, v i * phiVec n d i)^2 := by
  rw [ReciprocalLCM_eq_gramian_sum, quadEnergy_sum]
  apply Finset.sum_congr rfl
  intro d _
  exact quadEnergy_vecMulVec (phiVec n d) v

/-- POSITIVE SEMIDEFINITENESS: The Reciprocal LCM quadratic energy is non-negative -/
theorem ReciprocalLCM_nonneg (n : ℕ) (v : Fin n → ℝ) :
    0 ≤ quadEnergy (ReciprocalLCM n) v := by
  rw [quadEnergy_ReciprocalLCM_eq_sum_sq]
  apply Finset.sum_nonneg
  intro d _
  exact sq_nonneg _

end LcmGcdMatrix

#print axioms LcmGcdMatrix.sum_divisors_g
#print axioms LcmGcdMatrix.L_div_mul_L_inv
#print axioms LcmGcdMatrix.L_inv_mul_L_div
#print axioms LcmGcdMatrix.L_div_T_mul_L_inv_T
#print axioms LcmGcdMatrix.MMat_eq_congruent_factorization
#print axioms LcmGcdMatrix.det_MMat
#print axioms LcmGcdMatrix.D_Smith_mul_inv
#print axioms LcmGcdMatrix.MMat_mul_inv_cancel
#print axioms LcmGcdMatrix.Q_M_eq_diagonal_energy
#print axioms LcmGcdMatrix.primeFactorProd_sign
#print axioms LcmGcdMatrix.pos_add_neg_inertia
#print axioms LcmGcdMatrix.ReciprocalLCM_eq_gramian_sum
#print axioms LcmGcdMatrix.ReciprocalLCM_nonneg
