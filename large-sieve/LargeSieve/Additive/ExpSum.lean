/-
# Large Sieve Inequality — Attempt 8: Compiled results + creative attacks

Building on Attempts 1-7 plus three parallel child sessions, we compile
all sorry-free results and push toward a minimal sorry count.

Key achievements (all sorry-free):
- packing_bound (R ≤ δ⁻¹): via sorted fractional parts + telescoping
- large_sieve_bombieri: Bombieri 1965 version, N·δ⁻¹

The sharp Large Sieve constant (N-1+δ⁻¹) is NOT proved here: the naive
decomposition "diagonal ≤ δ⁻¹ + off-diagonal ≤ (N-1)" is incorrect
(counterexample: R=2, N=2, δ=0.001, α=(0,0.001), a=(1,1) gives off-diagonal
≈ 4 > 2 = (N-1)·∑|a|²), and the sharp bound requires a global argument
(Beurling–Selberg majorant / Montgomery–Vaughan duality) not available in
Mathlib. The final multiplicative large sieve instead routes through
Gallagher's 1967 argument (`Additive/Gallagher.lean`), which needs only the
sorry-free results in this file, so the sharp bound is never used.
-/

import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Data.Complex.BigOperators
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

open Complex Real Finset BigOperators Matrix MeasureTheory
open scoped ComplexOrder

noncomputable section

-- ============================================================
-- Definitions (shared with Attempt 5)
-- ============================================================

def e (x : ℝ) : ℂ := Complex.exp (2 * ↑Real.pi * ↑x * Complex.I)

theorem e_zero : e 0 = 1 := by unfold e; simp
theorem e_add (x y : ℝ) : e (x + y) = e x * e y := by
  unfold e; rw [← Complex.exp_add]; congr 1; push_cast; ring
theorem norm_e (x : ℝ) : ‖e x‖ = 1 := by
  unfold e; rw [Complex.norm_exp]
  simp [Complex.mul_re, Complex.I_re, Complex.I_im]
theorem e_ne_zero (x : ℝ) : e x ≠ 0 := by
  intro h; have := norm_e x; rw [h, norm_zero] at this; exact one_ne_zero this.symm
theorem e_neg (x : ℝ) : e (-x) = starRingEnd ℂ (e x) := by
  unfold e; rw [← Complex.exp_conj]; congr 1; apply Complex.ext
  · simp [Complex.conj_re, Complex.mul_re, Complex.I_re, Complex.I_im,
          Complex.ofReal_re, Complex.ofReal_im]
  · simp [Complex.conj_im, Complex.mul_im, Complex.I_re, Complex.I_im,
          Complex.ofReal_re, Complex.ofReal_im]

def fracDist (x : ℝ) : ℝ := |x - round x|

theorem fracDist_nonneg (x : ℝ) : 0 ≤ fracDist x := abs_nonneg _

theorem fracDist_le_half (x : ℝ) : fracDist x ≤ 1 / 2 := by
  unfold fracDist
  exact abs_sub_round x

def expSum (a : ℤ → ℂ) (M : ℤ) (N : ℕ) (α : ℝ) : ℂ :=
  ∑ n ∈ Finset.Icc (M + 1) (M + ↑N), a n * e (↑n * α)

-- ============================================================
-- Part 1: e(n) = 1 for integer n — periodicity
-- ============================================================

/-- e(n) = 1 for any integer n. This is the periodicity of e(x). -/
theorem e_int (n : ℤ) : e (↑n) = 1 := by
  unfold e
  have : (2 : ℂ) * ↑Real.pi * ↑(n : ℝ) * Complex.I = ↑n * (2 * ↑Real.pi * Complex.I) := by
    push_cast; ring
  rw [this]
  exact Complex.exp_int_mul_two_pi_mul_I n

-- ============================================================
-- Part 2: Orthogonality — ∫₀¹ e(k·x) dx = δ_{k,0}
-- ============================================================

/-- For integer k ≠ 0, the integral ∫₀¹ e(kx) dx = 0.
    This is the fundamental orthogonality of exponential functions. -/
theorem integral_e_int_ne_zero {k : ℤ} (hk : k ≠ 0) :
    ∫ x in (0:ℝ)..1, e (↑k * x) = 0 := by
  unfold e
  have hc : (2 * ↑Real.pi * (↑k : ℂ) * Complex.I) ≠ 0 := by
    apply mul_ne_zero
    apply mul_ne_zero
    apply mul_ne_zero
    · exact_mod_cast (two_ne_zero : (2:ℝ) ≠ 0)
    · exact_mod_cast Real.pi_ne_zero
    · exact_mod_cast hk
    · exact Complex.I_ne_zero
  have key : ∀ x : ℝ, (2 : ℂ) * ↑Real.pi * ↑(↑k * x) * Complex.I =
      (2 * ↑Real.pi * ↑k * Complex.I) * ↑x := by
    intro x; push_cast; ring
  simp_rw [key]
  rw [integral_exp_mul_complex hc]
  simp only [Complex.ofReal_one, mul_one, Complex.ofReal_zero, mul_zero]
  rw [Complex.exp_zero]
  have hperiod : Complex.exp (2 * ↑Real.pi * ↑k * Complex.I) =
      Complex.exp (↑k * (2 * ↑Real.pi * Complex.I)) := by
    congr 1; ring
  rw [hperiod, Complex.exp_int_mul_two_pi_mul_I]
  simp

/-- For k = 0, ∫₀¹ e(0·x) dx = 1. -/
theorem integral_e_zero : ∫ x in (0:ℝ)..1, e (0 * x) = 1 := by
  simp [e_zero, intervalIntegral.integral_const]

/-- Combined orthogonality statement. -/
theorem integral_e_int (k : ℤ) :
    ∫ x in (0:ℝ)..1, e (↑k * x) = if k = 0 then 1 else 0 := by
  split
  · next h => subst h; simp only [Int.cast_zero, zero_mul, e_zero,
      intervalIntegral.integral_const, sub_zero, one_smul]
  · next h => exact integral_e_int_ne_zero h

-- ============================================================
-- Part 3: Helpers from Attempt 5 (reproduced)
-- ============================================================

def gramEntry {R : ℕ} (α : Fin R → ℝ) (m n : ℤ) : ℂ :=
  ∑ r : Fin R, e ((↑n - ↑m) * α r)

theorem gramEntry_conj {R : ℕ} (α : Fin R → ℝ) (m n : ℤ) :
    gramEntry α n m = starRingEnd ℂ (gramEntry α m n) := by
  simp only [gramEntry, map_sum]
  congr 1; ext r
  have : (↑m - ↑n) * α r = -((↑n - ↑m) * α r) := by ring
  rw [this, e_neg]

theorem gramEntry_diag {R : ℕ} (α : Fin R → ℝ) (n : ℤ) :
    gramEntry α n n = ↑R := by
  simp [gramEntry, sub_self, e_zero]

theorem norm_sq_eq_re_conj_mul (z : ℂ) :
    ‖z‖ ^ 2 = (starRingEnd ℂ z * z).re := by
  rw [sq, Complex.norm_mul_self_eq_normSq, ← Complex.normSq_eq_conj_mul_self]
  simp [Complex.ofReal_re]

-- ============================================================
-- Part 4: Sum exchange — the key algebraic identity
-- ============================================================

/-- **Sum exchange identity**:
    ∑_r ‖S(α_r)‖² = re(∑_m ∑_n conj(aₘ)·aₙ · G(m,n))

    This is the fundamental identity connecting the exponential sum
    to the Gram matrix. It follows by expanding each ‖S(α_r)‖²,
    then exchanging the order of summation. -/
theorem large_sieve_sum_exchange
    {R : ℕ} (α : Fin R → ℝ) (a : ℤ → ℂ) (M : ℤ) (N : ℕ) :
    (∑ r : Fin R, ‖expSum a M N (α r)‖ ^ 2) =
      (∑ m ∈ Finset.Icc (M + 1) (M + ↑N),
        ∑ n ∈ Finset.Icc (M + 1) (M + ↑N),
          starRingEnd ℂ (a m) * a n * gramEntry α m n).re := by
  set S := Finset.Icc (M + 1) (M + ↑N)
  -- Step 1: Expand each ‖S(α_r)‖² using norm_sq_eq_re_conj_mul
  have step1 : ∀ r : Fin R,
      ‖expSum a M N (α r)‖ ^ 2 =
        (∑ m ∈ S, ∑ n ∈ S,
          starRingEnd ℂ (a m * e (↑m * α r)) * (a n * e (↑n * α r))).re := by
    intro r; unfold expSum
    rw [norm_sq_eq_re_conj_mul, map_sum, Finset.sum_mul]
    congr 1
    apply Finset.sum_congr rfl; intro m _
    rw [Finset.mul_sum]
  -- Step 2: Sum over r, pull re outside
  have step2 : (∑ r : Fin R, ‖expSum a M N (α r)‖ ^ 2) =
      (∑ r : Fin R, (∑ m ∈ S, ∑ n ∈ S,
        starRingEnd ℂ (a m * e (↑m * α r)) * (a n * e (↑n * α r))).re) := by
    apply Finset.sum_congr rfl; intro r _; exact step1 r
  rw [step2, ← Complex.re_sum]
  congr 1
  -- Step 3: Exchange sum over r with sums over m, n
  simp_rw [Finset.sum_comm (s := Finset.univ) (t := S)]
  apply Finset.sum_congr rfl; intro m _
  apply Finset.sum_congr rfl; intro n _
  -- Step 4: Factor out a_m, a_n from the sum over r
  simp only [map_mul]
  -- Each term: conj(a_m) · conj(e(m·α_r)) · (a_n · e(n·α_r))
  --          = conj(a_m) · a_n · e((n-m)·α_r)
  have term_eq : ∀ r : Fin R,
      starRingEnd ℂ (a m) * starRingEnd ℂ (e (↑m * α r)) * (a n * e (↑n * α r)) =
      starRingEnd ℂ (a m) * a n * e ((↑n - ↑m) * α r) := by
    intro r
    have he := (e_neg (↑m * α r)).symm
    have hadd : e (-(↑m * α r)) * e (↑n * α r) = e ((↑n - ↑m) * α r) := by
      rw [← e_add]; congr 1; ring
    calc starRingEnd ℂ (a m) * starRingEnd ℂ (e (↑m * α r)) * (a n * e (↑n * α r))
        = starRingEnd ℂ (a m) * e (-(↑m * α r)) * (a n * e (↑n * α r)) := by rw [he]
      _ = starRingEnd ℂ (a m) * a n * (e (-(↑m * α r)) * e (↑n * α r)) := by ring
      _ = starRingEnd ℂ (a m) * a n * e ((↑n - ↑m) * α r) := by rw [hadd]
  simp_rw [term_eq, gramEntry, ← Finset.mul_sum]

-- ============================================================
-- Part 5: R=1 and weak bound (from Attempt 5)
-- ============================================================

theorem large_sieve_R1
    (a : ℤ → ℂ) (M : ℤ) (N : ℕ) (α : ℝ) (hN : 0 < N) :
    ‖expSum a M N α‖ ^ 2 ≤
      ↑N * (∑ n ∈ Finset.Icc (M + 1) (M + ↑N), ‖a n‖ ^ 2) := by
  unfold expSum
  have hcard : (Finset.Icc (M + 1) (M + ↑N)).card = N := by
    rw [Int.card_Icc]; omega
  set S := Finset.Icc (M + 1) (M + ↑N)
  calc ‖∑ n ∈ S, a n * e (↑n * α)‖ ^ 2
      ≤ (∑ n ∈ S, ‖a n‖) ^ 2 := by
        gcongr
        calc ‖∑ n ∈ S, a n * e (↑n * α)‖
            ≤ ∑ n ∈ S, ‖a n * e (↑n * α)‖ := norm_sum_le S _
          _ = ∑ n ∈ S, ‖a n‖ := by
              apply Finset.sum_congr rfl; intro n _
              rw [norm_mul, norm_e, mul_one]
    _ ≤ (S.card : ℝ) * ∑ n ∈ S, ‖a n‖ ^ 2 := sq_sum_le_card_mul_sum_sq
    _ = ↑N * ∑ n ∈ S, ‖a n‖ ^ 2 := by congr 1; exact_mod_cast hcard

theorem large_sieve_weak
    {R : ℕ} (α : Fin R → ℝ) (a : ℤ → ℂ) (M : ℤ) (N : ℕ) (hN : 0 < N) :
    (∑ r : Fin R, ‖expSum a M N (α r)‖ ^ 2) ≤
      ↑R * (↑N * ∑ n ∈ Finset.Icc (M + 1) (M + ↑N), ‖a n‖ ^ 2) := by
  calc ∑ r : Fin R, ‖expSum a M N (α r)‖ ^ 2
      ≤ ∑ r : Fin R, (↑N * ∑ n ∈ Finset.Icc (M + 1) (M + ↑N), ‖a n‖ ^ 2) := by
        apply Finset.sum_le_sum; intro r _; exact large_sieve_R1 a M N (α r) hN
    _ = ↑R * (↑N * ∑ n ∈ Finset.Icc (M + 1) (M + ↑N), ‖a n‖ ^ 2) := by
        rw [Finset.sum_const, Finset.card_fin]; simp [nsmul_eq_mul]

-- ============================================================
-- Part 6: Parseval identity for trigonometric polynomials
-- ============================================================

/-- Each `fun x => e(k * x)` is continuous, hence interval integrable. -/
theorem continuous_e_mul (k : ℝ) : Continuous (fun x : ℝ => e (k * x)) := by
  unfold e
  apply Continuous.cexp
  apply Continuous.mul
  · apply Continuous.mul
    · exact continuous_const
    · exact Complex.continuous_ofReal.comp (continuous_const.mul continuous_id)
  · exact continuous_const

theorem intervalIntegrable_e_mul (k : ℝ) (a b : ℝ) :
    IntervalIntegrable (fun x => e (k * x)) MeasureTheory.volume a b :=
  (continuous_e_mul k).continuousOn.intervalIntegrable

/-- Cross-term integral: ∫₀¹ conj(e(mx))·e(nx) dx = δ_{m,n}.
    This is the orthonormality of the exponential system. -/
theorem cross_integral (m n : ℤ) :
    ∫ x in (0:ℝ)..1, starRingEnd ℂ (e (↑m * x)) * e (↑n * x) = if n = m then 1 else 0 := by
  -- conj(e(mx)) * e(nx) = e(-mx) * e(nx) = e((n-m)x)
  have key : ∀ x : ℝ, starRingEnd ℂ (e (↑m * x)) * e (↑n * x) = e ((↑n - ↑m) * x) := by
    intro x
    rw [← e_neg, ← e_add]
    congr 1; ring
  simp_rw [key]
  -- Now apply integral_e_int to n - m
  have : ∀ x : ℝ, e ((↑n - ↑m) * x) = e (↑(n - m) * x) := by
    intro x; congr 1; push_cast; ring
  simp_rw [this, integral_e_int]
  simp [sub_eq_zero]

/-- **Parseval's identity for trigonometric polynomials**:
    ∫₀¹ conj(T(x))·T(x) dx = ∑_{n∈S} conj(aₙ)·aₙ = ∑ |aₙ|²

    Proved sorry-free via product expansion + sum interchange + orthogonality
    (`cross_integral`, `integral_e_int`). -/
theorem parseval_trig_poly_complex (a : ℤ → ℂ) (S : Finset ℤ) :
    ∫ x in (0:ℝ)..1,
        starRingEnd ℂ (∑ n ∈ S, a n * e (↑n * x)) *
        (∑ n ∈ S, a n * e (↑n * x)) =
      ∑ n ∈ S, starRingEnd ℂ (a n) * a n := by
  -- Expand conj(∑) · ∑ = ∑_m ∑_n conj(a_m e(mx)) · a_n e(nx)
  simp_rw [map_sum, map_mul, Finset.sum_mul, Finset.mul_sum]
  -- Integrability of each cross-term
  have hint : ∀ (m n : ℤ),
      IntervalIntegrable (fun x => starRingEnd ℂ (a m) * starRingEnd ℂ (e (↑m * x)) *
        (a n * e (↑n * x))) MeasureTheory.volume 0 1 := by
    intro m n
    apply ContinuousOn.intervalIntegrable
    apply Continuous.continuousOn
    exact (continuous_const.mul (continuous_e_mul _).star).mul
      (continuous_const.mul (continuous_e_mul _))
  -- Continuity of each inner sum ∑_n f(m,n,x)
  have hcont_inner : ∀ m : ℤ, Continuous (fun x =>
      ∑ n ∈ S, starRingEnd ℂ (a m) * starRingEnd ℂ (e (↑m * x)) *
        (a n * e (↑n * x))) := by
    intro m; apply continuous_finsetSum; intro n _
    exact (continuous_const.mul (continuous_e_mul _).star).mul
      (continuous_const.mul (continuous_e_mul _))
  -- Swap integral and outer finite sum
  rw [intervalIntegral.integral_finsetSum (fun m _ =>
    (hcont_inner m).continuousOn.intervalIntegrable)]
  apply Finset.sum_congr rfl; intro m hm
  -- Swap integral and inner finite sum
  rw [intervalIntegral.integral_finsetSum (fun n _ => hint m n)]
  -- Factor out constants and apply cross_integral
  simp_rw [show ∀ n : ℤ, ∀ x : ℝ,
      starRingEnd ℂ (a m) * starRingEnd ℂ (e (↑m * x)) * (a n * e (↑n * x)) =
      (starRingEnd ℂ (a m) * a n) * (starRingEnd ℂ (e (↑m * x)) * e (↑n * x)) from
    fun n x => by ring]
  simp_rw [intervalIntegral.integral_const_mul, cross_integral]
  -- Now ∑_n conj(a_m) * a_n * (if n = m then 1 else 0)
  simp [Finset.sum_ite_eq', hm]

-- ============================================================
-- Part 7: Gram matrix diagonal dominance
-- ============================================================

/-- The off-diagonal Gram entries can be bounded:
    |G(m,n)| ≤ R for any m, n.
    (Trivial bound by triangle inequality) -/
theorem gramEntry_norm_le {R : ℕ} (α : Fin R → ℝ) (m n : ℤ) :
    ‖gramEntry α m n‖ ≤ ↑R := by
  unfold gramEntry
  calc ‖∑ r : Fin R, e ((↑n - ↑m) * α r)‖
      ≤ ∑ r : Fin R, ‖e ((↑n - ↑m) * α r)‖ := norm_sum_le _ _
    _ = ∑ r : Fin R, (1 : ℝ) := by
        apply Finset.sum_congr rfl; intro r _
        exact norm_e _
    _ = ↑R := by simp

-- ============================================================
-- Part 8: Sieve matrix + PSD (from Attempt 5)
-- ============================================================

def sieveMatrix {R : ℕ} (α : Fin R → ℝ) (S : Finset ℤ) : Matrix (Fin R) S ℂ :=
  Matrix.of fun r n => e (↑(n : ℤ) * α r)

theorem sieveMatrix_gram_posSemidef
    {R : ℕ} (α : Fin R → ℝ) (S : Finset ℤ) :
    ((sieveMatrix α S)ᴴ * sieveMatrix α S).PosSemidef :=
  Matrix.posSemidef_conjTranspose_mul_self _

theorem trace_sieveGram {R : ℕ} (α : Fin R → ℝ) (S : Finset ℤ) :
    ((sieveMatrix α S)ᴴ * sieveMatrix α S).trace = ↑(R * S.card) := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
    sieveMatrix, Matrix.conjTranspose_apply, Matrix.of_apply]
  rw [Finset.sum_comm]
  have : ∀ (n : ↥S) (r : Fin R),
      star (e (↑(n : ℤ) * α r)) * e (↑(n : ℤ) * α r) = 1 := by
    intro n r; rw [star_def, ← e_neg, ← e_add]; simp [e_zero]
  simp only [this, Finset.sum_const, Finset.card_fin, nsmul_eq_mul, mul_one]
  rw [Finset.card_univ, Fintype.card_coe]; push_cast; ring

-- ============================================================
-- Part 9: Norm-squared Parseval (ℝ-valued version)
-- ============================================================

/-- **Parseval norm-squared form**: ∫₀¹ ‖T(x)‖² dx = ∑_{n∈S} ‖aₙ‖².
    Follows from the complex form since ‖z‖² = re(conj(z)·z). -/
theorem parseval_trig_poly_norm (a : ℤ → ℂ) (S : Finset ℤ) :
    ∫ x in (0:ℝ)..1, ‖∑ n ∈ S, a n * e (↑n * x)‖ ^ 2 =
      ∑ n ∈ S, ‖a n‖ ^ 2 := by
  -- Step 1: ‖z‖² = re(conj(z) · z) pointwise
  have key : ∀ x : ℝ,
      (‖∑ n ∈ S, a n * e (↑n * x)‖ ^ 2 : ℝ) =
      (starRingEnd ℂ (∑ n ∈ S, a n * e (↑n * x)) *
        (∑ n ∈ S, a n * e (↑n * x))).re := by
    intro x; exact norm_sq_eq_re_conj_mul _
  simp_rw [key]
  -- Step 2: The ℂ-valued function conj(T)·T is continuous, hence integrable
  set T : ℝ → ℂ := fun x => ∑ n ∈ S, a n * e (↑n * x) with hT_def
  have hT_cont : Continuous T := continuous_finsetSum S (fun n _ =>
    continuous_const.mul (continuous_e_mul _))
  have hcT : Continuous (fun x => starRingEnd ℂ (T x) * T x) :=
    hT_cont.star.mul hT_cont
  have hint : IntervalIntegrable (fun x => starRingEnd ℂ (T x) * T x)
      MeasureTheory.volume (0:ℝ) 1 :=
    hcT.continuousOn.intervalIntegrable
  -- Step 3: ∫ re(f) = re(∫ f)
  rw [show (fun x => (starRingEnd ℂ (T x) * T x).re) =
      (fun x => RCLike.re (starRingEnd ℂ (T x) * T x)) from rfl]
  rw [intervalIntegral.intervalIntegral_re hint]
  -- Step 4: Apply complex Parseval
  rw [show ∫ x in (0:ℝ)..1, starRingEnd ℂ (T x) * T x =
      ∫ x in (0:ℝ)..1, starRingEnd ℂ (∑ n ∈ S, a n * e (↑n * x)) *
        (∑ n ∈ S, a n * e (↑n * x)) from rfl]
  rw [parseval_trig_poly_complex]
  -- Step 5: re(∑ conj(aₙ)·aₙ) = ∑ ‖aₙ‖²
  simp only [map_sum]
  congr 1; ext n
  exact (norm_sq_eq_re_conj_mul (a n)).symm

-- ============================================================
-- Part 9b: Derivative infrastructure (Gallagher approach)
-- ============================================================

/-- The derivative of e(k·x) w.r.t. x is 2πik · e(k·x). -/
theorem hasDerivAt_e_mul (k : ℝ) (x : ℝ) :
    HasDerivAt (fun x => e (k * x)) (2 * ↑Real.pi * ↑k * Complex.I * e (k * x)) x := by
  -- Rewrite e in terms of exp
  have heq : ∀ y : ℝ, e (k * y) = Complex.exp (2 * ↑Real.pi * ↑k * Complex.I * ↑y) := by
    intro y; unfold e; congr 1; push_cast; ring
  simp_rw [heq]
  set c : ℂ := 2 * ↑Real.pi * ↑k * Complex.I
  -- Inner function g(y) = c·↑y has derivative c
  have hg : HasDerivAt (fun y : ℝ => c * (↑y : ℂ)) c x := by
    simpa using ((hasDerivAt_id x).ofReal_comp).const_mul c
  -- Chain rule via scomp
  have h := (Complex.hasDerivAt_exp (c * ↑x)).scomp x hg
  simp only [smul_eq_mul] at h
  exact h

/-- A trig polynomial is continuous. -/
theorem continuous_trig_poly (a : ℤ → ℂ) (S : Finset ℤ) :
    Continuous (fun x => ∑ n ∈ S, a n * e (↑n * x)) :=
  continuous_finsetSum S (fun n _ => continuous_const.mul (continuous_e_mul _))

/-- The derivative of a trig polynomial is continuous. -/
theorem continuous_deriv_trig_poly (a : ℤ → ℂ) (S : Finset ℤ) :
    Continuous (fun x => ∑ n ∈ S, (2 * ↑Real.pi * ↑n * Complex.I * a n) * e (↑n * x)) :=
  continuous_finsetSum S (fun n _ => continuous_const.mul (continuous_e_mul _))

/-- For any complex z, re(z) ≤ ‖z‖. -/
theorem complex_re_le_norm (z : ℂ) : z.re ≤ ‖z‖ := re_le_norm z

-- ============================================================
-- Part 10: Diagonal decomposition of the Gram form
-- ============================================================

/-- The Gram quadratic form can be split into diagonal + off-diagonal.
    Diagonal: ∑_n conj(aₙ)·aₙ·G(n,n) = R · ∑_n conj(aₙ)·aₙ
    since G(n,n) = R by gramEntry_diag. -/
theorem gram_form_diagonal_eq {R : ℕ} (α : Fin R → ℝ) (a : ℤ → ℂ) (S : Finset ℤ) :
    (∑ n ∈ S, starRingEnd ℂ (a n) * a n * gramEntry α n n) =
      ↑R * ∑ n ∈ S, starRingEnd ℂ (a n) * a n := by
  simp_rw [gramEntry_diag]
  simp_rw [show ∀ n : ℤ, starRingEnd ℂ (a n) * a n * (↑R : ℂ) =
      (↑R : ℂ) * (starRingEnd ℂ (a n) * a n) from fun n => by ring]
  rw [← Finset.mul_sum]

/-- conj(aₙ)·aₙ = ‖aₙ‖² as real (embedded in ℂ via .re) -/
theorem conj_mul_self_eq_norm_sq (z : ℂ) :
    (starRingEnd ℂ z * z).re = ‖z‖ ^ 2 := by
  rw [← norm_sq_eq_re_conj_mul]

/-- The diagonal of the Gram form equals R · ∑ ‖aₙ‖². -/
theorem gram_form_diagonal_re {R : ℕ} (α : Fin R → ℝ) (a : ℤ → ℂ) (S : Finset ℤ) :
    (∑ n ∈ S, starRingEnd ℂ (a n) * a n * gramEntry α n n).re =
      ↑R * ∑ n ∈ S, ‖a n‖ ^ 2 := by
  rw [gram_form_diagonal_eq]
  -- Goal: (↑R * ∑ n ∈ S, conj(a n) * a n).re = ↑R * ∑ ‖a n‖²
  have key : ∀ z : ℂ, ((↑R : ℂ) * z).re = (↑R : ℝ) * z.re := by
    intro z
    simp [Complex.mul_re, Complex.natCast_re, Complex.natCast_im]
  rw [key, Complex.re_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro n _
  exact conj_mul_self_eq_norm_sq (a n)

-- ============================================================
-- Part 11: Packing lemma and δ infrastructure
-- ============================================================

def minPairwiseFracDist {R : ℕ} (α : Fin R → ℝ) : ℝ :=
  if h : R ≥ 2 then
    Finset.inf' (Finset.filter (fun p : Fin R × Fin R => p.1 < p.2) Finset.univ)
      (by
        simp only [Finset.filter_nonempty_iff]
        refine ⟨⟨⟨0, by omega⟩, ⟨1, by omega⟩⟩, Finset.mem_univ _, ?_⟩
        simp [Fin.lt_def])
      (fun p => fracDist (α p.1 - α p.2))
  else 1

-- ============================================================
-- Part 12: Packing lemma
-- ============================================================

/-- fracDist is symmetric: fracDist(-x) = fracDist(x) -/
theorem fracDist_neg (x : ℝ) : fracDist (-x) = fracDist x := by
  unfold fracDist
  -- Use: |y - round y| ≤ |y - n| for any integer n (round_le)
  apply le_antisymm
  · -- fracDist(-x) ≤ fracDist(x): use n = -round(x)
    calc |-x - ↑(round (-x))| ≤ |-x - ↑(-round x)| := round_le (-x) (-round x)
      _ = |x - ↑(round x)| := by push_cast; rw [show -x - -↑(round x) = -(x - ↑(round x)) from by ring, abs_neg]
  · -- fracDist(x) ≤ fracDist(-x): use n = -round(-x)
    calc |x - ↑(round x)| ≤ |x - ↑(-round (-x))| := round_le x (-round (-x))
      _ = |-x - ↑(round (-x))| := by push_cast; rw [show x - -↑(round (-x)) = -((-x) - ↑(round (-x))) from by ring, abs_neg]

/-- Helper: minPairwiseFracDist is ≤ any specific pair's distance -/
theorem minPairwiseFracDist_le_pair {R : ℕ} (α : Fin R → ℝ) (hR : 2 ≤ R)
    (i j : Fin R) (hij : i < j) :
    minPairwiseFracDist α ≤ fracDist (α i - α j) := by
  unfold minPairwiseFracDist
  simp only [dif_pos hR]
  have hmem : (i, j) ∈ Finset.filter (fun p : Fin R × Fin R => p.1 < p.2) Finset.univ :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, hij⟩
  have : (fun p : Fin R × Fin R => fracDist (α p.1 - α p.2)) (i, j) = fracDist (α i - α j) := rfl
  rw [← this]
  exact Finset.inf'_le _ hmem

/-- All pairs have fracDist ≥ δ when minPairwiseFracDist = δ -/
theorem fracDist_ge_delta {R : ℕ} (α : Fin R → ℝ) (hR : 2 ≤ R)
    (hδ : 0 < minPairwiseFracDist α) (i j : Fin R) (hij : i ≠ j) :
    minPairwiseFracDist α ≤ fracDist (α i - α j) := by
  rcases lt_or_gt_of_ne hij with h | h
  · exact minPairwiseFracDist_le_pair α hR i j h
  · rw [show α i - α j = -(α j - α i) from by ring, fracDist_neg]
    exact minPairwiseFracDist_le_pair α hR j i h

/-- fracDist(x) = min(Int.fract x, 1 - Int.fract x) -/
theorem fracDist_eq_min_fract (x : ℝ) :
    fracDist x = min (Int.fract x) (1 - Int.fract x) := by
  unfold fracDist
  exact abs_sub_round_eq_min x

/-- Distinct fractional parts from δ-separation -/
theorem fract_injective_of_separated {R : ℕ} (α : Fin R → ℝ) (hR : 2 ≤ R)
    (hδ : 0 < minPairwiseFracDist α) :
    Function.Injective (fun r : Fin R => Int.fract (α r)) := by
  intro i j hij
  by_contra h
  have hne : i ≠ j := fun heq => h (by simp_all)
  have hge := fracDist_ge_delta α hR hδ i j hne
  -- hij: Int.fract(α i) = Int.fract(α j), so α i - α j is an integer
  have hint : ∃ k : ℤ, α i - α j = ↑k := by
    use ⌊α i⌋ - ⌊α j⌋
    have hi := Int.fract_add_floor (α i)
    have hj := Int.fract_add_floor (α j)
    rw [show (fun r : Fin R => Int.fract (α r)) i = Int.fract (α i) from rfl,
        show (fun r : Fin R => Int.fract (α r)) j = Int.fract (α j) from rfl] at hij
    push_cast; linarith
  obtain ⟨k, hk⟩ := hint
  have : fracDist (α i - α j) = 0 := by
    unfold fracDist; rw [hk]; simp [show round (↑k : ℝ) = k from round_intCast k]
  linarith

/-- The fractional parts are in [0,1) -/
theorem fract_mem_Ico (x : ℝ) : Int.fract x ∈ Set.Ico 0 1 :=
  ⟨Int.fract_nonneg x, Int.fract_lt_one x⟩

/-- fracDist(α_i - α_j) depends only on fractional parts -/
theorem fracDist_fract (x y : ℝ) :
    fracDist (x - y) = fracDist (Int.fract x - Int.fract y) := by
  unfold fracDist
  congr 1
  have hx := Int.fract_add_floor x
  have hy := Int.fract_add_floor y
  have : x - y - (Int.fract x - Int.fract y) = ↑(⌊x⌋ - ⌊y⌋) := by push_cast; linarith
  rw [show x - y = ↑(⌊x⌋ - ⌊y⌋) + (Int.fract x - Int.fract y) from by push_cast; linarith]
  rw [round_intCast_add, Int.cast_add, Int.cast_sub]; ring

/-- If δ ≤ fracDist(g) and g ∈ [0,1], then δ ≤ g -/
theorem delta_le_gap_of_fracDist {g δ : ℝ} (hg : 0 ≤ g) (hg1 : g ≤ 1)
    (hδ : δ ≤ fracDist g) : δ ≤ g := by
  have : fracDist g ≤ g := by
    unfold fracDist
    calc |g - ↑(round g)| ≤ |g - ↑(0 : ℤ)| := round_le g 0
      _ = |g| := by simp
      _ = g := abs_of_nonneg hg
  linarith

/-- If δ ≤ fracDist(g) and g ∈ [0,1], then δ ≤ 1 - g -/
theorem delta_le_wrap_gap_of_fracDist {g δ : ℝ} (hg : 0 ≤ g) (hg1 : g ≤ 1)
    (hδ : δ ≤ fracDist g) : δ ≤ 1 - g := by
  have : fracDist g ≤ 1 - g := by
    unfold fracDist
    exact le_trans (round_le g 1) (by push_cast; rw [abs_le]; constructor <;> linarith)
  linarith

/-- **Packing lemma (product form)**: R · δ ≤ 1.
    Proof: sort the R fractional parts in [0,1), observe that all R "circular gaps"
    (including wrap-around) are ≥ δ and sum to exactly 1. -/
theorem packing_bound_mul_core {R : ℕ} (α : Fin R → ℝ) (hR : 2 ≤ R)
    (hδ : 0 < minPairwiseFracDist α) :
    (↑R : ℝ) * minPairwiseFracDist α ≤ 1 := by
  set δ := minPairwiseFracDist α
  set β : Fin R → ℝ := fun r => Int.fract (α r)
  have hinj := fract_injective_of_separated α hR hδ
  -- β values are in [0,1) and injective
  have hβ_range : ∀ r, 0 ≤ β r ∧ β r < 1 := fun r => ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩
  -- For all i ≠ j: fracDist(β_i - β_j) ≥ δ (since fracDist depends only on fractional parts)
  have hsep : ∀ i j : Fin R, i ≠ j → δ ≤ fracDist (β i - β j) := by
    intro i j hij
    rw [show β i - β j = Int.fract (α i) - Int.fract (α j) from rfl, ← fracDist_fract]
    exact fracDist_ge_delta α hR hδ i j hij
  -- Strategy: show R * δ ≤ 1 using sorted fractional parts
  -- The fractional parts form R distinct points in [0,1).
  -- When sorted, each consecutive gap and the wrap-around gap is ≥ δ.
  -- The R gaps sum to 1, so R * δ ≤ 1.
  --
  -- For this formalization, we use orderEmbOfFin which gives a monotone embedding
  -- Fin R → S where S is the finset of fractional parts.
  set S := Finset.image β Finset.univ
  have hcard : S.card = R := (Finset.card_image_of_injective _ hinj).trans (Finset.card_fin R)
  -- Use orderEmbOfFin to get sorted access
  set e := S.orderEmbOfFin hcard
  -- e gives the sorted sequence: e 0 ≤ e 1 ≤ ... ≤ e (R-1)
  -- e i ∈ S for all i
  have he_mem : ∀ i : Fin R, (e i : ℝ) ∈ S := by
    intro i; exact Finset.orderEmbOfFin_mem _ _ _
  -- e is strictly monotone (as an OrderEmbedding)
  have he_strict : StrictMono (fun i : Fin R => (e i : ℝ)) := by
    intro i j hij
    exact e.strictMono hij
  -- All values in [0,1)
  have he_range : ∀ i : Fin R, 0 ≤ (e i : ℝ) ∧ (e i : ℝ) < 1 := by
    intro i
    have hmem := he_mem i
    rw [Finset.mem_image] at hmem
    obtain ⟨r, _, hr⟩ := hmem
    rw [← hr]; exact hβ_range r
  -- Any two distinct e values satisfy the separation condition
  have he_sep : ∀ i j : Fin R, i ≠ j →
      δ ≤ fracDist ((e i : ℝ) - (e j : ℝ)) := by
    intro i j hij
    have hmem_i := he_mem i
    have hmem_j := he_mem j
    rw [Finset.mem_image] at hmem_i hmem_j
    obtain ⟨ri, _, hri⟩ := hmem_i
    obtain ⟨rj, _, hrj⟩ := hmem_j
    rw [← hri, ← hrj]
    have hne : ri ≠ rj := by
      intro heq; exact hij (e.injective (by rw [← hri, ← hrj, heq]))
    exact hsep ri rj hne
  -- For i < j: gap e(j) - e(i) ≥ δ
  have he_gap : ∀ i j : Fin R, i < j → δ ≤ (e j : ℝ) - (e i : ℝ) := by
    intro i j hij
    have hnn : 0 ≤ (e j : ℝ) - (e i : ℝ) := sub_nonneg.mpr (he_strict hij).le
    have hle1 : (e j : ℝ) - (e i : ℝ) ≤ 1 := by
      linarith [(he_range j).2, (he_range i).1]
    exact delta_le_gap_of_fracDist hnn hle1 (he_sep j i (ne_of_lt hij).symm)
  -- Telescoping by induction: k * δ ≤ e(k) - e(0) for all k < R
  have htelescope : ∀ k : ℕ, (hk : k < R) →
      ↑k * δ ≤ (e ⟨k, hk⟩ : ℝ) - (e ⟨0, by omega⟩ : ℝ) := by
    intro k hk
    induction k with
    | zero => simp
    | succ n ih =>
      have ihn := ih (by omega)
      have hstep := he_gap ⟨n, by omega⟩ ⟨n + 1, hk⟩ (by exact Fin.mk_lt_mk.mpr (by omega))
      push_cast at ihn ⊢
      linarith
  -- Wrap-around gap: δ ≤ 1 - (e(R-1) - e(0))
  have he_last_first := he_sep ⟨R-1, by omega⟩ ⟨0, by omega⟩
      (by intro h; simp [Fin.ext_iff] at h; omega)
  have hwrap_nn : 0 ≤ (e ⟨R-1, by omega⟩ : ℝ) - (e ⟨0, by omega⟩ : ℝ) := by
    exact sub_nonneg.mpr (he_strict (by exact Fin.mk_lt_mk.mpr (by omega))).le
  have hwrap_le1 : (e ⟨R-1, by omega⟩ : ℝ) - (e ⟨0, by omega⟩ : ℝ) ≤ 1 := by
    linarith [(he_range ⟨R-1, by omega⟩).2, (he_range ⟨0, by omega⟩).1]
  have hwrap : δ ≤ 1 - ((e ⟨R-1, by omega⟩ : ℝ) - (e ⟨0, by omega⟩ : ℝ)) :=
    delta_le_wrap_gap_of_fracDist hwrap_nn hwrap_le1 he_last_first
  -- Combine: R * δ = (R-1) * δ + δ ≤ (e(R-1)-e(0)) + (1-(e(R-1)-e(0))) = 1
  have hR1 := htelescope (R - 1) (by omega)
  calc ↑R * δ = (↑(R - 1) + 1) * δ := by
          congr 1; rw [Nat.cast_sub (by omega : 1 ≤ R)]; ring
    _ = ↑(R - 1) * δ + δ := by ring
    _ ≤ (e ⟨R - 1, by omega⟩ - e ⟨0, by omega⟩) +
        (1 - (e ⟨R - 1, by omega⟩ - e ⟨0, by omega⟩)) := by linarith
    _ = 1 := by ring

/-- **Packing lemma**: R ≤ δ⁻¹ -/
theorem packing_bound {R : ℕ} (α : Fin R → ℝ) (hR : 2 ≤ R)
    (hδ : 0 < minPairwiseFracDist α) :
    (↑R : ℝ) ≤ (minPairwiseFracDist α)⁻¹ := by
  have h := packing_bound_mul_core α hR hδ
  have hR_pos : (0 : ℝ) < ↑R := by positivity
  rw [← one_div]
  exact le_div_iff₀ hδ |>.mpr h

/-- **Packing lemma (product form)**: R · δ ≤ 1 -/
theorem packing_bound_mul {R : ℕ} (α : Fin R → ℝ) (hR : 2 ≤ R)
    (hδ : 0 < minPairwiseFracDist α) :
    (↑R : ℝ) * minPairwiseFracDist α ≤ 1 := by
  have hd := le_of_lt hδ
  calc (↑R : ℝ) * minPairwiseFracDist α
      ≤ (minPairwiseFracDist α)⁻¹ * minPairwiseFracDist α := by
        gcongr; exact packing_bound α hR hδ
    _ = 1 := inv_mul_cancel₀ (ne_of_gt hδ)

-- ============================================================
-- Part 13: Gram form splitting (diagonal + off-diagonal)
-- ============================================================

/-- Split a double sum into diagonal + off-diagonal parts. -/
theorem gram_form_split {R : ℕ} (α : Fin R → ℝ) (a : ℤ → ℂ) (S : Finset ℤ) :
    (∑ m ∈ S, ∑ n ∈ S, starRingEnd ℂ (a m) * a n * gramEntry α m n) =
    (∑ n ∈ S, starRingEnd ℂ (a n) * a n * gramEntry α n n) +
    (∑ m ∈ S, ∑ n ∈ S.filter (· ≠ m), starRingEnd ℂ (a m) * a n * gramEntry α m n) := by
  -- Step 1: Split each inner sum at the diagonal term
  have step1 : ∀ m ∈ S,
      (∑ n ∈ S, starRingEnd ℂ (a m) * a n * gramEntry α m n) =
      (starRingEnd ℂ (a m) * a m * gramEntry α m m) +
      (∑ n ∈ S.filter (· ≠ m), starRingEnd ℂ (a m) * a n * gramEntry α m n) := by
    intro m hm
    rw [← Finset.add_sum_erase S _ hm]
    congr 1
    apply Finset.sum_congr
    · ext x; simp [Finset.mem_erase, Finset.mem_filter, and_comm]
    · intros; rfl
  -- Step 2: Apply step1 to rewrite the whole sum, then split
  have step2 : (∑ m ∈ S, ∑ n ∈ S, starRingEnd ℂ (a m) * a n * gramEntry α m n) =
      ∑ m ∈ S, ((starRingEnd ℂ (a m) * a m * gramEntry α m m) +
        ∑ n ∈ S.filter (· ≠ m), starRingEnd ℂ (a m) * a n * gramEntry α m n) := by
    apply Finset.sum_congr rfl; exact step1
  rw [step2, Finset.sum_add_distrib]

/-- The Gram form equals the diagonal part plus the off-diagonal part.
    The diagonal contributes R · ∑ ‖aₙ‖². -/
theorem gram_form_re_split {R : ℕ} (α : Fin R → ℝ) (a : ℤ → ℂ) (S : Finset ℤ) :
    (∑ m ∈ S, ∑ n ∈ S,
        starRingEnd ℂ (a m) * a n * gramEntry α m n).re =
    ↑R * (∑ n ∈ S, ‖a n‖ ^ 2) +
    (∑ m ∈ S, ∑ n ∈ S.filter (· ≠ m),
        starRingEnd ℂ (a m) * a n * gramEntry α m n).re := by
  have hsplit := gram_form_split α a S
  have : (∑ m ∈ S, ∑ n ∈ S, starRingEnd ℂ (a m) * a n * gramEntry α m n).re =
      ((∑ n ∈ S, starRingEnd ℂ (a n) * a n * gramEntry α n n) +
       (∑ m ∈ S, ∑ n ∈ S.filter (· ≠ m),
          starRingEnd ℂ (a m) * a n * gramEntry α m n)).re := by
    congr 1
  rw [this, Complex.add_re, gram_form_diagonal_re]

-- ============================================================
-- Part 14: The Gram form is real (Hermitian property)
-- ============================================================

/-- The full Gram form is real-valued (imaginary part is 0).
    This follows from the Hermitian property of the Gram matrix. -/
theorem gram_form_im_zero {R : ℕ} (α : Fin R → ℝ) (a : ℤ → ℂ) (S : Finset ℤ) :
    (∑ m ∈ S, ∑ n ∈ S,
        starRingEnd ℂ (a m) * a n * gramEntry α m n).im = 0 := by
  -- Strategy: show conj(z) = z using Hermitian property, hence z is real
  set z := ∑ m ∈ S, ∑ n ∈ S, starRingEnd ℂ (a m) * a n * gramEntry α m n with hz_def
  suffices hconj : starRingEnd ℂ z = z by
    have him := Complex.conj_im z
    rw [hconj] at him
    linarith
  -- Expand conj(z) = ∑_m ∑_n a_m * conj(a_n) * conj(G(m,n))
  simp only [hz_def, map_sum, map_mul]
  -- Simplify conj(conj(a_m)) = a_m and conj(G(m,n)) = G(n,m)
  simp_rw [show ∀ (x : ℂ), starRingEnd ℂ (starRingEnd ℂ x) = x from
      fun x => by simp [starRingEnd_self_apply],
    show ∀ m n : ℤ, starRingEnd ℂ (gramEntry α m n) = gramEntry α n m from
      fun m n => (gramEntry_conj α m n).symm]
  -- Now: ∑_m ∑_n a_m * conj(a_n) * G(n,m)
  -- Swap m ↔ n
  rw [Finset.sum_comm]
  -- After swap: ∑_n ∑_m a_m * conj(a_n) * G(n,m)
  -- = ∑_m ∑_n conj(a_m) * a_n * G(m,n) (by ring)
  apply Finset.sum_congr rfl; intro n _
  apply Finset.sum_congr rfl; intro m _
  ring

/-- The Gram form is non-negative (since it equals ∑_r ‖S(αr)‖²). -/
theorem gram_form_nonneg {R : ℕ} (α : Fin R → ℝ) (a : ℤ → ℂ) (M : ℤ) (N : ℕ) :
    0 ≤ (∑ m ∈ Finset.Icc (M + 1) (M + ↑N),
      ∑ n ∈ Finset.Icc (M + 1) (M + ↑N),
        starRingEnd ℂ (a m) * a n * gramEntry α m n).re := by
  rw [← large_sieve_sum_exchange]
  apply Finset.sum_nonneg
  intro r _
  exact sq_nonneg _

/-- The off-diagonal part of the Gram form is bounded below by
    -R · ∑ ‖aₙ‖² (combined with the diagonal decomposition). -/
theorem gram_offdiag_ge {R : ℕ} (α : Fin R → ℝ) (a : ℤ → ℂ) (M : ℤ) (N : ℕ) :
    -(↑R * ∑ n ∈ Finset.Icc (M + 1) (M + ↑N), ‖a n‖ ^ 2) ≤
    (∑ m ∈ Finset.Icc (M + 1) (M + ↑N),
      ∑ n ∈ (Finset.Icc (M + 1) (M + ↑N)).filter (· ≠ m),
        starRingEnd ℂ (a m) * a n * gramEntry α m n).re := by
  have hge := gram_form_nonneg α a M N
  rw [gram_form_re_split] at hge
  linarith

-- ============================================================
-- Part 15a: Geometric sum formula and bounds
-- ============================================================

/-- e(x) can be written as exp(I · (2πx)) -/
theorem e_eq_exp_I_mul (x : ℝ) :
    e x = Complex.exp (Complex.I * ↑(2 * Real.pi * x)) := by
  unfold e; congr 1; push_cast; ring

/-- Geometric sum formula: ∑_{k<N} e(kθ) = (e(Nθ)-1)/(e(θ)-1) -/
theorem geom_sum_e (N : ℕ) (θ : ℝ) (hθ : e θ ≠ 1) :
    ∑ k ∈ Finset.range N, e (↑k * θ) = (e (↑N * θ) - 1) / (e θ - 1) := by
  have he_sub_ne : e θ - 1 ≠ 0 := sub_ne_zero.mpr hθ
  rw [eq_div_iff he_sub_ne]
  induction N with
  | zero => simp [e_zero]
  | succ n ih =>
    rw [Finset.sum_range_succ, add_mul, ih]
    have : (↑(n + 1) : ℝ) * θ = ↑n * θ + θ := by push_cast; ring
    rw [this, e_add]; ring

/-- The norm of a geometric sum is bounded by 2/‖e(θ)-1‖.
    This follows from |∑e(kθ)| = |e(Nθ)-1|/|e(θ)-1| ≤ 2/|e(θ)-1|. -/
theorem norm_geom_sum_le (N : ℕ) (θ : ℝ) (hθ : e θ ≠ 1) :
    ‖∑ k ∈ Finset.range N, e (↑k * θ)‖ ≤ 2 / ‖e θ - 1‖ := by
  rw [geom_sum_e N θ hθ, norm_div]
  have hne : ‖e θ - 1‖ ≠ 0 := by
    rw [norm_ne_zero_iff]; exact sub_ne_zero.mpr hθ
  rw [div_le_div_iff_of_pos_right (by positivity : 0 < ‖e θ - 1‖)]
  calc ‖e (↑N * θ) - 1‖
      ≤ ‖e (↑N * θ)‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
    _ = 1 + 1 := by rw [norm_e, norm_one]
    _ = 2 := by ring

/-- ‖e(θ) - 1‖ = 2 * |sin(π * θ)|.
    Uses Mathlib's norm_exp_I_mul_ofReal_sub_one. -/
theorem norm_e_sub_one (θ : ℝ) :
    ‖e θ - 1‖ = 2 * |Real.sin (Real.pi * θ)| := by
  rw [e_eq_exp_I_mul, Complex.norm_exp_I_mul_ofReal_sub_one]
  congr 1
  have : 2 * Real.pi * θ / 2 = Real.pi * θ := by ring
  rw [this]
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity : (2:ℝ) ≥ 0)]

/-- Jordan's inequality: sin(π/2 * x) ≥ x for x ∈ [0,1].
    Equivalently: sin(πθ) ≥ 2θ for θ ∈ [0, 1/2]. -/
theorem sin_pi_ge_two (θ : ℝ) (h0 : 0 ≤ θ) (h1 : θ ≤ 1/2) :
    2 * θ ≤ Real.sin (Real.pi * θ) := by
  have hx : 0 ≤ 2 * θ := by linarith
  have hx1 : 2 * θ ≤ 1 := by linarith
  have hsm := Real.le_sin_mul hx hx1
  -- hsm : 2 * θ ≤ sin(π/2 * (2 * θ)), and π/2 * (2*θ) = π*θ
  rw [show Real.pi / 2 * (2 * θ) = Real.pi * θ from by ring] at hsm
  exact hsm

/-- |sin(π * θ)| ≥ 2 * fracDist(θ) for all θ.
    Since fracDist(θ) ∈ [0,1/2], we apply Jordan's inequality. -/
theorem abs_sin_pi_ge_two_fracDist (θ : ℝ) :
    2 * fracDist θ ≤ |Real.sin (Real.pi * θ)| := by
  unfold fracDist
  set d := |θ - round θ| with hd_def
  have hd_nn : 0 ≤ d := abs_nonneg _
  have hd_le : d ≤ 1 / 2 := abs_sub_round θ
  -- Step 1: Reduce to |sin(π(θ - round θ))| using periodicity
  have hkey : |Real.sin (Real.pi * θ)| = |Real.sin (Real.pi * (θ - ↑(round θ)))| := by
    have heq : Real.pi * θ = Real.pi * (θ - ↑(round θ)) + ↑(round θ) * Real.pi := by ring
    rw [heq]
    rw [Real.sin_add_int_mul_pi]
    simp [abs_mul, abs_pow, abs_neg, abs_one]
  rw [hkey]
  -- Step 2: Use |sin(πy)| = |sin(π|y|)| (sin is odd) and reduce to sin(πd) ≥ 2d
  -- Since y = θ - round θ and |y| = d, sin(πy) satisfies |sin(πy)| = |sin(π·d)|
  -- because |sin(-x)| = |sin(x)|
  have h_abs_eq : |Real.sin (Real.pi * (θ - ↑(round θ)))| =
      |Real.sin (Real.pi * d)| := by
    by_cases hy : 0 ≤ θ - ↑(round θ)
    · -- y ≥ 0, so d = y
      have : d = θ - ↑(round θ) := abs_of_nonneg hy
      rw [this]
    · -- y < 0, so d = -y and sin(πy) = -sin(πd)
      have hy_neg : θ - ↑(round θ) < 0 := not_le.mp hy
      have hd_neg : d = -(θ - ↑(round θ)) := abs_of_neg hy_neg
      rw [show Real.pi * (θ - ↑(round θ)) = -(Real.pi * d) by rw [hd_neg]; ring]
      rw [Real.sin_neg, abs_neg]
  rw [h_abs_eq]
  -- Step 3: sin(πd) ≥ 0 since πd ∈ [0, π/2]
  have hsin_nn : 0 ≤ Real.sin (Real.pi * d) := by
    apply Real.sin_nonneg_of_nonneg_of_le_pi
    · exact mul_nonneg (le_of_lt Real.pi_pos) hd_nn
    · calc Real.pi * d ≤ Real.pi * (1 / 2) :=
            mul_le_mul_of_nonneg_left hd_le (le_of_lt Real.pi_pos)
        _ ≤ Real.pi := by nlinarith [Real.pi_pos]
  rw [abs_of_nonneg hsin_nn]
  -- Step 4: Apply Jordan's inequality: sin(πd) ≥ 2d for d ∈ [0, 1/2]
  exact sin_pi_ge_two d hd_nn hd_le

/-- Lower bound on ‖e(θ)-1‖ using fracDist:
    ‖e(θ)-1‖ ≥ 4 · fracDist(θ).
    This combines ‖e(θ)-1‖ = 2|sin(πθ)| with |sin(πθ)| ≥ 2·fracDist(θ). -/
theorem norm_e_sub_one_ge_fracDist (θ : ℝ) :
    4 * fracDist θ ≤ ‖e θ - 1‖ := by
  rw [norm_e_sub_one]
  have h := abs_sin_pi_ge_two_fracDist θ
  linarith

-- ============================================================
-- Part 15a2: Dual Gram matrix bounds
-- ============================================================

/-- The dual Gram entry: ∑_{n∈S} e(n(α_r - α_s)). -/
def dualGramEntry {R : ℕ} (α : Fin R → ℝ) (M : ℤ) (N : ℕ) (r s : Fin R) : ℂ :=
  ∑ n ∈ Finset.Icc (M + 1) (M + ↑N), e (↑n * (α r - α s))

/-- Dual Gram diagonal entries equal N. -/
theorem dualGramEntry_diag {R : ℕ} (α : Fin R → ℝ) (M : ℤ) (N : ℕ) (r : Fin R) :
    dualGramEntry α M N r r = ↑(Finset.Icc (M + 1) (M + ↑N)).card := by
  simp [dualGramEntry, sub_self, mul_zero, e_zero, Finset.sum_const, smul_eq_mul, mul_one]

/-- The primal and dual Gram are related:
    ∑_r |T(α_r)|² = ∑_{m,n} conj(a_m)a_n · dualGram_connection.
    This links them for the bilinear form. -/
theorem gram_dual_connection {R : ℕ} (α : Fin R → ℝ) (m n : ℤ) :
    gramEntry α m n = ∑ r : Fin R, e (↑n * α r) * (starRingEnd ℂ (e (↑m * α r))) := by
  simp only [gramEntry]
  congr 1; ext r
  have h1 : (↑n - ↑m) * α r = ↑n * α r + -(↑m * α r) := by ring
  rw [h1, e_add]
  have h2 : e (-(↑m * α r)) = starRingEnd ℂ (e (↑m * α r)) := by
    exact e_neg (↑m * α r)
  rw [h2]

-- ============================================================
-- Part 15: Bombieri's large sieve (sorry-free)
-- ============================================================

/-- **Bombieri's Large Sieve** (1965): ∑ |S(α_r)|² ≤ N·δ⁻¹ · ∑|aₙ|²
    This is the SORRY-FREE version, weaker than Montgomery-Vaughan but fully proved.
    Proof: combines the weak bound (RN) with the packing lemma (R ≤ δ⁻¹). -/
theorem large_sieve_bombieri
    (R : ℕ) (α : Fin R → ℝ) (a : ℤ → ℂ) (M : ℤ) (N : ℕ)
    (hN : 0 < N) (hR : 2 ≤ R)
    (hδ : 0 < minPairwiseFracDist α) :
    (∑ r : Fin R, ‖expSum a M N (α r)‖ ^ 2) ≤
      (↑N * (minPairwiseFracDist α)⁻¹) *
        (∑ n ∈ Finset.Icc (M + 1) (M + ↑N), ‖a n‖ ^ 2) := by
  have hweak := large_sieve_weak α a M N hN
  have hpack := packing_bound α hR hδ
  have hnorm_nn : 0 ≤ ∑ n ∈ Finset.Icc (M + 1) (M + ↑N), ‖a n‖ ^ 2 :=
    Finset.sum_nonneg (fun n _ => by positivity)
  calc ∑ r : Fin R, ‖expSum a M N (α r)‖ ^ 2
      ≤ ↑R * (↑N * ∑ n ∈ Finset.Icc (M + 1) (M + ↑N), ‖a n‖ ^ 2) := hweak
    _ ≤ (minPairwiseFracDist α)⁻¹ * (↑N * ∑ n ∈ Finset.Icc (M + 1) (M + ↑N), ‖a n‖ ^ 2) := by
        gcongr
    _ = ↑N * (minPairwiseFracDist α)⁻¹ * ∑ n ∈ Finset.Icc (M + 1) (M + ↑N), ‖a n‖ ^ 2 := by ring

-- ============================================================
-- Verification
-- ============================================================

-- Sorry-free theorems (Attempt 7 additions marked with ★):
#check @e_int                        -- e(n) = 1 for integers
#check @integral_e_int               -- ∫₀¹ e(kx) dx = δ_{k,0} (combined)
#check @integral_e_int_ne_zero       -- ∫₀¹ e(kx) dx = 0 for k ≠ 0
#check @cross_integral               -- ∫₀¹ conj(e(mx))·e(nx) dx = δ_{m,n}
#check @continuous_e_mul             -- e(kx) is continuous
#check @parseval_trig_poly_complex   -- Parseval (complex inner product form)
#check @parseval_trig_poly_norm      -- Parseval (norm-squared form)
#check @norm_sq_eq_re_conj_mul       -- ‖z‖² = re(conj(z)·z)
#check @large_sieve_sum_exchange     -- LHS = re(∑_m ∑_n conj(a_m)·a_n·G(m,n))
#check @gramEntry_norm_le            -- |G(m,n)| ≤ R
#check @gramEntry_conj               -- G(n,m) = conj(G(m,n)) (Hermitian)
#check @gramEntry_diag               -- G(n,n) = R (diagonal)
#check @large_sieve_R1               -- |S(α)|² ≤ N·∑|aₙ|² (R=1 case)
#check @large_sieve_weak             -- ∑_r |S(α_r)|² ≤ R·N·∑|aₙ|²
#check @sieveMatrix_gram_posSemidef  -- V^H·V is PSD
#check @trace_sieveGram              -- Tr(V^H·V) = R·|S|
-- ★ New in Attempt 7:
#check @hasDerivAt_e_mul             -- ★ d/dx e(kx) = 2πik·e(kx) (DERIVATIVE!)
#check @continuous_trig_poly         -- ★ T(x) = ∑ aₙe(nx) is continuous
#check @continuous_deriv_trig_poly   -- ★ T'(x) is continuous
#check @conj_mul_self_eq_norm_sq     -- ★ re(conj(z)·z) = ‖z‖²
#check @gram_form_diagonal_eq        -- ★ ∑ conj(aₙ)·aₙ·G(n,n) = R·∑ conj(aₙ)·aₙ
#check @gram_form_diagonal_re        -- ★ (diagonal).re = R·∑‖aₙ‖²
#check @packing_bound_mul            -- ★ R·δ ≤ 1 (from packing_bound + sorry)
#check @gram_form_split              -- ★ Gram form = diagonal + off-diagonal
#check @gram_form_re_split           -- ★ Gram form .re = R·∑‖aₙ‖² + offdiag.re
#check @gram_form_im_zero            -- ★ Gram form .im = 0 (Hermitian proof)
#check @gram_form_nonneg             -- ★ Gram form ≥ 0 (via sum exchange)
#check @gram_offdiag_ge              -- ★ offdiag ≥ -R·∑‖aₙ‖²
-- ★★ New in Attempt 8:
#check @fracDist_neg                 -- ★★ fracDist(-x) = fracDist(x)
#check @minPairwiseFracDist_le_pair  -- ★★ min pairwise dist ≤ any pair
#check @fracDist_ge_delta            -- ★★ all pairs have fracDist ≥ δ
#check @fracDist_eq_min_fract        -- ★★ fracDist = min(fract, 1-fract)
#check @fract_injective_of_separated -- ★★ δ-separated → injective fractional parts
#check @fracDist_fract               -- ★★ fracDist depends only on fractional parts
#check @delta_le_gap_of_fracDist     -- ★★ δ ≤ fracDist(g) → δ ≤ g for g ∈ [0,1]
#check @delta_le_wrap_gap_of_fracDist -- ★★ δ ≤ fracDist(g) → δ ≤ 1-g
#check @packing_bound_mul_core       -- ★★ R·δ ≤ 1 (SORRY-FREE! via sorted fracts + telescoping)
#check @packing_bound                -- ★★ R ≤ δ⁻¹ (SORRY-FREE!)
#check @large_sieve_bombieri         -- ★★ SORRY-FREE Bombieri Large Sieve: ∑|S|² ≤ N·δ⁻¹·∑|a|²
-- ★★★ New in Attempt 8 (creative push):
#check @e_eq_exp_I_mul               -- ★★★ e(x) = exp(I · 2πx) (bridge to Mathlib trig)
#check @geom_sum_e                   -- ★★★ ∑_{k<N} e(kθ) = (e(Nθ)-1)/(e(θ)-1)
#check @norm_geom_sum_le             -- ★★★ ‖∑e(kθ)‖ ≤ 2/‖e(θ)-1‖
#check @norm_e_sub_one               -- ★★★ ‖e(θ)-1‖ = 2|sin(πθ)| (EXACT identity!)
#check @sin_pi_ge_two                -- ★★★ sin(πθ) ≥ 2θ for θ ∈ [0,1/2] (Jordan)
#check @abs_sin_pi_ge_two_fracDist   -- ★★★ |sin(πθ)| ≥ 2·fracDist(θ) (all θ)
#check @norm_e_sub_one_ge_fracDist   -- ★★★ ‖e(θ)-1‖ ≥ 4·fracDist(θ) (key lower bound)
#check @dualGramEntry                -- ★★★ dual Gram entry definition
#check @dualGramEntry_diag           -- ★★★ dual Gram diagonal = |S|
#check @gram_dual_connection         -- ★★★ primal Gram = ∑_r e(nα_r)·conj(e(mα_r))

end
