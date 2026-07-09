/-
# Large Sieve — Attempt 12: Gallagher's proof (Sobolev route)

Goal: a fully sorry-free additive large sieve of the shape
  ∑_r ‖S(α_r)‖² ≤ C · (N + δ⁻¹) · ∑ ‖a_n‖²
via Gallagher's 1967 argument. The sharp constant needs Beurling–Selberg,
but FLDutchmann's axiom only needs SOME constant, so this suffices.

Plan:
1. Derivative of a trig polynomial (HasDerivAt for the finite sum).
2. HasDerivAt of ‖T(x)‖² with derivative 2·re(conj T · T').
3. Gallagher/Sobolev pointwise bound via FTC + min-value averaging:
   ‖T(x₀)‖² ≤ δ⁻¹·∫_I ‖T‖² + ∫_I 2‖T‖‖T'‖  on I = [x₀-δ/2, x₀+δ/2].
4. AM-GM: 2‖T‖‖T'‖ ≤ η‖T‖² + η⁻¹‖T'‖².
5. Disjointness of the intervals around fract(α_r) + periodization to [0,1].
6. Parseval for T and T' + recentering of frequencies to [1,N].
-/

import LargeSieve.Additive.ExpSum
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

open scoped BigOperators
open Finset

noncomputable section

namespace Gallagher

-- ============================================================
-- Part 1: Derivative of a trig polynomial
-- ============================================================

/-- Derivative of a trig polynomial at any point. -/
theorem hasDerivAt_trig_poly (a : ℤ → ℂ) (S : Finset ℤ) (x : ℝ) :
    HasDerivAt (fun t => ∑ n ∈ S, a n * e (↑n * t))
      (∑ n ∈ S, (2 * ↑Real.pi * ↑n * Complex.I * a n) * e (↑n * x)) x := by
  have h : ∀ n ∈ S, HasDerivAt (fun t => a n * e (↑n * t))
      ((2 * ↑Real.pi * ↑n * Complex.I * a n) * e (↑n * x)) x := by
    intro n _
    have hd := (hasDerivAt_e_mul (n : ℝ) x).const_mul (a n)
    have heq : (2 * ↑Real.pi * ↑n * Complex.I * a n) * e (↑n * x)
        = a n * (2 * ↑Real.pi * ↑(n : ℝ) * Complex.I * e (↑n * x)) := by
      push_cast
      ring
    rw [heq]
    exact hd
  exact HasDerivAt.fun_sum h

-- ============================================================
-- Part 2: Derivative of ‖T(x)‖²
-- ============================================================

/-- If U has derivative d at x, then ‖U‖² has derivative 2·re(conj(U x)·d). -/
theorem hasDerivAt_norm_sq {U : ℝ → ℂ} {d : ℂ} {x : ℝ}
    (hU : HasDerivAt U d x) :
    HasDerivAt (fun t => ‖U t‖ ^ 2) (2 * (starRingEnd ℂ (U x) * d).re) x := by
  have hre : HasDerivAt (fun t => (U t).re) d.re x :=
    Complex.reCLM.hasFDerivAt.comp_hasDerivAt x hU
  have him : HasDerivAt (fun t => (U t).im) d.im x :=
    Complex.imCLM.hasFDerivAt.comp_hasDerivAt x hU
  have h1 : HasDerivAt (fun t => (U t).re * (U t).re + (U t).im * (U t).im)
      ((d.re * (U x).re + (U x).re * d.re) + (d.im * (U x).im + (U x).im * d.im)) x :=
    (hre.mul hre).add (him.mul him)
  have heq : (fun t => (U t).re * (U t).re + (U t).im * (U t).im)
      = fun t => ‖U t‖ ^ 2 := by
    funext t
    rw [norm_sq_eq_re_conj_mul (U t), Complex.mul_re, Complex.conj_re, Complex.conj_im]
    ring
  rw [heq] at h1
  have hval : 2 * (starRingEnd ℂ (U x) * d).re
      = (d.re * (U x).re + (U x).re * d.re) + (d.im * (U x).im + (U x).im * d.im) := by
    rw [Complex.mul_re, Complex.conj_re, Complex.conj_im]
    ring
  rw [hval]
  exact h1

/-- The derivative of ‖T‖² is bounded: |(‖U‖²)'| ≤ 2‖U‖‖d‖. -/
theorem abs_deriv_norm_sq_le (z d : ℂ) :
    |2 * (starRingEnd ℂ z * d).re| ≤ 2 * ‖z‖ * ‖d‖ := by
  have h1 : |(starRingEnd ℂ z * d).re| ≤ ‖starRingEnd ℂ z * d‖ :=
    Complex.abs_re_le_norm _
  have h2 : ‖starRingEnd ℂ z * d‖ = ‖z‖ * ‖d‖ := by
    rw [norm_mul]
    simp
  calc |2 * (starRingEnd ℂ z * d).re| = 2 * |(starRingEnd ℂ z * d).re| := by
        rw [abs_mul]; norm_num
    _ ≤ 2 * (‖z‖ * ‖d‖) := by nlinarith
    _ = 2 * ‖z‖ * ‖d‖ := by ring

-- ============================================================
-- Part 3: Sobolev / Gallagher pointwise bound
-- ============================================================

/-- FTC-based bound: for x₀, x₁ ∈ [A,B],
    f(x₁) ≤ f(x₀) + ∫_A^B |f'|, where f has continuous derivative g on ℝ. -/
theorem ftc_bound {f g : ℝ → ℝ} (hf : ∀ x, HasDerivAt f (g x) x)
    (hg : Continuous g) {A B x₀ x₁ : ℝ} (hAB : A ≤ B)
    (h₀ : x₀ ∈ Set.Icc A B) (h₁ : x₁ ∈ Set.Icc A B) :
    f x₁ ≤ f x₀ + ∫ t in A..B, |g t| := by
  have hftc : f x₁ - f x₀ = ∫ t in x₀..x₁, g t := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t _ => hf t) (hg.intervalIntegrable _ _)]
  have habs : |∫ t in x₀..x₁, g t| ≤ ∫ t in A..B, |g t| := by
    have h1 : |∫ t in x₀..x₁, g t| ≤ abs (∫ t in x₀..x₁, (fun s => |g s|) t) := by
      simpa [Real.norm_eq_abs] using
        (intervalIntegral.norm_integral_le_abs_integral_norm
          (f := g) (a := x₀) (b := x₁) (μ := MeasureTheory.volume))
    have h2 : abs (∫ t in x₀..x₁, (fun s => |g s|) t)
        ≤ abs (∫ t in A..B, (fun s => |g s|) t) := by
      apply intervalIntegral.abs_integral_mono_interval
      · rw [Set.uIoc, Set.uIoc]
        exact Set.Ioc_subset_Ioc (le_trans inf_le_left (le_inf h₀.1 h₁.1))
          (le_trans (sup_le h₀.2 h₁.2) le_sup_right)
      · exact Filter.Eventually.of_forall (fun t => abs_nonneg _)
      · exact hg.abs.intervalIntegrable _ _
    have h3 : abs (∫ t in A..B, (fun s => |g s|) t) = ∫ t in A..B, |g t| :=
      abs_of_nonneg (intervalIntegral.integral_nonneg hAB (fun t _ => abs_nonneg _))
    calc |∫ t in x₀..x₁, g t| ≤ abs (∫ t in x₀..x₁, (fun s => |g s|) t) := h1
      _ ≤ abs (∫ t in A..B, (fun s => |g s|) t) := h2
      _ = ∫ t in A..B, |g t| := h3
  rw [← hftc] at habs
  linarith [le_abs_self (f x₁ - f x₀), habs]

/-- Mean-value: a continuous function attains a value ≤ its average.
    ∃ x₀ ∈ [A,B], f(x₀)·(B-A) ≤ ∫_A^B f. -/
theorem exists_le_average {f : ℝ → ℝ} (hf : Continuous f) {A B : ℝ} (hAB : A < B) :
    ∃ x₀ ∈ Set.Icc A B, f x₀ * (B - A) ≤ ∫ t in A..B, f t := by
  obtain ⟨x₀, hx₀, hmin⟩ := (isCompact_Icc (a := A) (b := B)).exists_isMinOn
    (Set.nonempty_Icc.mpr hAB.le) hf.continuousOn
  refine ⟨x₀, hx₀, ?_⟩
  have : ∫ t in A..B, f x₀ ≤ ∫ t in A..B, f t := by
    apply intervalIntegral.integral_mono_on hAB.le
      (intervalIntegrable_const) (hf.intervalIntegrable _ _)
    intro t ht
    exact hmin ht
  simpa [intervalIntegral.integral_const, smul_eq_mul, mul_comm] using this
-- ============================================================
-- Part 4: Gallagher pointwise bound for trig polynomials
-- ============================================================

/-- Abbreviation: the trig polynomial and its derivative. -/
def T (a : ℤ → ℂ) (S : Finset ℤ) (t : ℝ) : ℂ := ∑ n ∈ S, a n * e (↑n * t)

def T' (a : ℤ → ℂ) (S : Finset ℤ) (t : ℝ) : ℂ :=
  ∑ n ∈ S, (2 * ↑Real.pi * ↑n * Complex.I * a n) * e (↑n * t)

theorem continuous_T (a : ℤ → ℂ) (S : Finset ℤ) : Continuous (T a S) :=
  continuous_trig_poly a S

theorem continuous_T' (a : ℤ → ℂ) (S : Finset ℤ) : Continuous (T' a S) := by
  unfold T'
  exact continuous_finsetSum S (fun n _ => continuous_const.mul (continuous_e_mul _))

theorem hasDerivAt_T (a : ℤ → ℂ) (S : Finset ℤ) (x : ℝ) :
    HasDerivAt (T a S) (T' a S x) x :=
  hasDerivAt_trig_poly a S x

/-- AM-GM pointwise: 2‖z‖‖d‖ ≤ η‖z‖² + η⁻¹‖d‖². -/
theorem two_mul_norm_le (z d : ℂ) {η : ℝ} (hη : 0 < η) :
    2 * ‖z‖ * ‖d‖ ≤ η * ‖z‖ ^ 2 + η⁻¹ * ‖d‖ ^ 2 := by
  rw [← sub_nonneg]
  have key : η * ‖z‖ ^ 2 + η⁻¹ * ‖d‖ ^ 2 - 2 * ‖z‖ * ‖d‖
      = η⁻¹ * (η * ‖z‖ - ‖d‖) ^ 2 := by
    field_simp
    ring
  rw [key]
  positivity

/-- The integrand controlling the Gallagher bound. -/
def G (a : ℤ → ℂ) (S : Finset ℤ) (δ η : ℝ) (t : ℝ) : ℝ :=
  δ⁻¹ * ‖T a S t‖ ^ 2 + (η * ‖T a S t‖ ^ 2 + η⁻¹ * ‖T' a S t‖ ^ 2)

theorem continuous_normsq_T (a : ℤ → ℂ) (S : Finset ℤ) :
    Continuous (fun t => ‖T a S t‖ ^ 2) :=
  ((continuous_T a S).norm.pow 2)

theorem continuous_normsq_T' (a : ℤ → ℂ) (S : Finset ℤ) :
    Continuous (fun t => ‖T' a S t‖ ^ 2) :=
  ((continuous_T' a S).norm.pow 2)

theorem continuous_cross_term (a : ℤ → ℂ) (S : Finset ℤ) (η : ℝ) :
    Continuous (fun t => η * ‖T a S t‖ ^ 2 + η⁻¹ * ‖T' a S t‖ ^ 2) :=
  (continuous_const.mul (continuous_normsq_T a S)).add
    (continuous_const.mul (continuous_normsq_T' a S))

theorem continuous_G (a : ℤ → ℂ) (S : Finset ℤ) (δ η : ℝ) :
    Continuous (G a S δ η) := by
  unfold G
  exact (continuous_const.mul (continuous_normsq_T a S)).add
    (continuous_cross_term a S η)

theorem G_nonneg (a : ℤ → ℂ) (S : Finset ℤ) {δ η : ℝ} (hδ : 0 < δ) (hη : 0 < η)
    (t : ℝ) : 0 ≤ G a S δ η t := by
  unfold G
  have h1 : (0:ℝ) ≤ δ⁻¹ := inv_nonneg.mpr hδ.le
  have h2 : (0:ℝ) ≤ η⁻¹ := inv_nonneg.mpr hη.le
  positivity

/-- **Gallagher pointwise bound**: for any x₀ and δ, η > 0,
    ‖T(x₀)‖² ≤ ∫_{x₀-δ/2}^{x₀+δ/2} G. -/
theorem gallagher_pointwise (a : ℤ → ℂ) (S : Finset ℤ) (x₀ : ℝ) {δ η : ℝ}
    (hδ : 0 < δ) (hη : 0 < η) :
    ‖T a S x₀‖ ^ 2 ≤ ∫ t in (x₀ - δ/2)..(x₀ + δ/2), G a S δ η t := by
  set A := x₀ - δ/2 with hA
  set B := x₀ + δ/2 with hB
  have hAB : A < B := by simp [hA, hB]; linarith
  -- the derivative of ‖T‖²
  set g : ℝ → ℝ := fun t => 2 * (starRingEnd ℂ (T a S t) * T' a S t).re with hg_def
  have hf : ∀ x, HasDerivAt (fun t => ‖T a S t‖ ^ 2) (g x) x := fun x =>
    hasDerivAt_norm_sq (hasDerivAt_T a S x)
  have hg_cont : Continuous g := by
    apply continuous_const.mul
    exact (Complex.continuous_re.comp
      (((continuous_T a S).star).mul (continuous_T' a S)))
  -- find a point where ‖T‖² is below its average
  have hf_cont : Continuous (fun t => ‖T a S t‖ ^ 2) := continuous_normsq_T a S
  obtain ⟨x₁, hx₁, havg⟩ := exists_le_average hf_cont hAB
  -- FTC bound from x₁ to x₀
  have hx₀mem : x₀ ∈ Set.Icc A B := by
    constructor <;> simp [hA, hB] <;> linarith
  have hftc := ftc_bound hf hg_cont hAB.le hx₁ hx₀mem
  -- combine: ‖T x₀‖² ≤ ‖T x₁‖² + ∫|g| ≤ δ⁻¹∫‖T‖² + ∫|g|
  have hBA : B - A = δ := by simp [hA, hB]
  have h1 : ‖T a S x₁‖ ^ 2 ≤ δ⁻¹ * ∫ t in A..B, ‖T a S t‖ ^ 2 := by
    rw [hBA] at havg
    have h' := mul_le_mul_of_nonneg_left havg (inv_nonneg.mpr hδ.le)
    calc ‖T a S x₁‖ ^ 2 = δ⁻¹ * (‖T a S x₁‖ ^ 2 * δ) := by
          field_simp
      _ ≤ δ⁻¹ * ∫ t in A..B, ‖T a S t‖ ^ 2 := h'
  -- pointwise |g| ≤ η‖T‖² + η⁻¹‖T'‖²
  have h2 : ∫ t in A..B, |g t| ≤
      ∫ t in A..B, (η * ‖T a S t‖ ^ 2 + η⁻¹ * ‖T' a S t‖ ^ 2) := by
    apply intervalIntegral.integral_mono_on hAB.le
      (hg_cont.abs.intervalIntegrable _ _)
      ((continuous_cross_term a S η).intervalIntegrable _ _)
    intro t _
    calc |g t| ≤ 2 * ‖T a S t‖ * ‖T' a S t‖ := abs_deriv_norm_sq_le _ _
      _ ≤ η * ‖T a S t‖ ^ 2 + η⁻¹ * ‖T' a S t‖ ^ 2 := two_mul_norm_le _ _ hη
  -- assemble
  have hsplit : ∫ t in A..B, G a S δ η t =
      (∫ t in A..B, δ⁻¹ * ‖T a S t‖ ^ 2) +
      ∫ t in A..B, (η * ‖T a S t‖ ^ 2 + η⁻¹ * ‖T' a S t‖ ^ 2) := by
    unfold G
    exact intervalIntegral.integral_add
      ((continuous_const.mul (continuous_normsq_T a S)).intervalIntegrable _ _)
      ((continuous_cross_term a S η).intervalIntegrable _ _)
  rw [hsplit, intervalIntegral.integral_const_mul]
  linarith [hftc, h1, h2]

-- ============================================================
-- Part 5: Periodicity + disjoint intervals + periodization
-- ============================================================

theorem T_periodic (a : ℤ → ℂ) (S : Finset ℤ) : Function.Periodic (T a S) 1 := by
  intro t
  unfold T
  apply Finset.sum_congr rfl
  intro n _
  congr 1
  have h : (↑n : ℝ) * (t + 1) = ↑n * t + ↑n := by ring
  rw [h, e_add, e_int, mul_one]

theorem T'_periodic (a : ℤ → ℂ) (S : Finset ℤ) : Function.Periodic (T' a S) 1 := by
  intro t
  unfold T'
  apply Finset.sum_congr rfl
  intro n _
  congr 1
  have h : (↑n : ℝ) * (t + 1) = ↑n * t + ↑n := by ring
  rw [h, e_add, e_int, mul_one]

theorem G_periodic (a : ℤ → ℂ) (S : Finset ℤ) (δ η : ℝ) :
    Function.Periodic (G a S δ η) 1 := by
  intro t
  unfold G
  rw [T_periodic a S t, T'_periodic a S t]

/-- Sum of integrals over disjoint δ-intervals around points in [0,1) is at most
    the integral over (-1/2, 3/2), for nonneg continuous g. -/
theorem sum_interval_integrals_le {R : ℕ} (β : Fin R → ℝ) {δ : ℝ} (hδ : 0 < δ)
    (hδ1 : δ ≤ 1) (hβ : ∀ r, β r ∈ Set.Ico (0:ℝ) 1)
    (hsep : ∀ r s, r ≠ s → δ ≤ |β r - β s|)
    (g : ℝ → ℝ) (hg : Continuous g) (hg0 : ∀ t, 0 ≤ g t) :
    ∑ r : Fin R, ∫ t in (β r - δ/2)..(β r + δ/2), g t ≤
      ∫ t in (-(1:ℝ)/2)..(3/2), g t := by
  -- convert each interval integral to a set integral over Ioc
  have hconv : ∀ r : Fin R, ∫ t in (β r - δ/2)..(β r + δ/2), g t =
      ∫ t in Set.Ioc (β r - δ/2) (β r + δ/2), g t := by
    intro r
    rw [intervalIntegral.integral_of_le (by linarith)]
  simp_rw [hconv]
  -- the Ioc's are pairwise disjoint
  have hpair : (↑(Finset.univ : Finset (Fin R)) : Set (Fin R)).Pairwise
      (Function.onFun Disjoint fun r => Set.Ioc (β r - δ/2) (β r + δ/2)) := by
    intro r _ s hs hrs
    rw [Function.onFun, Set.disjoint_left]
    intro t htr hts
    have h1 : β r - δ/2 < t := htr.1
    have h2 : t ≤ β r + δ/2 := htr.2
    have h3 : β s - δ/2 < t := hts.1
    have h4 : t ≤ β s + δ/2 := hts.2
    have habs : |β r - β s| < δ := by
      rw [abs_sub_lt_iff]
      constructor <;> linarith
    linarith [hsep r s hrs]
  have hmeas : ∀ r ∈ (Finset.univ : Finset (Fin R)),
      MeasurableSet (Set.Ioc (β r - δ/2) (β r + δ/2)) := fun r _ => measurableSet_Ioc
  have hint : ∀ r ∈ (Finset.univ : Finset (Fin R)),
      MeasureTheory.IntegrableOn g (Set.Ioc (β r - δ/2) (β r + δ/2)) :=
    fun r _ => hg.integrableOn_Ioc
  rw [← MeasureTheory.integral_biUnion_finset Finset.univ hmeas hpair hint]
  rw [intervalIntegral.integral_of_le (by norm_num : (-(1:ℝ)/2) ≤ 3/2)]
  apply MeasureTheory.setIntegral_mono_set hg.integrableOn_Ioc
    (Filter.Eventually.of_forall (fun t => hg0 t))
  apply Filter.Eventually.of_forall
  -- ⋃ r, Ioc(β r - δ/2, β r + δ/2) ⊆ Ioc(-1/2, 3/2)
  intro t ht
  have ht' : t ∈ ⋃ (i : Fin R) (_ : i ∈ (Finset.univ : Finset (Fin R))),
      Set.Ioc (β i - δ / 2) (β i + δ / 2) := ht
  simp only [Set.mem_iUnion, Finset.mem_univ, Set.iUnion_true, Set.mem_Ioc] at ht'
  obtain ⟨r, hr1, hr2⟩ := ht'
  have hβr := hβ r
  rw [Set.mem_Ico] at hβr
  show t ∈ Set.Ioc (-(1:ℝ)/2) (3/2)
  rw [Set.mem_Ioc]
  exact ⟨by linarith, by linarith⟩

/-- Periodization: ∫_{-1/2}^{3/2} g = 2 ∫_0^1 g for 1-periodic g. -/
theorem integral_two_periods {g : ℝ → ℝ} (hg : Continuous g)
    (hper : Function.Periodic g 1) :
    ∫ t in (-(1:ℝ)/2)..(3/2), g t = 2 * ∫ t in (0:ℝ)..1, g t := by
  have hsplit : ∫ t in (-(1:ℝ)/2)..(3/2), g t =
      (∫ t in (-(1:ℝ)/2)..(1/2), g t) + ∫ t in ((1:ℝ)/2)..(3/2), g t := by
    rw [intervalIntegral.integral_add_adjacent_intervals
      (hg.intervalIntegrable _ _) (hg.intervalIntegrable _ _)]
  have h1 : ∫ t in (-(1:ℝ)/2)..(1/2), g t = ∫ t in (0:ℝ)..1, g t := by
    have h := hper.intervalIntegral_add_eq (-(1:ℝ)/2) 0
    simp only [zero_add] at h
    convert h using 2
    norm_num
  have h2 : ∫ t in ((1:ℝ)/2)..(3/2), g t = ∫ t in (0:ℝ)..1, g t := by
    have h := hper.intervalIntegral_add_eq ((1:ℝ)/2) 0
    simp only [zero_add] at h
    convert h using 2
    norm_num
  rw [hsplit, h1, h2]
  ring

-- ============================================================
-- Part 6: Parseval for T'
-- ============================================================

/-- T' is itself a trig polynomial with coefficients (2πnI · aₙ). -/
theorem T'_eq_T_deriv_coeffs (a : ℤ → ℂ) (S : Finset ℤ) (t : ℝ) :
    T' a S t = T (fun n => 2 * ↑Real.pi * ↑n * Complex.I * a n) S t := by
  unfold T T'
  apply Finset.sum_congr rfl
  intro n _
  ring

/-- Parseval for T': ∫₀¹ ‖T'‖² = 4π² ∑ n² ‖aₙ‖². -/
theorem parseval_T' (a : ℤ → ℂ) (S : Finset ℤ) :
    ∫ x in (0:ℝ)..1, ‖T' a S x‖ ^ 2 = ∑ n ∈ S, ‖2 * ↑Real.pi * ↑n * Complex.I * a n‖ ^ 2 := by
  simp_rw [T'_eq_T_deriv_coeffs]
  exact parseval_trig_poly_norm _ S

/-- Parseval for T: ∫₀¹ ‖T‖² = ∑ ‖aₙ‖². -/
theorem parseval_T (a : ℤ → ℂ) (S : Finset ℤ) :
    ∫ x in (0:ℝ)..1, ‖T a S x‖ ^ 2 = ∑ n ∈ S, ‖a n‖ ^ 2 :=
  parseval_trig_poly_norm a S

/-- Norm of derivative coefficient: ‖2πnI · aₙ‖² = 4π²n² ‖aₙ‖². -/
theorem norm_deriv_coeff (n : ℤ) (a : ℂ) :
    ‖2 * ↑Real.pi * ↑n * Complex.I * a‖ ^ 2 = (2 * Real.pi) ^ 2 * (n : ℝ) ^ 2 * ‖a‖ ^ 2 := by
  simp only [norm_mul, Complex.norm_real, Complex.norm_I, mul_one]
  rw [show (‖(2 : ℂ)‖ : ℝ) = 2 from by norm_num,
      show ‖Real.pi‖ = Real.pi from Real.norm_of_nonneg Real.pi_pos.le,
      show ‖(↑n : ℂ)‖ = |(n : ℝ)| from Complex.norm_real _]
  have h : |((n : ℤ) : ℝ)| ^ 2 = ((n : ℤ) : ℝ) ^ 2 := sq_abs _
  calc (2 * Real.pi * |((n : ℤ) : ℝ)| * ‖a‖) ^ 2
      = 2 ^ 2 * Real.pi ^ 2 * |((n : ℤ) : ℝ)| ^ 2 * ‖a‖ ^ 2 := by ring
    _ = 2 ^ 2 * Real.pi ^ 2 * ((n : ℤ) : ℝ) ^ 2 * ‖a‖ ^ 2 := by rw [h]
    _ = (2 * Real.pi) ^ 2 * ((n : ℤ) : ℝ) ^ 2 * ‖a‖ ^ 2 := by ring

-- ============================================================
-- Part 7: Gallagher additive large sieve
-- ============================================================

/-- **Gallagher's additive large sieve** (with explicit constant):
    For R δ-separated points in [0,1) with δ ≤ 1,
    ∑_r ‖T(αᵣ)‖² ≤ 2(δ⁻¹ + η) ∑ ‖aₙ‖² + 2η⁻¹ ∑ ‖(2πnI aₙ)‖²
    for any η > 0. -/
theorem gallagher_sum_bound {R : ℕ} (β : Fin R → ℝ) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hβ : ∀ r, β r ∈ Set.Ico (0:ℝ) 1)
    (hsep : ∀ r s, r ≠ s → δ ≤ |β r - β s|)
    (a : ℤ → ℂ) (S : Finset ℤ) {η : ℝ} (hη : 0 < η) :
    ∑ r : Fin R, ‖T a S (β r)‖ ^ 2 ≤
      2 * (δ⁻¹ + η) * (∑ n ∈ S, ‖a n‖ ^ 2) +
      2 * η⁻¹ * (∑ n ∈ S, ‖2 * ↑Real.pi * ↑n * Complex.I * a n‖ ^ 2) := by
  -- Step 1: pointwise bound for each r
  have h1 : ∑ r : Fin R, ‖T a S (β r)‖ ^ 2 ≤
      ∑ r : Fin R, ∫ t in (β r - δ/2)..(β r + δ/2), G a S δ η t :=
    Finset.sum_le_sum (fun r _ => gallagher_pointwise a S (β r) hδ hη)
  -- Step 2: disjoint intervals → integral over [-1/2, 3/2]
  have h2 : ∑ r : Fin R, ∫ t in (β r - δ/2)..(β r + δ/2), G a S δ η t ≤
      ∫ t in (-(1:ℝ)/2)..(3/2), G a S δ η t :=
    sum_interval_integrals_le β hδ hδ1 hβ hsep (G a S δ η) (continuous_G a S δ η)
      (G_nonneg a S hδ hη)
  -- Step 3: periodization
  have hGper : Function.Periodic (G a S δ η) 1 := G_periodic a S δ η
  have h3 : ∫ t in (-(1:ℝ)/2)..(3/2), G a S δ η t = 2 * ∫ t in (0:ℝ)..1, G a S δ η t :=
    integral_two_periods (continuous_G a S δ η) hGper
  -- Step 4: expand G and use Parseval
  have h4 : ∫ t in (0:ℝ)..1, G a S δ η t =
      (δ⁻¹ + η) * ∑ n ∈ S, ‖a n‖ ^ 2 +
      η⁻¹ * ∑ n ∈ S, ‖2 * ↑Real.pi * ↑n * Complex.I * a n‖ ^ 2 := by
    have hint1 : IntervalIntegrable (fun t => (δ⁻¹ + η) * ‖T a S t‖ ^ 2)
        MeasureTheory.volume (0:ℝ) 1 :=
      (continuous_const.mul (continuous_normsq_T a S)).intervalIntegrable _ _
    have hint2 : IntervalIntegrable (fun t => η⁻¹ * ‖T' a S t‖ ^ 2)
        MeasureTheory.volume (0:ℝ) 1 :=
      (continuous_const.mul (continuous_normsq_T' a S)).intervalIntegrable _ _
    calc ∫ t in (0:ℝ)..1, G a S δ η t
        = ∫ t in (0:ℝ)..1, ((δ⁻¹ + η) * ‖T a S t‖ ^ 2 + η⁻¹ * ‖T' a S t‖ ^ 2) := by
          apply intervalIntegral.integral_congr
          intro t _; unfold G; ring
      _ = (∫ t in (0:ℝ)..1, (δ⁻¹ + η) * ‖T a S t‖ ^ 2) +
          ∫ t in (0:ℝ)..1, η⁻¹ * ‖T' a S t‖ ^ 2 :=
          intervalIntegral.integral_add hint1 hint2
      _ = (δ⁻¹ + η) * ∑ n ∈ S, ‖a n‖ ^ 2 +
          η⁻¹ * ∑ n ∈ S, ‖2 * ↑Real.pi * ↑n * Complex.I * a n‖ ^ 2 := by
          rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
            parseval_T, parseval_T']
  calc ∑ r : Fin R, ‖T a S (β r)‖ ^ 2
      ≤ ∫ t in (-(1:ℝ)/2)..(3/2), G a S δ η t := le_trans h1 h2
    _ = 2 * ∫ t in (0:ℝ)..1, G a S δ η t := h3
    _ = 2 * ((δ⁻¹ + η) * ∑ n ∈ S, ‖a n‖ ^ 2 +
          η⁻¹ * ∑ n ∈ S, ‖2 * ↑Real.pi * ↑n * Complex.I * a n‖ ^ 2) := by rw [h4]
    _ = 2 * (δ⁻¹ + η) * (∑ n ∈ S, ‖a n‖ ^ 2) +
        2 * η⁻¹ * (∑ n ∈ S, ‖2 * ↑Real.pi * ↑n * Complex.I * a n‖ ^ 2) := by ring

/-- Recentering: |T(a, Icc(M+1,M+N), α)| = |T(b, Icc(0,N-1), α)|
    where b(k) = a(M+1+k). Phase factor e((M+1)α) has unit norm. -/
theorem T_recenter_norm (a : ℤ → ℂ) (M : ℤ) (N : ℕ) (α : ℝ) :
    ‖T a (Finset.Icc (M+1) (M+↑N)) α‖ =
    ‖T (fun k => a (M + 1 + k)) (Finset.Icc 0 (↑N - 1)) α‖ := by
  suffices h : T a (Finset.Icc (M+1) (M+↑N)) α =
      e ((↑M + 1) * α) * T (fun k => a (M + 1 + k)) (Finset.Icc 0 (↑N - 1)) α by
    rw [h, norm_mul, norm_e, one_mul]
  unfold T
  rw [Finset.mul_sum]
  apply Finset.sum_nbij' (fun n => n - (M + 1)) (fun k => M + 1 + k)
  · intro n hn; rw [Finset.mem_Icc] at hn ⊢; omega
  · intro k hk; rw [Finset.mem_Icc] at hk ⊢; omega
  · intro n _; omega
  · intro k _; omega
  · intro n _
    show a n * e (↑n * α) =
      e ((↑M + 1) * α) * (a (M + 1 + (n - (M + 1))) * e (↑(n - (M + 1)) * α))
    rw [show M + 1 + (n - (M + 1)) = n from by omega]
    rw [show (↑(n - (M + 1)) : ℝ) = (↑n : ℝ) - (↑M + 1) from by push_cast; ring]
    rw [show ((↑n : ℝ) - (↑M + 1)) * α = (↑n : ℝ) * α - (↑M + 1) * α from by ring]
    rw [show e ((↑M + 1) * α) * (a n * e ((↑n : ℝ) * α - (↑M + 1) * α))
        = a n * (e ((↑M + 1) * α) * e ((↑n : ℝ) * α - (↑M + 1) * α)) from by ring]
    congr 1; rw [← e_add]; congr 1; ring

/-- For k ∈ Icc 0 (N-1), k² ≤ (N-1)². -/
theorem sq_le_of_mem_range {N : ℕ} {k : ℤ} (hk : k ∈ Finset.Icc (0 : ℤ) (↑N - 1)) :
    (k : ℝ) ^ 2 ≤ (↑N - 1) ^ 2 := by
  rw [Finset.mem_Icc] at hk
  have h1 : (k : ℝ) ≤ ↑N - 1 := by exact_mod_cast hk.2
  have h2 : (0 : ℝ) ≤ k := by exact_mod_cast hk.1
  nlinarith

/-- Derivative coefficient sum bounded: ∑_{k=0}^{N-1} (2πk)²‖bₖ‖² ≤ 4π²(N-1)² ∑ ‖bₖ‖². -/
theorem deriv_coeff_sum_le (b : ℤ → ℂ) (N : ℕ) :
    ∑ k ∈ Finset.Icc (0:ℤ) (↑N - 1),
      ‖2 * ↑Real.pi * ↑k * Complex.I * b k‖ ^ 2 ≤
    (2 * Real.pi) ^ 2 * (↑N - 1) ^ 2 *
      ∑ k ∈ Finset.Icc (0:ℤ) (↑N - 1), ‖b k‖ ^ 2 := by
  simp_rw [norm_deriv_coeff]
  rw [show (2 * Real.pi) ^ 2 * (↑N - 1 : ℝ) ^ 2 * ∑ k ∈ Finset.Icc (0:ℤ) (↑N - 1), ‖b k‖ ^ 2
      = ∑ k ∈ Finset.Icc (0:ℤ) (↑N - 1), (2 * Real.pi) ^ 2 * (↑N - 1 : ℝ) ^ 2 * ‖b k‖ ^ 2
      from by rw [Finset.mul_sum]]
  apply Finset.sum_le_sum
  intro k hk
  have h := sq_le_of_mem_range hk
  have hpi2 : 0 ≤ (2 * Real.pi) ^ 2 := sq_nonneg _
  have hnb : 0 ≤ ‖b k‖ ^ 2 := sq_nonneg _
  have h2 := mul_le_mul_of_nonneg_left h hpi2
  nlinarith [mul_le_mul_of_nonneg_right h2 hnb]

/-- **Gallagher additive large sieve** (concrete form with explicit constant):
    ∑_r ‖expSum a M N (αᵣ)‖² ≤ C · (N + δ⁻¹) · ∑ ‖aₙ‖²
    where C = 8π² + 2 (any constant ≥ max(2, 8π²) works). -/
theorem gallagher_large_sieve {R : ℕ} (β : Fin R → ℝ) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hβ : ∀ r, β r ∈ Set.Ico (0:ℝ) 1)
    (hsep : ∀ r s, r ≠ s → δ ≤ |β r - β s|)
    (a : ℤ → ℂ) (M : ℤ) (N : ℕ) (hN : 0 < N) :
    ∑ r : Fin R, ‖T a (Finset.Icc (M+1) (M+↑N)) (β r)‖ ^ 2 ≤
      (8 * Real.pi ^ 2 + 2) * (↑N + δ⁻¹) * ∑ n ∈ Finset.Icc (M+1) (M+↑N), ‖a n‖ ^ 2 := by
  -- Recenter: work with b(k) = a(M+1+k), support = Icc 0 (N-1)
  set b := fun k : ℤ => a (M + 1 + k) with hb_def
  set S := Finset.Icc (0:ℤ) (↑N - 1) with hS_def
  -- norms are equal after recentering
  have hnorm_eq : ∀ r, ‖T a (Finset.Icc (M+1) (M+↑N)) (β r)‖ ^ 2 =
      ‖T b S (β r)‖ ^ 2 := by
    intro r
    rw [T_recenter_norm a M N (β r)]
  simp_rw [hnorm_eq]
  -- coefficient norms are equal
  have hcoeff_eq : ∑ n ∈ Finset.Icc (M+1) (M+↑N), ‖a n‖ ^ 2 = ∑ k ∈ S, ‖b k‖ ^ 2 := by
    apply Finset.sum_nbij' (fun n => n - (M + 1)) (fun k => M + 1 + k)
    · intro n hn; rw [Finset.mem_Icc] at hn ⊢; omega
    · intro k hk; rw [Finset.mem_Icc] at hk ⊢; omega
    · intro n _; omega
    · intro k _; omega
    · intro n _
      show ‖a n‖ ^ 2 = ‖a (M + 1 + (n - (M + 1)))‖ ^ 2
      rw [show M + 1 + (n - (M + 1)) = n from by omega]
  rw [hcoeff_eq]
  -- apply gallagher_sum_bound with η = N (as real)
  have hN' : (0:ℝ) < ↑N := Nat.cast_pos.mpr hN
  have hη : (0:ℝ) < ↑N := hN'
  have h1 := gallagher_sum_bound β hδ hδ1 hβ hsep b S hη
  -- bound the derivative term
  have h2 := deriv_coeff_sum_le b N
  -- key: (N-1)²/N ≤ N for N ≥ 1
  have hN1 : (1:ℝ) ≤ ↑N := by exact_mod_cast hN
  have hsum_nn : 0 ≤ ∑ k ∈ S, ‖b k‖ ^ 2 :=
    Finset.sum_nonneg (fun k _ => sq_nonneg _)
  have hpi2 : 0 ≤ Real.pi ^ 2 := sq_nonneg _
  -- deriv sum ≤ 4π²(N-1)² ∑‖b‖² ≤ 4π²N² ∑‖b‖²
  have h3 : (↑N - 1 : ℝ) ^ 2 ≤ (↑N : ℝ) ^ 2 := by nlinarith
  have h4 : ∑ k ∈ S, ‖2 * ↑Real.pi * ↑k * Complex.I * b k‖ ^ 2 ≤
      (2 * Real.pi) ^ 2 * (↑N : ℝ) ^ 2 * ∑ k ∈ S, ‖b k‖ ^ 2 :=
    le_trans h2 (by nlinarith [mul_le_mul_of_nonneg_right (by nlinarith : (2 * Real.pi) ^ 2 * (↑N - 1 : ℝ) ^ 2 ≤ (2 * Real.pi) ^ 2 * (↑N : ℝ) ^ 2) hsum_nn])
  -- Key simplification: N⁻¹ * N² = N (cancel one N)
  have hNne : (↑N : ℝ) ≠ 0 := by positivity
  have hNinv : (↑N : ℝ)⁻¹ * (↑N : ℝ) ^ 2 = ↑N := by
    rw [sq, ← mul_assoc, inv_mul_cancel₀ hNne, one_mul]
  -- Assemble: 2(δ⁻¹ + N) + 2·N⁻¹·4π²·N² = 2δ⁻¹ + 2N + 8π²N = 2δ⁻¹ + (8π²+2)N
  calc ∑ r, ‖T b S (β r)‖ ^ 2
      ≤ 2 * (δ⁻¹ + ↑N) * ∑ k ∈ S, ‖b k‖ ^ 2 +
        2 * (↑N)⁻¹ * ∑ k ∈ S, ‖2 * ↑Real.pi * ↑k * Complex.I * b k‖ ^ 2 := h1
    _ ≤ 2 * (δ⁻¹ + ↑N) * ∑ k ∈ S, ‖b k‖ ^ 2 +
        2 * (↑N)⁻¹ * ((2 * Real.pi) ^ 2 * (↑N : ℝ) ^ 2 * ∑ k ∈ S, ‖b k‖ ^ 2) := by
        linarith [mul_le_mul_of_nonneg_left h4 (by positivity : (0:ℝ) ≤ 2 * (↑N)⁻¹)]
    _ = (2 * δ⁻¹ + 2 * ↑N + 2 * (2 * Real.pi) ^ 2 * ((↑N)⁻¹ * (↑N : ℝ) ^ 2)) *
        ∑ k ∈ S, ‖b k‖ ^ 2 := by ring
    _ = (2 * δ⁻¹ + 2 * ↑N + 2 * (2 * Real.pi) ^ 2 * ↑N) *
        ∑ k ∈ S, ‖b k‖ ^ 2 := by rw [hNinv]
    _ = (2 * δ⁻¹ + (8 * Real.pi ^ 2 + 2) * ↑N) *
        ∑ k ∈ S, ‖b k‖ ^ 2 := by ring
    _ ≤ (8 * Real.pi ^ 2 + 2) * (↑N + δ⁻¹) *
        ∑ k ∈ S, ‖b k‖ ^ 2 := by
        apply mul_le_mul_of_nonneg_right _ hsum_nn
        have h5 : 0 ≤ 8 * Real.pi ^ 2 := by positivity
        have hdinv : 0 ≤ δ⁻¹ := by positivity
        nlinarith

end Gallagher

-- Verification: only standard Mathlib axioms, no sorry
#print axioms Gallagher.gallagher_large_sieve
#print axioms Gallagher.gallagher_sum_bound
#print axioms Gallagher.T_recenter_norm
