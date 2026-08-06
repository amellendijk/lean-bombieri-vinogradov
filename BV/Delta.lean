import Mathlib
import Architect

import BV.Mathlib.MeasureTheory.Function.LocallyIntegrable
import BV.Mathlib.Analysis.Calculus.Deriv.Slope

import BV.ForMathlib.Indicator
import BV.ForMathlib.RCLikeToComplex

import BV.Axioms
import BV.Defs

open ArithmeticFunction
open scoped Moebius zeta
open BV

/-!
### Preliminaries

Decomposing the von Mangoldt function into type I and type II functions. -/

@[blueprint (statement := /--
$$\Delta_f(x ;q, a) := \sum_{n \le x, ~ n \equiv a \pmod q} f(n) ~ - \frac{1}{\varphi(q)} \sum_{n \le x, (n, q) = 1} f(n) $$
for $x \ge 1$, $q \in \N$
-/)]
noncomputable def Delta {R : Type*} [Field R] (f : ℕ → R) (x : ℝ) (q : ℕ) (a : ZMod q) : R :=
  summatory ((Nat.modEqs (a : ZMod q)).indicator f) x -
  ((Nat.totient q : R)⁻¹) * summatory (onCoprime q f) x

theorem DirichletCharacter.inv_zmod_apply {q : ℕ} {a : ZMod q} (ha : IsUnit a)
    (χ : DirichletCharacter ℂ q) : χ⁻¹ a = χ a⁻¹ := by
  rw [MulChar.inv_apply_eq_inv']
  have hmul : χ a * χ a⁻¹ = 1 := by
    rw [← map_mul, ZMod.mul_inv_of_unit a ha, map_one]
  exact inv_eq_of_mul_eq_one_right hmul

theorem DirichletCharacter.starRingEnd_apply {q : ℕ} {a : ZMod q} (ha : IsUnit a)
    (χ : DirichletCharacter ℂ q) : starRingEnd ℂ (χ a) = χ⁻¹ a := by
  rw [MulChar.inv_apply_eq_inv']
  rw [Complex.inv_eq_conj]
  apply DirichletCharacter.unit_norm_eq_one χ ha.unit

lemma DirichletCharacter.one_natCast_apply {q : ℕ} [NeZero q] (n : ℕ) :
    (1 : DirichletCharacter ℂ q) (n : ZMod q) = if q.Coprime n then 1 else 0 := by
  split_ifs with h
  · exact MulChar.one_apply ((ZMod.isUnit_iff_coprime n q).mpr h.symm)
  · exact MulChar.map_nonunit _ (fun hu => h ((ZMod.isUnit_iff_coprime n q).mp hu).symm)

notation3 "Δ_[" f "](" x "; " q ", " a ")" => Delta f x q a

@[fun_prop]
lemma isLocallyBounded_Delta {R : Type*} [NormedField R] (f : ℕ → R) (q : ℕ) (a : ZMod q) :
    IsLocallyBounded fun x ↦ Δ_[f](x; q, a) := by
  simp [Delta]
  fun_prop

@[fun_prop]
lemma isLocallyBoundedOn_Delta {R : Type*} [NormedField R] {s : Set ℝ} (f : ℕ → R) (q : ℕ) (a : ZMod q) :
    IsLocallyBoundedOn (fun x ↦ Δ_[f](x; q, a)) s := by
  simp [Delta]
  fun_prop

open MeasureTheory in
@[fun_prop]
lemma aeStronglyMeasurable_Delta {R : Type*} [NormedField R] [MeasurableSpace R] (f : ℕ → R) (q : ℕ) (a : ZMod q) :
    AEStronglyMeasurable (fun x ↦ Δ_[f](x; q, a)) := by
  simp [Delta]
  fun_prop

@[push_cast]
lemma Complex.ofReal_setIndicator {ι : Type*} {s : Set ι} (f : ι → ℝ) (n : ι) :
  (↑(s.indicator (fun n ↦ f n) n) : ℂ) = s.indicator (fun n ↦ (f n : ℂ)) n := by
  classical
  simp [Set.indicator_apply]
  split_ifs <;> simp

@[push_cast]
lemma Complex.ofReal_onCoprime {f : ℕ → ℝ} (r n : ℕ): (↑(onCoprime r (fun n ↦ f n) n) : ℂ) = (onCoprime r (fun n ↦ (f n : ℂ)) n) := by
  simp [onCoprime]
  split_ifs <;> simp

@[norm_cast]
lemma Complex.ofReal_summatory {g : ℕ → ℝ} {x : ℝ} : (↑(summatory (fun n ↦ g n) x) : ℂ) = (summatory (fun n ↦ (g n : ℂ)) x) := by
  simp [summatory]

@[push_cast]
lemma Complex.ofReal_Delta {g : ℕ → ℝ} {x : ℝ} {q : ℕ} {a : ZMod q} : ↑(Δ_[fun n ↦ g n](x; q, a)) = Δ_[fun n ↦ (g n : ℂ)](x; q, a) := by
  simp [Delta]
  push_cast
  rfl

@[push_cast]
lemma Complex.ofReal_integral {X : Type*} [MeasurableSpace X] {«μ» : MeasureTheory.Measure X} {f : X → ℝ} : ↑(∫ (x : X), f x ∂«μ») = ∫ (x : X), (↑(f x) : ℂ) ∂«μ» := by
  apply Eq.symm
  apply integral_complex_ofReal

attribute [norm_cast] integral_complex_ofReal

attribute [push] RingHom.map_add
attribute [push] RingHom.map_sub

-- Thought: Instead of RCLike should I just take anything that ℂ is an algebra over? I don't need completeness here...
@[blueprint(statement :=
/--
$$\Delta_f(y ;q, a) = \frac{1}{\varphi(q)} \sum_{\chi \pmod{q}, \chi \ne \chi_0} \bar\chi(a) \sum_{n \le y} f(n) \chi(n) $$
-/)]
lemma Delta_eq_sum_char {𝕜 : Type*} [Field 𝕜] [Algebra 𝕜 ℂ] {f : ℕ → 𝕜} {y : ℝ} {q : ℕ} [NeZero q] {a : ZMod q}
    (ha : IsUnit a) :
    open Classical in
    (algebraMap _ _ (Delta f y q a))  = (Nat.totient q : ℂ)⁻¹ *
      ∑ χ : DirichletCharacter ℂ q, if χ ≠ 1 then
        star (χ (a : ZMod q)) * summatory (fun n => algebraMap _ _ (f n) * χ n) y
      else 0 := by
  have hφ : (Nat.totient q : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.totient_pos.mpr (NeZero.pos q)).ne'
  simp only [Delta, summatory, Nat.modEqs, onCoprime, Set.indicator_apply, Set.mem_setOf_eq]
  -- Suffices to prove the equivalent form with φ cleared
  suffices h : (q.totient : ℂ) * ∑ i ∈ Nat.Icc 1 y, algebraMap _ _ (if (i : ZMod q) = (a : ZMod q) then f i else 0) -
      ∑ i ∈ Nat.Icc 1 y, algebraMap _ _ (if q.Coprime i then f i else 0) =
      ∑ χ : DirichletCharacter ℂ q, if χ ≠ 1 then
        star (χ (a : ZMod q)) * ∑ x ∈ Nat.Icc 1 y, algebraMap _ _ (f x) * χ x else 0 by
    simp at ⊢ h
    field_simp [hφ]
    linear_combination h
  -- Let F χ = star(χ a') * ∑_n f(n) χ(n)
  set F := fun χ : DirichletCharacter ℂ q =>
    star (χ (a : ZMod q)) * ∑ x ∈ Nat.Icc 1 y, algebraMap _ _ (f x) * χ x
  -- Step 1: Split off the χ = 1 term: ∑_{χ≠1} F χ = ∑_χ F χ - F 1
  have hsplit : ∑ χ : DirichletCharacter ℂ q, (if χ ≠ 1 then F χ else 0) = ∑ χ, F χ - F 1 := by
    have hadd := Finset.add_sum_erase Finset.univ F (Finset.mem_univ (1 : DirichletCharacter ℂ q))
    rw [← hadd]
    ring_nf
    rw [← Finset.sum_filter]
    congr
    grind
  rw [hsplit]
  have hFsum : ∑ χ : DirichletCharacter ℂ q, F χ =
      (q.totient : ℂ) * ∑ i ∈ Nat.Icc 1 y, algebraMap _ _ (if (i : ZMod q) = (a : ZMod q) then f i else 0) := by
    have := DirichletCharacter.sum_char_inv_mul_char_eq ℂ ha
    simp only [F, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun y hy ↦ ?_)
    simp_rw [mul_comm <| algebraMap _ _ (f y), ← mul_assoc, ← Finset.sum_mul, MulChar.star_apply',
      DirichletCharacter.inv_zmod_apply ha, this]
    simp only [eq_comm]
    split_ifs <;> simp
  have hF1 : F 1 = ∑ i ∈ Nat.Icc 1 y, algebraMap _ _ (if q.Coprime i then f i else 0) := by
    simp only [F, MulChar.one_apply ha, star_one, one_mul, DirichletCharacter.one_natCast_apply]
    congr! 1 with n
    split_ifs <;> simp
  rw [hFsum, hF1]

-- theorem Delta_eq_summatory {f : ℕ → ℂ} {y : ℝ} {q : ℕ} [NeZero q] {a : ZMod q}
--     (ha : IsUnit a) :
--     open Classical in
--     (↑(Delta f y q a) : ℂ) = (Nat.totient q : ℂ)⁻¹ *
--       ∑ χ : DirichletCharacter ℂ q, if χ ≠ 1 then
--         star (χ (a : ZMod q)) * summatory (fun n => (f n : ℂ) * χ n) y
--       else 0 := by
--   sorry


@[blueprint (statement :=
/--
$$\Delta_{\Lambda}(x; q, a) = \psi(x; q,a) - \frac{1}{\varphi(q)} \sum_{n \le x, n \not\mid q} \Lambda{n} $$
-/
)]
theorem Delta_Lambda_eq (x : ℝ) (q : ℕ) (a : ZMod q) :
    Δ_[Λ](x; q, a) = ψ x a - (q.totient : ℝ)⁻¹ * ∑ n ∈ Nat.Icc 1 x with q.Coprime n, Λ n
   := by
  simp only [Delta, chebyPsi_eq_summatory]
  congr 2
  rw [summatory, Finset.sum_filter]
  congr! 1 with n hn

noncomputable def C_D1 (A : ℕ) : ℝ := C_SW A 0

open ProofData in
@[blueprint (statement :=
/--
For all $A \in \N$,
$$ \sum_{n \le x} \Lambda{n} = x + O_A(x/\log(x)^A)$$
-/
)]
lemma PNT [ProofData] (A : ℕ) :
    |summatory (fun n ↦ Λ n) x - x| ≤ C_D1 A * (x / Real.log x ^ A) := by
  have := siegel_walfisz A 0 le_x (q := 1) (by norm_num) (by simp) (a := 1) (by simp)
  simp [ψ_one_one] at this
  grw [summatory_vonMangoldt, this]
  rfl

lemma vonMangoldt_eq_ite_vonMangoldt (n : ℕ) : Λ n = if IsPrimePow n then Λ n else 0 := by
  simp [vonMangoldt_apply]
  grind

lemma ArithmeticFunction.mul_coe_zeta_apply (f : ArithmeticFunction ℝ) (n : ℕ) : (f * ζ) n = ∑ d ∈ n.divisors, f d := by
  rw [ArithmeticFunction.mul_apply, Nat.sum_divisorsAntidiagonal (f := fun i j ↦ f i * (↑ζ : ArithmeticFunction ℝ) j)]
  congr! with d hd
  simp only [Nat.mem_divisors, ne_eq] at hd
  simp only [natCoe_apply, zeta_apply, Nat.div_eq_zero_iff, Nat.cast_ite, CharP.cast_eq_zero,
    Nat.cast_one, mul_ite, mul_zero, mul_one, ite_eq_right_iff]
  have : d ≤ n := Nat.le_of_dvd (by grind) hd.1
  rintro (hd' | hnd)
  · simp only [zero_dvd_iff, and_not_self, hd'] at hd
  · grind

open ProofData in
lemma sum_vonMangoldt_le_log [ProofData] {k : ℕ} (hk : 0 < k) {q : ℕ} (hq : 0 < q) :
    |∑ p ∈ Finset.Ioc 0 ⌊x ^ ((1:ℝ) / k)⌋₊ with Nat.Prime p, if ¬q.Coprime (p ^ k) then Λ p else 0| ≤ log q := by
  have {p : ℕ} (hp : p.Prime) : ¬ q.Coprime (p^k) ↔ p ∣ q := by
    rw [Nat.coprime_comm]
    simp only [Nat.coprime_pow_left_iff, hk, Nat.Prime.coprime_iff_not_dvd hp, Decidable.not_not]
  rw [abs_of_nonneg ?A]
  case A =>
    -- TODO: Make positivity work.
    apply Finset.sum_nonneg fun _ _ ↦ ?_
    split_ifs <;> simp
  simp +contextual (disch := grind) only [this]
  simp_rw [← Finset.sum_filter]
  trans ∑ d ∈ q.divisors, Λ d
  · gcongr
    · intro d
      simp only [Finset.mem_filter, Finset.mem_Ioc, Nat.mem_divisors, ne_eq, and_imp]
      grind
  · apply le_of_eq
    rw [← ArithmeticFunction.vonMangoldt_mul_zeta, ArithmeticFunction.mul_coe_zeta_apply]

-- Variant of Chebyshev.sum_PrimePow_eq_sum_sum that's more syntactically general, but with an additional assumption.
open Finset in
theorem sum_PrimePow_eq_sum_sum_of_eq_zero {R : Type*} [AddCommMonoid R] (f : ℕ → R) {x : ℝ} (hx : 0 ≤ x) (hf : ∀ n : ℕ, 0 < n → n ≤ x → ¬ IsPrimePow n → f n = 0) :
    ∑ n ∈ Ioc 0 ⌊x⌋₊, f n
      = ∑ k ∈ Icc 1 ⌊Real.log x / Real.log 2⌋₊, ∑ p ∈ Ioc 0 ⌊x ^ ((1 : ℝ) / k)⌋₊ with p.Prime, f (p ^ k) := by
  rw [← Chebyshev.sum_PrimePow_eq_sum_sum, Finset.sum_filter]
  congr! with n hn
  · simp only [mem_Ioc, Nat.le_floor_iff, hx] at hn
    simpa using hf n hn.1 hn.2
  · exact hx

private noncomputable def C_SVNC : ℝ := (Real.log 2)⁻¹

theorem C_SVNC_le : C_SVNC ≤ (Real.log 2)⁻¹ := le_rfl

open ProofData in
@[blueprint (statement :=
/--
For all $A \in \N$,
$$ \sum_{n \le x, (q, n) \ne 1} \Lambda{n} \ll \log q \log x$$
-/
)]
lemma sum_vonMangoldt_not_coprime_ll_logq [ProofData] {q : ℕ} (hq : 0 < q) :
  |summatory (fun n ↦ if ¬ q.Coprime n then Λ n else 0) x| ≤ C_SVNC * (Real.log q * Real.log x) := by
  simp_rw [summatory_apply]
  rw [sum_PrimePow_eq_sum_sum_of_eq_zero]
  · grw [Finset.abs_sum_le_sum_abs]
    simp +contextual (disch := grind) only [ArithmeticFunction.vonMangoldt_apply_pow]
    trans (∑ x ∈ Finset.Icc 1 ⌊Real.log x / Real.log 2⌋₊, Real.log q)
    · gcongr with d hd
      -- TODO: fix bad convert
      convert sum_vonMangoldt_le_log _ hq
      · rfl
      · simp
      · grind
    simp only [Finset.sum_const, Nat.card_Icc, add_tsub_cancel_right, nsmul_eq_mul]
    grw [Nat.floor_le (by positivity), C_SVNC]
    apply le_of_eq
    ring
  · linarith only [le_x]
  · simp +contextual [vonMangoldt_eq_zero_iff]

lemma summatory_sub_ite {P : ℕ → Prop} [DecidablePred P] (f : ℕ → ℝ) {x : ℝ} :
    summatory f x - summatory (fun n ↦ if P n then f n else 0) x =
    summatory (fun x ↦ if ¬ P x then f x else 0) x := by
  pull summatory
  congr with n
  split_ifs <;> ring

open ProofData in
@[blueprint (statement :=
/--
For all $A \in \N$,
$$ \sum_{n \le x, n \not \mid q} \Lambda{n} = x + O_A(x/\log(x)^A+\log q \log x)$$
-/
)]
lemma sum_primes_not_dvd_log_eq_id [ProofData] (A : ℕ) {q : ℕ} (hq : 0 < q) :
  |summatory (fun n ↦ if q.Coprime n then Λ n else 0) x - x|
    ≤ C_D1 A * (x / Real.log x ^ A) + C_SVNC * (Real.log q * Real.log x) := by
  grw [abs_sub_le (b := (summatory (fun n ↦ Λ n) x)), PNT A, abs_sub_comm, summatory_sub_ite,
    sum_vonMangoldt_not_coprime_ll_logq hq]
  apply le_of_eq
  ring

noncomputable def ArithmeticFunction.twist {𝕜 : Type*} [Field 𝕜] [Algebra 𝕜 ℂ] {q : ℕ} (f : ArithmeticFunction 𝕜) (c : DirichletCharacter ℂ q)  : ArithmeticFunction ℂ := ⟨
  fun n ↦ algebraMap _ _ (f n) * c n,
  by simp
⟩

@[simp]
theorem ArithmeticFunction.twist_apply {𝕜 : Type*} [Field 𝕜] [Algebra 𝕜 ℂ] {q : ℕ} {f : ArithmeticFunction 𝕜} {χ : DirichletCharacter ℂ q} {n : ℕ} :
    f.twist χ n = algebraMap _ _ (f n) * χ ↑n := rfl

open ArithmeticFunction in
theorem ArithmeticFunction.mul_twist {𝕜 : Type*} [Field 𝕜] [Algebra 𝕜 ℂ] {q : ℕ} (f g : ArithmeticFunction 𝕜) (χ : DirichletCharacter ℂ q) (n : ℕ) :
    (f * g).twist χ n = (f.twist χ * g.twist χ) n := by
  simp [← mul_assoc, Finset.sum_mul]
  congr! 1 with ⟨a, b⟩ hab
  simp only [Nat.mem_divisorsAntidiagonal, ne_eq] at hab
  rw [← hab.1]
  simp only [Nat.cast_mul, map_mul]
  ring

theorem ArithmeticFunction.summatory_mul_eq_summatory {R : Type*} [Semiring R] (f g : ArithmeticFunction R) (x : ℝ) :
    summatory (f * g) x  = summatory (fun n ↦ f n * summatory g (x/n)) x := by
  have := ArithmeticFunction.sum_Ioc_mul_eq_sum_sum f g (⌊x⌋₊)
  simp_rw [summatory_apply, this, Nat.floor_div_natCast]

@[push]
lemma Finset.sum_summatory_comm {ι R : Type*} [DecidableEq ι] {s : Finset ι} [AddCommMonoid R] (f : ι → ℕ → R) {x : ℝ} :
    ∑ i ∈ s, summatory (f i) x = summatory (fun n ↦ ∑ i ∈ s, f i n) x := by
  simp [summatory_apply]
  rw [Finset.sum_comm]

@[push]
lemma Finset.summatory_sum_comm {ι R : Type*} [DecidableEq ι] {s : Finset ι} [AddCommMonoid R] (f : ι → ℕ → R) {x : ℝ} :
    summatory (fun n ↦ ∑ i ∈ s, f i n) x = ∑ i ∈ s, summatory (f i) x := by
  exact (sum_summatory_comm ..).symm

lemma ZMod.isUnit_inv' {q : ℕ} (n : ZMod q) : IsUnit n → IsUnit n⁻¹ := by
  intro h
  rw [isUnit_iff_exists]
  exact ⟨n, ZMod.inv_mul_of_unit _ h, ZMod.mul_inv_of_unit _ h⟩

@[blueprint (latexEnv := "lemma") (statement := /--
If $f$ is an arithmetic function supported on $[1, y]$ then
$$\Delta_{f*g}(x;\,q,\,a) = \sum_{\substack{k \le y \\ (k,q)=1}} f(k)\, \Delta_g\!\left(\frac{x}{k};\, q,\, a\bar{k}\right)$$
-/)]
theorem Delta_convolution_eq {𝕜 : Type*} [Field 𝕜] [Algebra 𝕜 ℂ] {y : ℝ} {q : ℕ} [NeZero q] {a : ZMod q} (ha : IsUnit a) (f g : ArithmeticFunction 𝕜) :
    Δ_[f*g](y; q, a) = summatory (fun k ↦ if k.Coprime q then f k * Δ_[g](y/k; q, a * (k : ZMod q)⁻¹) else 0) y := by
  apply_fun algebraMap 𝕜 ℂ
  rw [Delta_eq_sum_char (f := (f*g))]
  simp_rw [← twist_apply, mul_twist, ← Finset.sum_filter]
  simp_rw [summatory_mul_eq_summatory]
  simp only [twist_apply]
  pull summatory
  simp only [map_summatory, apply_ite, map_mul]
  congr! 2 with n
  split_ifs with hn
  · rw [Delta_eq_sum_char, ← Finset.sum_filter]
    · pull summatory
      congr! 1 with m
      simp only [ne_eq, RCLike.star_def, map_mul, star_mul']
      simp_rw [Finset.mul_sum]
      congr! 1 with χ hχ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hχ
      rw [← DirichletCharacter.inv_zmod_apply, ← DirichletCharacter.starRingEnd_apply]
      · simp; ring
      · simpa [ZMod.isUnit_iff_coprime] using hn
      · simpa [ZMod.isUnit_iff_coprime] using hn
    · simp [ha]
      apply ZMod.isUnit_inv'
      simpa [ZMod.isUnit_iff_coprime] using hn
  · have : ¬ IsUnit (n : ZMod q) := by simp [ZMod.isUnit_iff_coprime, hn]
    simp [this, MulChar.map_nonunit, summatory_zero]
  · exact ha
  · apply RingHom.injective

-- theorem Delta_convolution_eq_real {y : ℝ} {q : ℕ} [NeZero q] {a : ZMod q} (ha : IsUnit a) (f g : ArithmeticFunction ℝ) :
--     Δ_[f*g](y; q, a) = summatory (fun k ↦ if k.Coprime q then f k * Δ_[g](y/k; q, a * (k : ZMod q)⁻¹) else 0) y := by
--   apply_fun Complex.ofReal
--   push_cast
--   · have {n : ℕ} : ((f * g) n) = ((algebraMap _ _ f) * ↑g : ArithmeticFunction ℂ) n := by
--       sorry
--     sorry
--   · exact Complex.ofReal_injective

/-! ### Periodic function lemmas for Delta_one_bound -/

-- Perhaps we're supposed to unfold Function.Periodic?
theorem Function.Periodic.add_period_apply {α β : Type*} [Add α] {f : α → β} {c : α} (hf : f.Periodic c) (a : α) :
    f (a + c) = f a := hf a

theorem Function.Periodic.period_add_apply {α β : Type*} [AddCommMonoid α] {f : α → β} {c : α} (hf : f.Periodic c) (a : α) :
    f (c + a) = f a := by
  rw [add_comm, hf.add_period_apply]

/-- Rewrite `summatory` as a sum over `Finset.range` with a shift. -/
lemma summatory_eq_sum_range {R : Type*} [AddCommMonoid R] {f : ℕ → R} {x : ℝ} :
    summatory f x = ∑ n ∈ Finset.range ⌊x⌋₊, f (n + 1) := by
  rw [summatory_apply, ← Finset.sum_image (g := (· + 1))]
  · congr
    ext n
    simp only [Finset.mem_Ioc, Finset.mem_image, Finset.mem_range]
    refine ⟨?_, by grind⟩
    rintro ⟨hn_pos, hnx⟩
    use n-1
    grind
  · simp

/-- Sum of a periodic function over `k` full periods. -/
lemma sum_range_periodic {R : Type*} [AddCommMonoid R] [Module ℕ R]
    {f : ℕ → R} {q : ℕ} (hf : f.Periodic q) (k : ℕ) :
    ∑ n ∈ Finset.range (k * q), f n = k • ∑ n ∈ Finset.range q, f n := by
  induction k with
  | zero => simp
  | succ k hk =>
    simp [add_mul, Finset.sum_range_add]
    rw [hk, ← smul_eq_mul k q]
    simp_rw [(hf.nsmul k).period_add_apply, succ_nsmul]

/-- Sum of a periodic function splits into full periods plus a remainder. -/
lemma sum_range_periodic_mod {R : Type*} [AddCommMonoid R] [Module ℕ R]
    {f : ℕ → R} {q : ℕ} (hf : f.Periodic q) (N : ℕ) :
    ∑ n ∈ Finset.range N, f n =
      (N / q) • ∑ n ∈ Finset.range q, f n + ∑ n ∈ Finset.range (N % q), f n := by
  conv_lhs => rw [← Nat.div_add_mod N q, Finset.sum_range_add, mul_comm q]
  rw [sum_range_periodic hf, ← smul_eq_mul]
  congr 1
  simp only [(hf.nsmul (N/q)).period_add_apply]

/-- The modular residue indicator of a constant function is periodic with period `q`. -/
lemma indicator_modEqs_periodic {q : ℕ} (a : ZMod q) (c : ℝ) :
    Function.Periodic ((Nat.modEqs a).indicator (fun _ => c)) q := by
  classical
  simp [Set.indicator_apply]

/-- The coprimality indicator of a constant function is periodic with period `q`. -/
lemma onCoprime_periodic (q : ℕ) (c : ℝ) :
    Function.Periodic (onCoprime q (fun _ => c)) q := by
  classical
  intro n
  simp [onCoprime_apply]

/-- In one full period `{0, …, q-1}`, the indicator of `n ≡ a (mod q)` sums to `1`,
    when `a` is a unit. -/
lemma sum_range_indicator_modEqs {q : ℕ} [NeZero q] {a : ZMod q} :
    ∑ n ∈ Finset.range q, (Nat.modEqs a).indicator (fun _ => (1 : ℝ)) n = 1 := by
  classical
  simp [Set.indicator_apply, Finset.card_eq_one]
  use a.val
  ext n
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
  constructor
  -- I'm surprised `grind` wasn't of more use here...
  · rintro ⟨h, rfl⟩
    simp [Nat.mod_eq_of_lt h]
  · rintro rfl
    simp only [ZMod.natCast_val, ZMod.cast_id', id_eq, and_true, a.val_lt]

theorem sum_range_of_periodic_full_eq_add {R : Type*} [AddCommMonoid R] {a q : ℕ} (f : ℕ → R) (hf : f.Periodic q) :
    ∑ i ∈ Finset.range q, f i = ∑ i ∈ Finset.range q, f (i + a) := by
  by_cases hq : q = 0
  · simp [hq]
  have hq : 0 < q := by grind
  conv_rhs => rw [← Finset.sum_image (by simp)]
  rw [eq_comm]
  apply Finset.sum_bij (i := fun x _ ↦ (x % q))
  · simp +contextual [Nat.mod_lt _ hq]
  · simp
    intro x hx y hy hxy
    have : x ≡ y [MOD q] := Nat.ModEq.add_right_cancel' _ hxy
    apply Nat.ModEq.eq_of_lt_of_lt this hx hy
  · simp
    intro b hb
    have h : 0 ≤ (b - a : ℤ) % q := by
      apply Int.emod_nonneg _ (by positivity)
    let c : ℕ := ((b - a : ℤ) % q).natAbs
    refine ⟨c, ?_, ?_⟩
    · zify
      simp [c, abs_of_nonneg h]
      apply Int.emod_lt _ (by positivity)
    · rw [← Nat.mod_eq_of_lt hb, ← Nat.ModEq, ← Int.natCast_modEq_iff]
      simp [c]
      rw [abs_of_nonneg]
      · grw [Int.mod_modEq]
        simp
      · apply Int.emod_nonneg _ (by positivity)
  · simp [hf.map_mod_nat]

-- TODO: Consider other proof: use a-1 instead of constructing bijection.
/-- In one full period `{1, …, q}`, the indicator of `n ≡ a (mod q)` sums to `1`,
    when `a` is a unit. -/
lemma sum_range_indicator_modEqs_add_one {q : ℕ} [hq : NeZero q] {a : ZMod q} :
    ∑ n ∈ Finset.range q, (Nat.modEqs a).indicator (fun _ => (1 : ℝ)) (n+1) = 1 := by
  rw [← sum_range_of_periodic_full_eq_add (a := 1), sum_range_indicator_modEqs (a := a)]
  apply indicator_modEqs_periodic

/-- In one full period `{0, …, q-1}`, the coprime indicator sums to `φ(q)`. -/
lemma sum_range_onCoprime_zeta {q : ℕ} :
    ∑ n ∈ Finset.range q, onCoprime q (fun _ => (1 : ℝ)) (n) = (Nat.totient q : ℝ) := by
  simp [onCoprime_apply, Nat.totient_eq_card_coprime]

/-- In one full period `{1, …, q}`, the coprime indicator sums to `φ(q)`. -/
lemma sum_range_onCoprime_zeta_add_one {q : ℕ} :
    ∑ n ∈ Finset.range q, onCoprime q (fun _ => (1 : ℝ)) (n+1) = (Nat.totient q : ℝ) := by
  rw [← sum_range_of_periodic_full_eq_add]
  · apply sum_range_onCoprime_zeta
  · apply onCoprime_periodic

theorem apply_mem_range_iff_mem_range_comp {α β : Type*} {f : α → β} [AddCommGroup β] (a b : β) :
  (a + b) ∈ Set.range f ↔ a ∈ Set.range (fun n ↦ f n - b) := by
  grind

attribute [simp] Nat.mod_le

theorem sum_range_modEq {q : ℕ} {a : ZMod q} [hq : NeZero q] (n : ℕ) :
    ∃ c : ℝ, 0 ≤ c ∧ c ≤ 1 ∧
    ∑ m ∈ Finset.range n, (Nat.modEqs a).indicator (fun _ ↦ (1 : ℝ)) (m + 1) = (n / q : ℕ) + c := by
  classical
  use ∑ n ∈ Finset.range (n % q), (Nat.modEqs a).indicator (fun _ => (1 : ℝ)) (n+1)
  refine ⟨by positivity, ?B, ?_⟩
  case B =>
    conv_rhs => rw [← sum_range_indicator_modEqs_add_one (q := q) (a := a)]
    gcongr
    · exact (Nat.mod_lt n hq.pos).le
  rw [sum_range_periodic_mod ((indicator_modEqs_periodic a 1).add_const 1)]
  congr 1
  · simp [sum_range_indicator_modEqs_add_one]

theorem sum_range_onCoprime {q : ℕ} (n : ℕ):
    ∑ m ∈ Finset.range n, onCoprime q (fun _ ↦ (1 : ℝ)) (m + 1) = q.totient * (n / q : ℕ) + ∑ m ∈ Finset.range (n % q), onCoprime q (fun _ ↦  (1 : ℝ)) (m+1) := by
  rw [sum_range_periodic_mod ((onCoprime_periodic q 1).add_const 1) n]
  simp [sum_range_onCoprime_zeta_add_one]
  ring

theorem summatory_zeta_eq {x : ℝ} : summatory (ζ : ArithmeticFunction ℝ) x = summatory (fun _ ↦ 1) x := by
  congr! with n hn_pos hnx
  simp only [natCoe_apply, zeta_apply, Nat.cast_ite, CharP.cast_eq_zero, Nat.cast_one,
    ite_eq_right_iff, zero_ne_one, imp_false]
  grind

@[congr]
theorem Set.indicator_apply_congr {α β : Type*} [Zero β] (r s : Set α) (f g : α → β) (a b : α) (hab : a = b) (hrs : r = s) (hfg : ∀ n, n = a → f n = g n) :
    r.indicator f a = s.indicator g b := by
  classical
  subst_vars
  by_cases h : b ∈ s
  · simp [h, hfg]
  · simp [h]

theorem Delta_zeta_eq_Delta_one {x : ℝ} {q : ℕ} (a : ZMod q) :
    Δ_[(ζ : ArithmeticFunction ℝ)](x; q, a) = Δ_[fun _ ↦ (1 : ℝ)](x; q, a) := by
  simp [Delta]
  congr! 2 with n hn hnx
  · congr! 1 with n rfl
    grind
  · congr! 2 with n hn hnx n rfl hqn
    grind

@[blueprint (latexEnv := "lemma") (statement := /--
For $x \ge 1$, $q \in \N$ and $a \in (\Z/q\Z)^*$,
$$|\Delta_1(x;\, q,\, a)| \le 1$$
-/) (proof := /--
Carefully consider length $q$ intervals. Alternatively, write
$$\Delta_1(t;\, q,\, a) = \frac{1}{\varphi(q)} \sum_{a' \in (\Z/q\Z)^*} \left( \sum_{\substack{n \le t \\ n \equiv a \pmod{q}}} 1 - \sum_{\substack{n \le t \\ n \equiv a' \pmod{q}}} 1 \right)$$
and note each inner difference is bounded by $1$ in absolute value.
-/)]
theorem Delta_one_bound {x : ℝ} {q : ℕ} (a : ZMod q) (hq : 0 < q) : ‖Δ_[fun _ ↦ (1 : ℝ)](x; q, a)‖ ≤ 1 := by
  have : NeZero q := ⟨hq.ne.symm⟩
  simp [Delta, summatory_eq_sum_range]
  obtain ⟨c, ⟨hc_nonneg, hc_le, h⟩⟩ := sum_range_modEq (q := q) (a := a) ⌊x⌋₊
  rw [h, sum_range_onCoprime]
  rw [abs_le]
  have : 0 < (q.totient : ℝ) := by
    norm_cast
    simp [Nat.totient_pos, hq]
  field_simp
  have : (0 : ℝ) ≤ ∑ x ∈ Finset.range (⌊x⌋₊ % q), onCoprime q (fun _ ↦ (1:ℝ)) (x+1) := by
    positivity
  have : ∑ x ∈ Finset.range (⌊x⌋₊ % q), onCoprime q (fun _ ↦ (1 : ℝ)) (x+1) ≤ q.totient := by
    trans ∑ x ∈ Finset.range q, onCoprime q (fun _ ↦ (1 : ℝ)) (x+1)
    · gcongr
      apply (Nat.mod_lt _ hq).le
    · rw [sum_range_onCoprime_zeta_add_one]
  -- TODO: Make this neater.
  refine ⟨by nlinarith, by nlinarith⟩

-- TODO: make this proof pretty.
/-- Abel summation stated interms of `summatory`. -/
theorem abel_summation_summatory {𝕜 : Type*} [RCLike 𝕜] (c : ℕ → 𝕜) {f f' : ℝ → 𝕜}
    {a b : ℝ} (hac : ∀ n : ℕ, 0 < n → n ≤ a → c n * f n = 0) (ha : 0 ≤ a) (hab : a ≤ b)
    (hf_diff : ∀ t ∈ Set.Icc a b, HasDerivAt f (f' t) t)
    (hf_int : MeasureTheory.LocallyIntegrableOn f' (Set.Icc a b)) :
    summatory (fun k ↦ f k * c k) b = f b * summatory c b - f a * summatory c a
      - ∫ t in Set.Ioc a b, f' t * summatory c t := by
  wlog hc : c 0 = 0 generalizing c with ih
  · let c' (n : ℕ) := if n = 0 then 0 else c n
    have {x : ℝ} : summatory c x = summatory c' x := by
      congr! 1 with n hn_pos hnx
      grind
    simp_rw [this]
    rw [← ih]
    · congr! 1 with n hn_pos hnb
      grind
    · simp +contextual [c', hac]
    · simp [c']
  -- Convert from f' to deriv f to match the mathlib API.
  have  hf' (t : ℝ) (ht : t ∈ Set.Icc a b) : f' t = deriv f t := (hf_diff t ht).deriv.symm
  have : ∫ (t : ℝ) in Set.Ioc a b, f' t * summatory c t = ∫ (t : ℝ) in Set.Ioc a b, deriv f t * summatory c t := by
    simp_rw [← MeasureTheory.integral_Icc_eq_integral_Ioc]
    apply MeasureTheory.integral_congr_ae
    filter_upwards [MeasureTheory.ae_restrict_mem (measurableSet_Icc)]
    simp +contextual [hf']
  simp_rw [this]
  have hf_int : MeasureTheory.LocallyIntegrableOn (deriv f) (Set.Icc a b) := by
    apply hf_int.congr
    filter_upwards [MeasureTheory.ae_restrict_mem (measurableSet_Icc)]
    exact hf'
  have hf_diff : ∀ t ∈ Set.Icc a b, DifferentiableAt ℝ f t := by
    exact fun t ht ↦ (hf_diff t ht).differentiableAt
  -- Complete the actual proof
  have hf_int : MeasureTheory.IntegrableOn (deriv f) (Set.Icc a b) := by
    apply MeasureTheory.LocallyIntegrableOn.integrableOn_isCompact hf_int
    apply ConditionallyCompleteLinearOrder.isCompact_Icc
  simp_rw [summatory_apply]
  trans ∑ k ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊, f k * c k
  · rw [eq_comm]
    apply Finset.sum_subset
    · gcongr; simp
    · simp only [Finset.mem_Ioc, not_and, not_le, and_imp, mul_comm]
      intro k hk_pos hkb habk
      apply hac k hk_pos
      rw [← Nat.le_floor_iff ha]
      grind
  rw [sum_mul_eq_sub_sub_integral_mul c  ha hab hf_diff hf_int]
  · have {n : ℕ} : ∑ k ∈ Finset.Icc 0 n, c k = ∑ k ∈ Finset.Ioc 0 n, c k := by
      rw [eq_comm]
      apply Finset.sum_subset
      · exact Finset.Ioc_subset_Icc_self
      simp only [Finset.mem_Icc, zero_le, true_and, Finset.mem_Ioc, not_and, not_le]
      grind
    simp [this]

/-
Notes:
The API surrounding LocallyIntegrableOn is annoying and disjointed.
The main problem is that proving f*g is locally integrable basically requires one of the two functions to be continuous.
-/
open MeasureTheory in
@[blueprint (latexEnv := "lemma") (statement := /--
If $g$ is continuously differentiable on $[1, x]$ then
$$\Delta_g(x;\,q,\,a) = \Delta_1(x;\,q,\,a)\,g(x) - \int_1^x \Delta_1(t;\,q,\,a)\,g'(t)\,\mathrm{d}t$$
-/) (proof := /--
By Abel summation.
-/) (uses := [Delta_one_bound])]
theorem Delta_abel_summation {q : ℕ} [hq : NeZero q] {a : ZMod q} (ha : IsUnit a) (g g' : ℝ → ℂ) {x : ℝ} (hx : 1 ≤ x)
    (hg : ∀ t ∈ Set.Icc 1 x, HasDerivAt g (g' t) t)
    (hg_int : MeasureTheory.LocallyIntegrableOn g' (Set.Icc 1 x))
    (hg_one : g 1 = 0) :
    Δ_[fun n ↦ g n](x; q, a) = Δ_[fun _ ↦ (1 : ℂ)](x; q, a) * g x - ∫ t in Set.Ioc 1 x, Δ_[fun _ ↦ (1 : ℂ)](t; q, a) * g' t := by
  -- TODO: Figure out if we want to phrase this nicer.
  have test {f x} := Delta_eq_sum_char (𝕜 := ℂ) ha (y := x) (q := q) (f := f)
  simp only [Algebra.algebraMap_self, RingHom.id_apply] at test
  simp_rw [test]
  simp_rw [← Finset.sum_filter, Finset.mul_sum, Finset.sum_mul]
  rw [MeasureTheory.integral_finsetSum _ ?A, ← Finset.sum_sub_distrib]
  case A =>
    intro χ hχ
    rw [← IntegrableOn]
    apply IntegrableOn.mono_set (t := Set.Icc 1 x) _ (by grind)
    apply MeasureTheory.LocallyIntegrableOn.integrableOn_isCompact _ ?compact
    case compact => apply ConditionallyCompleteLinearOrder.isCompact_Icc
    pull summatory
    simp_rw [summatory_mul]
    apply hg_int.isLocallyBoundedOn_mul
    · measurability
    · fun_prop -- Wahoo! The API for locally bounded functions works!
    · fun_prop
  simp_rw [mul_assoc, MeasureTheory.integral_const_mul, ← mul_sub]
  congr! 3 with χ hχ
  let c : ℕ → ℂ := fun n ↦ χ n
  have := abel_summation_summatory (c := c) (f := (fun n ↦ g n)) (b := x) ?A (a := 1) (by norm_num) hx hg hg_int
  case A =>
    intro n _ hn
    norm_cast at hn
    simp [hg_one, show n = 1 by lia]
  rw [this]
  congr! 1
  · simp [hg_one, c, mul_comm]
  congr! 2 with x
  simp [mul_comm, c]

-- There really ought to be an RCLike version.
theorem Delta_abel_summation_real {q : ℕ} [hq : NeZero q] {a : ZMod q} (ha : IsUnit a) (g g' : ℝ → ℝ) {x : ℝ} (hx : 1 ≤ x)
    (hg : ∀ t ∈ Set.Icc 1 x, HasDerivAt g (g' t) t)
    (hg_int : MeasureTheory.LocallyIntegrableOn g' (Set.Icc 1 x))
    (hg_one : g 1 = 0) :
    Δ_[fun n ↦ g n](x; q, a) = Δ_[fun _ ↦ (1 : ℝ)](x; q, a) * g x - ∫ t in Set.Ioc 1 x, Δ_[fun _ ↦ (1 : ℝ)](t; q, a) * g' t := by
  apply_fun Complex.ofReal
  · push_cast
    apply Delta_abel_summation (g := fun n ↦ g n) (g' := fun t ↦ (g' t : ℂ)) ha (x := x) hx ?diff ?int (by simpa using hg_one)
    case diff =>
      intro t ht
      exact (hg t ht).ofReal_comp
    case int =>
      exact hg_int.ofReal
  · exact Complex.ofReal_injective


-- theorem Complex.deriv_ofReal_comp {f : ℝ → ℝ} {x : ℝ} : deriv (fun n ↦ (f n : ℂ)) = Complex.ofReal ∘ deriv f := by
--   ext x
--   simp only [Function.comp_apply]
--   by_cases hf : DifferentiableAt ℝ f x
--   · have := hf.hasDerivAt
--     have := this.ofReal_comp
--     rw [← hf.hasDerivAt.ofReal_comp.deriv]
--   · sorry

theorem Complex.ofReal_lipschitzWith : LipschitzWith 1 Complex.ofReal := by
  simp only [LipschitzWith, edist_dist, ENNReal.coe_one, one_mul, dist_nonneg,
    ENNReal.ofReal_le_ofReal_iff]
  simp_rw [SeminormedAddGroup.dist_eq]
  intro x y
  norm_cast

theorem Complex.ofReal_antilipschitzWith : AntilipschitzWith 1 Complex.ofReal := by
  simp only [AntilipschitzWith, edist_dist, ENNReal.coe_one, one_mul, dist_nonneg,
    ENNReal.ofReal_le_ofReal_iff]
  simp_rw [SeminormedAddGroup.dist_eq]
  intro x y
  norm_cast

attribute [fun_prop] MeasureTheory.LocallyIntegrableOn.norm

open MeasureTheory in
theorem Delta_monotone_bound_aux {q : ℕ} [hq : NeZero q] {a : ZMod q} (ha : IsUnit a) (g g' : ℝ → ℝ) {x : ℝ} (hx : 1 ≤ x)
    (hg : ∀ t ∈ Set.Icc 1 x, HasDerivAt g (g' t) t)
    (hg_int : MeasureTheory.LocallyIntegrableOn g' (Set.Icc 1 x))
    (hg_mono : MonotoneOn g (Set.Icc 1 x))
    (hg_one : g 1 = 0)
    :
    ‖Δ_[fun n ↦ g n](x; q, a)‖ ≤ 2 * g x := by
  have hg_nonneg {y : ℝ} (hy : 1 ≤ y) (hy' : y ≤ x) : 0 ≤ g y := hg_one ▸ hg_mono (by simpa using hx) (by simp [hy, hy']) hy
  have hg'_nonneg {y : ℝ} (hy : 1 < y) (hy' : y < x) : 0 ≤ g' y := by
    simp only [Set.mem_Icc, and_imp] at hg
    apply (hg y hy.le hy'.le).nonneg_of_monotoneOn_of_mem_nhds hg_mono
    simp
    grind
  grw [Delta_abel_summation_real ha g g' hx hg hg_int hg_one, norm_sub_le, two_mul, norm_mul, Delta_one_bound _ hq.pos]
  gcongr
  · simp only [Real.norm_eq_abs, one_mul]
    rw [abs_of_nonneg]
    apply hg_nonneg hx le_rfl
  · grw [norm_integral_le_integral_norm]
    trans ∫ x in Set.Ioc 1 x, g' x
    · simp_rw [MeasureTheory.integral_Ioc_eq_integral_Ioo]
      gcongr
      · rw [← integrableOn_Icc_iff_integrableOn_Ioo]
        apply MeasureTheory.LocallyIntegrableOn.integrableOn_isCompact
        · simp_rw [norm_mul]
          -- We can't fun_prop this lemma, as we have to make a choice of which term is bounded
          apply LocallyIntegrableOn.isLocallyBoundedOn_mul
          · simp
          · fun_prop
          · fun_prop
          · fun_prop
        · apply ConditionallyCompleteLinearOrder.isCompact_Icc
      · rw [← integrableOn_Icc_iff_integrableOn_Ioo]
        apply MeasureTheory.LocallyIntegrableOn.integrableOn_isCompact
        · exact hg_int
        · apply ConditionallyCompleteLinearOrder.isCompact_Icc
      · simp
      · grw [norm_mul, Delta_one_bound, one_mul, Real.norm_of_nonneg]
        · grind
        · exact hq.pos
    · apply le_of_eq
      rw [← intervalIntegral.integral_of_le, intervalIntegral.integral_eq_sub_of_hasDerivAt (f := g)]
      · simp [hg_one]
      · simpa [hx] using hg
      · rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hx, ← integrableOn_Icc_iff_integrableOn_Ioc]
        apply MeasureTheory.LocallyIntegrableOn.integrableOn_isCompact
        · exact hg_int
        · apply ConditionallyCompleteLinearOrder.isCompact_Icc
      · exact hx

open MeasureTheory in
--TODO : Add g 0 = 0 condition and remove ‖‖
@[blueprint (latexEnv := "lemma") (statement := /--
If $g$ is continuously differentiable and monotone on $[1, x]$ with $g(1) = 0$, then for all $t \ge 1$ and $a \in (\Z/q\Z)^*$,
$$|\Delta_g(x;\, q,\, a)| \le 2g(x)$$
-/) (uses := [Delta_one_bound, Delta_abel_summation])]
theorem Delta_monotone_bound {q : ℕ} [hq : NeZero q] {a : ZMod q} (ha : IsUnit a) (g : ℝ → ℝ) {x : ℝ} (hx : 1 ≤ x)
    (hg : ∀ t ∈ Set.Icc 1 x, DifferentiableAt ℝ g t)
    (hg_int : MeasureTheory.LocallyIntegrableOn (deriv g) (Set.Icc 1 x))
    (hg_mono : MonotoneOn g (Set.Icc 1 x))
    (hg1 : g 1 = 0)
    :
    ‖Δ_[fun n ↦ g n](x; q, a)‖ ≤ 2 * g x := by
  apply Delta_monotone_bound_aux (g' := deriv g) ha g hx ?deriv hg_int hg_mono hg1
  case deriv => apply fun t ht ↦ (hg t ht).hasDerivAt

open MeasureTheory in
@[blueprint (statement := /--
Let $v \ge 0$ and let $f$ be an arithmetic function supported on $[1, x]$. For $x \ge 2$, $q \in \N$ and $a \in (\Z/q\Z)^*$,
$$|\Delta_{f * \log^v}(x;\, q,\, a)| \le 2(\log x)^v \sum_{k \le x} |f(k)|$$
-/) (proof := /--
Straightforward application of the previous lemmas.
-/) (uses := [Delta_one_bound, Delta_abel_summation, Delta_monotone_bound])]
theorem Delta_flog_bound {v : ℕ} {f : ArithmeticFunction ℝ} {x : ℝ} (hx : 2 ≤ x) {q : ℕ} [NeZero q] (a : ZMod q) (ha : IsUnit a) :
    ‖Δ_[f * ppow log v](x; q, a)‖ ≤ 2 * (Real.log x)^v * summatory (fun k ↦ |f k|) x := by
  have hlog_nonneg : 0 ≤ Real.log x := by
    apply Real.log_nonneg (by grind)
  rw [Delta_convolution_eq (𝕜 := ℝ) ha, ← mul_summatory]
  grw [norm_summatory_le]
  gcongr with n hn_pos hnx
  split_ifs with h
  · by_cases hv : v = 0
    · subst hv
      simp only [ppow_zero, Delta_zeta_eq_Delta_one, norm_mul, pow_zero, mul_one]
      grw [Delta_one_bound]
      · simp
        have : 0 ≤ |f n| := abs_nonneg _
        linarith only [this]
      · exact NeZero.pos _
    replace hv : 0 < v := by grind
    have : ⇑(log.ppow v) = (fun n : ℕ ↦ (Real.log n)^v) := by
      ext n
      simp [hv]
    grw [norm_mul, this, Delta_monotone_bound (g := fun x ↦ (Real.log x)^v)]
    · simp only [Real.norm_eq_abs]
      ring_nf
      gcongr
      · apply Real.log_nonneg
        field_simp
        exact hnx
      · conv_rhs => rw [← mul_one x]
        gcongr
        field_simp
        norm_cast
    · simp [ha]
      have : (n : ZMod q) = (n : ℤ) := by simp
      rw [this]
      apply ZMod.isUnit_inv
      simp only [Int.cast_natCast, ZMod.isUnit_iff_coprime]
      exact h
    · field_simp
      exact hnx
    · simp only [Set.mem_Icc, and_imp]
      intro t h1t htx
      apply DifferentiableAt.pow
      apply Real.differentiableAt_log
      grind
    · have : deriv (fun x ↦ (Real.log x) ^ v)
        =ᵐ[(MeasureTheory.volume).restrict ({0}ᶜ)] fun x ↦ v * (Real.log x)^(v-1) * x⁻¹ := by
        simp
        apply Set.EqOn.aeEq (s := {0}ᶜ)
        · intro x;
          simp +contextual
        · simp
      apply LocallyIntegrableOn.congr this.symm _ |>.mono_set
      · simp
      apply ContinuousOn.locallyIntegrableOn
      · apply ContinuousOn.mul
        · apply ContinuousOn.mul
          · fun_prop
          · apply ContinuousOn.pow
            apply Real.continuousOn_log.mono
            simp
        · apply continuousOn_inv₀.mono
          simp
      simp
    · apply MonotoneOn.comp (t := Set.Ici 0) (g := (· ^ v))
      · apply zpow_left_monoOn₀  (n := v)
        grind
      · intro x hx y hy hxy
        simp only [Set.mem_Icc] at hx hy ⊢
        gcongr
        grind
      · intro a
        simp only [Set.mem_Icc, Set.mem_Ici, and_imp]
        intro h1a _
        apply Real.log_nonneg h1a
    · simp
      grind
  · simp only [norm_zero]
    positivity
