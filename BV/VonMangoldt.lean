import Mathlib

import BV.Summatory

open ArithmeticFunction
open scoped Moebius zeta

lemma vonMangoldt_eq_ite_vonMangoldt (n : ℕ) :
    Λ n = if IsPrimePow n then Λ n else 0 := by
  simp [vonMangoldt_apply]
  grind

lemma ArithmeticFunction.mul_coe_zeta_apply (f : ArithmeticFunction ℝ) (n : ℕ) :
    (f * ζ) n = ∑ d ∈ n.divisors, f d := by
  rw [ArithmeticFunction.mul_apply,
    Nat.sum_divisorsAntidiagonal (f := fun i j ↦ f i * (↑ζ : ArithmeticFunction ℝ) j)]
  congr! with d hd
  simp only [Nat.mem_divisors, ne_eq] at hd
  simp only [natCoe_apply, zeta_apply, Nat.div_eq_zero_iff, Nat.cast_ite, CharP.cast_eq_zero,
    Nat.cast_one, mul_ite, mul_zero, mul_one, ite_eq_right_iff]
  have hdn : d ≤ n := Nat.le_of_dvd (by grind) hd.1
  rintro (hd' | hnd)
  · simp only [zero_dvd_iff, and_not_self, hd'] at hd
  · grind

/-- A syntactically flexible prime-power decomposition, generalized over an
arbitrary additive commutative monoid. -/
theorem sum_PrimePow_eq_sum_sum_of_eq_zero {R : Type*} [AddCommMonoid R]
    (f : ℕ → R) {x : ℝ} (hx : 0 ≤ x)
    (hf : ∀ n : ℕ, 0 < n → n ≤ x → ¬ IsPrimePow n → f n = 0) :
    ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, f n =
      ∑ k ∈ Finset.Icc 1 ⌊Real.log x / Real.log 2⌋₊,
        ∑ p ∈ Finset.Ioc 0 ⌊x ^ ((1 : ℝ) / k)⌋₊ with p.Prime, f (p ^ k) := by
  rw [← Chebyshev.sum_PrimePow_eq_sum_sum, Finset.sum_filter]
  congr! with n hn
  · simp only [Finset.mem_Ioc, Nat.le_floor_iff, hx] at hn
    simpa using hf n hn.1 hn.2
  · exact hx

lemma sum_vonMangoldt_prime_pow_not_coprime_le_log {z : ℝ} {k : ℕ} (hk : 0 < k)
    {q : ℕ} (hq : 0 < q) :
    ∑ p ∈ Finset.Ioc 0 ⌊z ^ ((1 : ℝ) / k)⌋₊ with Nat.Prime p,
        (if ¬q.Coprime (p ^ k) then Λ p else 0) ≤ Real.log q := by
  have hprime {p : ℕ} (hp : p.Prime) : ¬q.Coprime (p ^ k) ↔ p ∣ q := by
    rw [Nat.coprime_comm]
    simp only [Nat.coprime_pow_left_iff, hk, Nat.Prime.coprime_iff_not_dvd hp,
      Decidable.not_not]
  simp +contextual (disch := grind) only [hprime]
  simp_rw [← Finset.sum_filter]
  trans ∑ d ∈ q.divisors, Λ d
  · gcongr
    intro d
    simp only [Finset.mem_filter, Finset.mem_Ioc, Nat.mem_divisors, ne_eq, and_imp]
    grind
  · exact le_of_eq ArithmeticFunction.vonMangoldt_sum

/-- The non-coprime von Mangoldt sum is nonnegative. -/
theorem sum_vonMangoldt_not_coprime_nonneg (z : ℝ) (q : ℕ) :
    0 ≤ ∑ n ∈ Finset.Ioc 0 ⌊z⌋₊, if ¬q.Coprime n then Λ n else 0 := by
  exact Finset.sum_nonneg fun _ _ ↦ by split_ifs <;> simp

/-- Explicit endpoint estimate for the von Mangoldt mass on integers not
coprime to `q`, stated entirely using standard Mathlib finsets. -/
theorem sum_vonMangoldt_not_coprime_le {z : ℝ} (hz : 2 ≤ z) {q : ℕ} (hq : 0 < q) :
    ∑ n ∈ Finset.Ioc 0 ⌊z⌋₊, (if ¬q.Coprime n then Λ n else 0) ≤
      Real.log q * Real.log z / Real.log 2 := by
  rw [sum_PrimePow_eq_sum_sum_of_eq_zero]
  · simp +contextual (disch := grind) only [ArithmeticFunction.vonMangoldt_apply_pow]
    trans ∑ k ∈ Finset.Icc 1 ⌊Real.log z / Real.log 2⌋₊, Real.log q
    · gcongr with k hk
      exact sum_vonMangoldt_prime_pow_not_coprime_le_log (Finset.mem_Icc.mp hk).1 hq
    simp only [Finset.sum_const, Nat.card_Icc, add_tsub_cancel_right, nsmul_eq_mul]
    grw [Nat.floor_le (div_nonneg (Real.log_nonneg (by linarith))
      (Real.log_nonneg (by norm_num)))]
    ring_nf
    exact le_rfl
  · linarith
  · simp +contextual [vonMangoldt_eq_zero_iff]

lemma summatory_sub_ite {P : ℕ → Prop} [DecidablePred P] (f : ℕ → ℝ) {x : ℝ} :
    summatory f x - summatory (fun n ↦ if P n then f n else 0) x =
    summatory (fun n ↦ if ¬P n then f n else 0) x := by
  pull summatory
  congr with n
  split_ifs <;> ring
