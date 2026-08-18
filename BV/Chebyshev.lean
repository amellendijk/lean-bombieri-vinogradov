import Mathlib

import BV.Summatory

open ArithmeticFunction

/-- The set of natural numbers congruent to `a` modulo `q`. -/
def Nat.modEqs {q : ℕ} (a : ZMod q) : Set ℕ := {n : ℕ | n = a}

@[simp]
theorem Nat.modEqs_one_one : Nat.modEqs (1 : ZMod 1) = Set.univ := by
  have h : ∀ n : ZMod 1, n = 1 := fun n ↦ Subsingleton.elim n 1
  simp [Nat.modEqs, h]

@[simp]
theorem Nat.mem_modEqs {q : ℕ} (a : ZMod q) (n : ℕ) :
    n ∈ Nat.modEqs a ↔ n = a := Iff.rfl

namespace Chebyshev

/-- The modular Chebyshev function `ψ(x; q, a)`. -/
noncomputable def psiMod (x : ℝ) {q : ℕ} (a : ZMod q) : ℝ :=
  ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, if ((n : ℕ) : ZMod q) = a then Λ n else 0

theorem psiMod_eq_summatory (x : ℝ) {q : ℕ} (a : ZMod q) :
    psiMod x a = summatory ((Nat.modEqs a).indicator Λ) x := by
  classical
  simp [summatory_apply, psiMod, Set.indicator_apply, Nat.modEqs]

theorem summatory_vonMangoldt {x : ℝ} :
    summatory (fun n ↦ Λ n) x = Chebyshev.psi x := by
  simp [Chebyshev.psi_eq_sum_Icc]
  rw [summatory_apply, ← Finset.add_sum_Ioc_eq_sum_Icc]
  · simp
  · positivity

@[simp]
theorem psiMod_one_one {x : ℝ} : psiMod x (1 : ZMod 1) = Chebyshev.psi x := by
  simp [psiMod_eq_summatory, summatory_vonMangoldt]

theorem psiMod_nonneg {q : ℕ} (z : ℝ) (a : ZMod q) : 0 ≤ psiMod z a := by
  classical
  rw [psiMod_eq_summatory]
  exact summatory_nonneg _ _ fun n _ ↦ by
    rw [Set.indicator_apply]
    positivity

/-- Restricting the von Mangoldt sum to one residue class can only decrease it. -/
theorem psiMod_le_psi {q : ℕ} (z : ℝ) (a : ZMod q) :
    psiMod z a ≤ Chebyshev.psi z := by
  classical
  rw [psiMod_eq_summatory, ← summatory_vonMangoldt]
  refine summatory_le_summatory fun n _ _ ↦ ?_
  rw [Set.indicator_apply]
  split_ifs
  · exact le_rfl
  · exact ArithmeticFunction.vonMangoldt_nonneg

/-- A reusable elementary error bound for the modular Chebyshev function. -/
theorem abs_psiMod_sub_div_le {q : ℕ} (hq : 0 < q) {z : ℝ} (hz : 0 ≤ z)
    (a : ZMod q) :
    |psiMod z a - z / q.totient| ≤ Chebyshev.psi z + z := by
  have hψ0 := psiMod_nonneg z a
  have hψ := psiMod_le_psi z a
  have hφ : (1 : ℝ) ≤ q.totient := by exact_mod_cast Nat.totient_pos.mpr hq
  have hφ0 : (0 : ℝ) < q.totient := lt_of_lt_of_le zero_lt_one hφ
  have hzφ0 : 0 ≤ z / q.totient := div_nonneg hz hφ0.le
  have hzφ : z / q.totient ≤ z := by
    rw [div_le_iff₀ hφ0]
    nlinarith
  grind

/-- Explicit compact-range consequence of `abs_psiMod_sub_div_le`. -/
theorem abs_psiMod_sub_div_le_const {q : ℕ} (hq : 0 < q) {z : ℝ} (hz : 1 ≤ z)
    (a : ZMod q) :
    |psiMod z a - z / q.totient| ≤ (Real.log 4 + 5) * z := by
  refine (abs_psiMod_sub_div_le hq (zero_le_one.trans hz) a).trans ?_
  have hψ := psiMod_le_psi z a
  have hCheb := Chebyshev.psi_le_const_mul_self (show 0 ≤ z by positivity)
  grind

end Chebyshev

/-- Compatibility alias for the original project name. -/
noncomputable abbrev chebyPsi := Chebyshev.psiMod

lemma chebyPsi_eq_summatory (x : ℝ) {q : ℕ} (a : ZMod q) :
    chebyPsi x a = summatory ((Nat.modEqs a).indicator Λ) x :=
  Chebyshev.psiMod_eq_summatory x a

scoped[BV] notation "ψ" => Chebyshev.psiMod

lemma summatory_vonMangoldt {x : ℝ} :
    summatory (fun n ↦ Λ n) x = Chebyshev.psi x :=
  Chebyshev.summatory_vonMangoldt

theorem ψ_one_one {x : ℝ} : Chebyshev.psiMod x (1 : ZMod 1) = Chebyshev.psi x :=
  Chebyshev.psiMod_one_one

lemma abs_psi_sub_div_le {q : ℕ} (hq : 0 < q) {z : ℝ} (hz : 1 ≤ z)
    (a : ZMod q) :
    |Chebyshev.psiMod z a - z / q.totient| ≤ (Real.log 4 + 5) * z :=
  Chebyshev.abs_psiMod_sub_div_le_const hq hz a
