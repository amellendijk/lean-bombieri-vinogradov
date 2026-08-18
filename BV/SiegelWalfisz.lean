import Mathlib
import Architect

import BV.Axioms
import BV.Defs
import BV.VonMangoldt

open ArithmeticFunction

noncomputable def C_D1 (A : ℕ) : ℝ := C_SW A 0

/-- The prime number theorem consequence of Siegel–Walfisz at an explicit endpoint. -/
lemma PNT (A : ℕ) {z : ℝ} (hz : 2 ≤ z) :
    |summatory (fun n ↦ Λ n) z - z| ≤ C_D1 A * (z / Real.log z ^ A) := by
  have h := siegel_walfisz A 0 hz (q := 1) (by positivity) (by simp)
    (a := (1 : ZMod 1)) (by simp)
  simp only [ψ_one_one] at h
  rw [← summatory_vonMangoldt] at h
  simpa [C_D1] using h

noncomputable def C_SVNC : ℝ := (Real.log 2)⁻¹

theorem C_SVNC_le : C_SVNC ≤ (Real.log 2)⁻¹ := le_rfl

/-- The unique project-facing non-coprime von Mangoldt estimate. -/
lemma sum_vonMangoldt_not_coprime_ll_logq {z : ℝ} (hz : 2 ≤ z)
    {q : ℕ} (hq : 0 < q) :
    |summatory (fun n ↦ if ¬q.Coprime n then Λ n else 0) z| ≤
      C_SVNC * (Real.log q * Real.log z) := by
  rw [abs_of_nonneg]
  · simpa [summatory_apply, C_SVNC, div_eq_mul_inv, mul_assoc, mul_left_comm,
      mul_comm] using sum_vonMangoldt_not_coprime_le hz hq
  · positivity

/-- Public generic coprime-error consequence of Siegel–Walfisz. -/
lemma coprime_vonMangoldt_error (B : ℕ) {z : ℝ} (hz : 2 ≤ z)
    {q : ℕ} (hq : 0 < q) :
    |summatory (fun n ↦ if q.Coprime n then Λ n else 0) z - z| ≤
      C_D1 B * (z / (Real.log z) ^ B) + C_SVNC * (Real.log q * Real.log z) := by
  have hsplit :
      summatory (fun n ↦ if q.Coprime n then Λ n else 0) z - z =
        (summatory (fun n ↦ Λ n) z - z) -
          summatory (fun n ↦ if ¬q.Coprime n then Λ n else 0) z := by
    rw [← summatory_sub_ite]
    ring
  rw [hsplit]
  exact (abs_sub _ _).trans (add_le_add (PNT B hz)
    (sum_vonMangoldt_not_coprime_ll_logq hz hq))

open ProofData in
lemma PNT_at_x [ProofData] (A : ℕ) :
    |summatory (fun n ↦ Λ n) x - x| ≤ C_D1 A * (x / Real.log x ^ A) :=
  PNT A le_x

open ProofData in
lemma coprime_vonMangoldt_error_at_x [ProofData] (B : ℕ) {q : ℕ} (hq : 0 < q) :
    |summatory (fun n ↦ if q.Coprime n then Λ n else 0) x - x| ≤
      C_D1 B * (x / (Real.log x) ^ B) + C_SVNC * (Real.log q * Real.log x) :=
  coprime_vonMangoldt_error B le_x hq
