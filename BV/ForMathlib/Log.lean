
import Mathlib

import BV.ForMathlib.IsLocallyBounded

open Real MeasureTheory

@[fun_prop]
theorem Real.log_locallyBoundedOn :
    IsLocallyBoundedOn Real.log (Set.Ioi 0) := by
  constructor
  simp
  intro x hx
  simp [Filter.BoundedAtFilter]
  by_cases hx' : 1 ≤ x
  ·
    sorry
  · sorry

theorem Real.log_locallyIntegrableOn :
    LocallyIntegrableOn Real.log ({0}ᶜ) := by
  apply ContinuousOn.locallyIntegrableOn Real.continuousOn_log
  simp

/-- Comparing a logarithmic denominator at `z` with one at `x` when
`√x ≤ z ≤ x`. The hypotheses are independent of the project-specific `ProofData`. -/
theorem pnt_ratio_bound (x z : ℝ) (B : ℕ) (hz : 1 < z) (hzx : z ≤ x)
    (hsqrt : √x ≤ z) :
    z / (Real.log z) ^ B ≤ 2 ^ B * x / (Real.log x) ^ B := by
  have hx0 : 0 ≤ x := le_trans (by linarith : 0 ≤ z) hzx
  have hxpos : 0 < x := lt_of_lt_of_le (by linarith : 0 < z) hzx
  have hsx : 0 < √x := Real.sqrt_pos.2 hxpos
  have hlogz : 0 < Real.log z := Real.log_pos hz
  have hlogx : 0 < Real.log x := Real.log_pos (lt_of_lt_of_le hz hzx)
  have hlogsqrt : Real.log x / 2 ≤ Real.log z := by
    rw [← Real.log_sqrt hx0]
    exact Real.log_le_log hsx hsqrt
  have hlog : Real.log x ≤ 2 * Real.log z := by linarith
  have hp : (Real.log x) ^ B ≤ 2 ^ B * (Real.log z) ^ B := by
    calc
      (Real.log x) ^ B ≤ (2 * Real.log z) ^ B := by gcongr
      _ = 2 ^ B * (Real.log z) ^ B := mul_pow _ _ _
  have hL : 0 < (Real.log x) ^ B := pow_pos hlogx _
  have hZ : 0 < (Real.log z) ^ B := pow_pos hlogz _
  rw [div_le_div_iff₀ hZ hL]
  nlinarith
