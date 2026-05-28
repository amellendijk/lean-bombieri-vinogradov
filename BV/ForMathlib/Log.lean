
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
