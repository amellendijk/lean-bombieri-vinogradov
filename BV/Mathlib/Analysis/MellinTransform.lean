/-
Copyright (c) 2023 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/
module

public import Mathlib.Analysis.MellinTransform

/-! # The Mellin transform

We define the Mellin transform of a locally integrable function on `Ioi 0`, and show it is
differentiable in a suitable vertical strip.

## Main statements

- `mellin` : the Mellin transform `∫ (t : ℝ) in Ioi 0, t ^ (s - 1) • f t`,
  where `s` is a complex number.
- `HasMellin`: shorthand asserting that the Mellin transform exists and has a given value
  (analogous to `HasSum`).
- `mellin_differentiableAt_of_isBigO_rpow` : if `f` is `O(x ^ (-a))` at infinity, and
  `O(x ^ (-b))` at 0, then `mellin f` is holomorphic on the domain `b < re s < a`.

-/

@[expose] public section

open MeasureTheory Set Filter Asymptotics TopologicalSpace

open Real

open Complex hiding exp log

open scoped Topology

noncomputable section

section Defs

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/- TODO: The contents of this file are vibe-coded. Review before upstreaming to mathlib. -/


/-- The Mellin transform of *any* function is strongly measurable, with no hypotheses on `f`:
either `f` is a.e. strongly measurable on `Ioi 0` and the parametric-integral machinery applies,
or the integrand is non-measurable for every `s` (the kernel `x ^ (s - 1)` never vanishes on
`Ioi 0`), so `mellin f ≡ 0`. -/
@[fun_prop]
theorem stronglyMeasurable_mellin {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (f : ℝ → E) : StronglyMeasurable (mellin f) := by
  by_cases hf : AEStronglyMeasurable f (volume.restrict (Ioi 0))
  · obtain ⟨g, hg, hfg⟩ := hf
    have heq : mellin f = fun s => ∫ x in Ioi (0:ℝ), Complex.exp ((s - 1) * Real.log x) • g x := by
      funext s
      show ∫ x in Ioi (0:ℝ), (x:ℂ) ^ (s - 1) • f x = _
      refine integral_congr_ae ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioi, hfg] with x hx hfgx
      rw [hfgx, Complex.cpow_def_of_ne_zero (ofReal_ne_zero.mpr hx.ne'),
        ← Complex.ofReal_log hx.le, mul_comm]
    rw [heq]
    have hF : StronglyMeasurable fun p : ℂ × ℝ =>
        Complex.exp ((p.1 - 1) * Real.log p.2) • g p.2 := by fun_prop
    exact hF.integral_prod_right'
  · have h0 : mellin f = fun _ => 0 := by
      funext s
      refine integral_undef fun hInt => hf ?_
      have hker : Measurable fun x : ℝ => (Complex.exp ((s - 1) * Real.log x))⁻¹ := by fun_prop
      have h1 : AEStronglyMeasurable
          (fun x : ℝ => (Complex.exp ((s - 1) * Real.log x))⁻¹ • ((x:ℂ) ^ (s - 1) • f x))
          (volume.restrict (Ioi 0)) :=
        hker.aestronglyMeasurable.smul hInt.aestronglyMeasurable
      refine h1.congr ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      rw [Complex.cpow_def_of_ne_zero (ofReal_ne_zero.mpr hx.ne'),
        ← Complex.ofReal_log hx.le, mul_comm, inv_smul_smul₀ (Complex.exp_ne_zero _)]
    rw [h0]
    exact stronglyMeasurable_const

-- @[fun_prop]
-- theorem measurable_mellin {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
--     [MeasurableSpace E] [BorelSpace E] (f : ℝ → E) : Measurable (mellin f) :=
--   (stronglyMeasurable_mellin f).measurable

-- /-- Composition form so that `fun_prop` can close `StronglyMeasurable` goals about
-- `fun a => 𝓜 f (g a)` (e.g. along a vertical line `g = fun t => σ + t * I`). -/
-- @[fun_prop]
-- theorem stronglyMeasurable_mellin_comp {α : Type*} [MeasurableSpace α]
--     {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (f : ℝ → E)
--     {g : α → ℂ} (hg : Measurable g) :
--     StronglyMeasurable (fun a => mellin f (g a)) :=
--   (stronglyMeasurable_mellin f).comp_measurable hg

-- /-- Composition form so that `fun_prop` can close `AEStronglyMeasurable` goals about
-- `fun a => 𝓜 f (g a)` (it does not route them through `Measurable` on its own). -/
-- @[fun_prop]
-- theorem aestronglyMeasurable_mellin_comp {α : Type*} [MeasurableSpace α] {μ : Measure α}
--     {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (f : ℝ → E)
--     {g : α → ℂ} (hg : Measurable g) :
--     AEStronglyMeasurable (fun a => mellin f (g a)) μ :=
--   (stronglyMeasurable_mellin_comp f hg).aestronglyMeasurable

end Defs
