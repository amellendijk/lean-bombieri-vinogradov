/-
Copyright (c) 2019 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Slope

/-!
# Derivative as the limit of the slope

In this file we relate the derivative of a function with its definition from a standard
undergraduate course as the limit of the slope `(f y - f x) / (y - x)` as `y` tends to `𝓝[≠] x`.
Since we are talking about functions taking values in a normed space instead of the base field, we
use `slope f x y = (y - x)⁻¹ • (f y - f x)` instead of division.

We also prove some estimates on the upper/lower limits of the slope in terms of the derivative.

For a more detailed overview of one-dimensional derivatives in mathlib, see the module docstring of
`Mathlib/Analysis/Calculus/Deriv/Basic.lean`.

## Keywords

derivative, slope
-/

public section

universe u v

open scoped Topology

open Filter TopologicalSpace Set

section NormedField

variable {𝕜 : Type u} [NontriviallyNormedField 𝕜]
variable {F : Type v} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable {f : 𝕜 → F}
variable {f' : F}
variable {x : 𝕜}
variable {s : Set 𝕜}

theorem HasDerivAt.nonneg_of_monotoneOn
    {𝕜 : Type u} [NontriviallyNormedField 𝕜] {x : 𝕜} [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [OrderTopology 𝕜]
    {g : 𝕜 → 𝕜} {g' : 𝕜} (hd : HasDerivAt g g' x) {s : Set 𝕜} (hg : MonotoneOn g s) (hs : AccPt x (𝓟 s)) :
    0 ≤ g' := by
  rw [← hasDerivWithinAt_univ] at hd
  apply (hd.mono (subset_univ _)).nonneg_of_monotoneOn hs hg

theorem HasDerivAt.nonneg_of_monotoneOn_of_mem_nhds
    {𝕜 : Type u} [NontriviallyNormedField 𝕜] {x : 𝕜} [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [OrderTopology 𝕜]
    {g : 𝕜 → 𝕜} {g' : 𝕜} (hd : HasDerivAt g g' x) {s : Set 𝕜} (hg : MonotoneOn g s) (hs : s ∈ nhds x) :
    0 ≤ g' := by
  apply hd.nonneg_of_monotoneOn hg
  have := AccPt.nhds_inter (C := Set.univ) ?_ hs
  · simpa using this
  · apply PerfectSpace.univ_preperfect _ (Set.mem_univ _)
