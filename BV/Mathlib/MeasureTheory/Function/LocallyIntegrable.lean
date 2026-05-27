import Mathlib.MeasureTheory.Function.LocallyIntegrable


open MeasureTheory MeasureTheory.Measure Set Function TopologicalSpace Bornology Filter

open scoped Topology Interval ENNReal

variable {X Y ε ε' ε'' E F R : Type*} [MeasurableSpace X] [TopologicalSpace X]
variable [MeasurableSpace Y] [TopologicalSpace Y]
variable [TopologicalSpace ε] [ContinuousENorm ε] [TopologicalSpace ε'] [ContinuousENorm ε']
  [TopologicalSpace ε''] [ESeminormedAddMonoid ε'']
  [NormedAddCommGroup E] [NormedAddCommGroup F] {f g : X → ε} {μ ν : Measure X} {s : Set X}

namespace MeasureTheory
section LocallyIntegrableOn

/-- This lemma is in a more recent version of mathlib -/
@[gcongr]
axiom LocallyIntegrableOn.congr (h : f =ᵐ[μ.restrict s] g) (hf : LocallyIntegrableOn f s μ) :
    LocallyIntegrableOn g s μ



end LocallyIntegrableOn

section RCLike

variable {𝕜 : Type*} [RCLike 𝕜] {f : X → 𝕜}

attribute [fun_prop] LocallyIntegrable LocallyIntegrableOn


-- Doesn't match with Complex.ofReal, sadly

@[fun_prop]
theorem LocallyIntegrable.ofReal {f : X → ℝ} (hf : LocallyIntegrable f μ) :
    LocallyIntegrable (fun x => (f x : 𝕜)) μ := fun x =>
  let ⟨U, hU_nhd, hU_int⟩ := hf x
  ⟨U, hU_nhd, hU_int.ofReal⟩

@[fun_prop]
theorem LocallyIntegrableOn.ofReal {f : X → ℝ} (hf : LocallyIntegrableOn f s μ) :
    LocallyIntegrableOn (fun x => (f x : 𝕜)) s μ := fun x hx =>
  let ⟨U, hU_nhd, hU_int⟩ := hf x hx
  ⟨U, hU_nhd, hU_int.ofReal⟩

-- theorem LocallyIntegrable.re_im_iff :
--     LocallyIntegrable (fun x => RCLike.re (f x)) μ ∧
--         LocallyIntegrable (fun x => RCLike.im (f x)) μ ↔
--       LocallyIntegrable f μ := by
--   refine ⟨fun ⟨hre, him⟩ x => ?_, fun hf => ⟨hf.re, hf.im⟩⟩
--   obtain ⟨U₁, hU₁_nhd, hU₁_int⟩ := hre x
--   obtain ⟨U₂, hU₂_nhd, hU₂_int⟩ := him x
--   exact ⟨U₁ ∩ U₂, Filter.inter_mem hU₁_nhd hU₂_nhd,
--     Integrable.re_im_iff.mp ⟨hU₁_int.mono_set Set.inter_subset_left,
--       hU₂_int.mono_set Set.inter_subset_right⟩⟩

-- @[fun_prop]
-- theorem LocallyIntegrable.re (hf : LocallyIntegrable f μ) :
--     LocallyIntegrable (fun x => RCLike.re (f x)) μ := fun x =>
--   let ⟨U, hU_nhd, hU_int⟩ := hf x
--   ⟨U, hU_nhd, hU_int.re⟩

-- @[fun_prop]
-- theorem LocallyIntegrable.im (hf : LocallyIntegrable f μ) :
--     LocallyIntegrable (fun x => RCLike.im (f x)) μ := fun x =>
--   let ⟨U, hU_nhd, hU_int⟩ := hf x
--   ⟨U, hU_nhd, hU_int.im⟩

end RCLike

end MeasureTheory
