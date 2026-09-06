import Mathlib


public section


open Set Filter MeasureTheory MeasureTheory.Measure TopologicalSpace ENNReal

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] {μ : Measure α}

theorem MeasurableEmbedding.map_restrict {f : α → β} (hf : MeasurableEmbedding f)
    (μ : Measure α) (s : Set α) :
    (μ.restrict s).map f = (μ.map f).restrict (f '' s) := by
  rw [hf.restrict_map, hf.injective.preimage_image]

theorem MeasurableEmbedding.setLIntegral_map {f : β → ℝ≥0∞} {g : α → β} {s : Set β} (hg : MeasurableEmbedding g) :
    ∫⁻ y in s, f y ∂map g μ = ∫⁻ x in g ⁻¹' s, f (g x) ∂μ := by
  rw [hg.restrict_map, hg.lintegral_map]

-- attribute [congr] setLIntegral_congr

@[simp]
theorem lintegral_comp_neg_Iic
    (c : ℝ) (f : ℝ → ℝ≥0∞) : (∫⁻ x in Iic c, f (-x)) = ∫⁻ x in Ioi (-c), f x := by
  have A : MeasurableEmbedding fun x : ℝ => -x :=
    (Homeomorph.neg ℝ).isClosedEmbedding.measurableEmbedding
  rw [← A.lintegral_map f, A.map_restrict, map_neg_eq_self, image_neg_eq_neg, neg_Iic]
  apply setLIntegral_congr (Ioi_ae_eq_Ici.symm)

@[simp]
theorem lintegral_comp_neg_Ioi
    (c : ℝ) (f : ℝ → ℝ≥0∞) : (∫⁻ x in Ioi c, f (-x)) = ∫⁻ x in Iic (-c), f x := by
  rw [← neg_neg c, ← lintegral_comp_neg_Iic]
  simp only [neg_neg]


end
