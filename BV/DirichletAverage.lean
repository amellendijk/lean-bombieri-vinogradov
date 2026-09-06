import Mathlib

import BV.Defs

open MeasureTheory ENNReal

namespace DirichletAverage

scoped instance : MeasurableSpace ((Σ q : ℕ, DirichletCharacter ℂ q)) := ⊤

local instance : DiscreteMeasurableSpace (Σ q : ℕ, DirichletCharacter ℂ q) where
  forall_measurableSet := by simp

end DirichletAverage

open DirichletAverage

open Classical in
noncomputable def charsUpTo (Q : ℝ) : Finset ((q : ℕ) × DirichletCharacter ℂ q) :=
    (Finset.Ioc 0 ⌊Q⌋₊).biUnion fun q ↦ ((Finset.univ : Finset (DirichletCharacter ℂ q)).filter DirichletCharacter.IsPrimitive |>.image fun χ ↦ ⟨q, χ⟩)

lemma mem_charsUpTo {p : (q : ℕ) × DirichletCharacter ℂ q} {Q : ℝ} (hQ0 : 0 ≤ Q) : p ∈ charsUpTo Q ↔ p.2.IsPrimitive ∧ 0 < p.1 ∧ p.1 ≤ Q := by
  simp [charsUpTo]
  constructor
  · rintro ⟨q, ⟨hq1, hqQ⟩, ⟨χ, hχ, rfl⟩⟩
    simp
    rw [Nat.le_floor_iff hQ0] at hqQ
    grind
  · intro ⟨hχ, h0, hQ⟩
    use p.1
    constructor
    · simpa [hχ, Nat.one_le_iff_ne_zero, Nat.le_floor_iff hQ0, hQ] using h0
    · use p.snd

-- TODO: this should be decidable, no?
open Classical in
theorem Finset.sum_charsUpTo {Q : ℝ} (f : (q : ℕ) → (DirichletCharacter ℂ q) → ENNReal) : ∑ p ∈ charsUpTo Q, f p.1 p.2 = summatory (fun q ↦ ∑ χ with χ.IsPrimitive, f q χ) Q := by
  rw [summatory_apply, charsUpTo, Finset.sum_biUnion]
  · simp
  · intro x hx y hy hxy
    simp only [Finset.coe_Ioc, Set.mem_Ioc] at hx hy
    apply Finset.disjoint_iff_ne.mpr
    simp [hxy]

noncomputable def dirichletMeas (Q : ℝ) : Measure ((q : ℕ) × DirichletCharacter ℂ q) :=
  MeasureTheory.Measure.count.withDensity (Set.indicator (charsUpTo Q) (fun ⟨q, _⟩ ↦ q * (q.totient : ENNReal)⁻¹))

open Classical in
lemma lintegral_dirichletMeas {Q : ℝ} (f : {q : ℕ} → (χ : DirichletCharacter ℂ q) → ℝ≥0∞) :
    ∫⁻ p, f p.2 ∂dirichletMeas Q = summatory (fun q ↦ q * (q.totient : ENNReal)⁻¹ * ∑ χ : DirichletCharacter ℂ q with χ.IsPrimitive, f χ) Q := by
  rw [dirichletMeas]

  rw [lintegral_withDensity_eq_lintegral_mul _ (by measurability) (by measurability)]
  simp only [Pi.mul_apply]
  have := @Set.indicator_mul_left (g := fun a : (q : ℕ) × (DirichletCharacter ℂ q) ↦ f a.2) (s := charsUpTo Q)
  simp_rw [← this, lintegral_count]
  rw [← sum_eq_tsum_indicator, Finset.sum_charsUpTo fun q χ ↦ q * (q.totient : ENNReal)⁻¹ * f χ]
  simp_rw [Finset.mul_sum]
