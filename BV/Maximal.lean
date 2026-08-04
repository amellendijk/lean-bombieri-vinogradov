import Mathlib

import BV.Defs

open ProofData
open scoped ENNReal

namespace BV

/-- The supremum of an `ℝ≥0∞`-valued function on `[√x, x]`. -/
noncomputable def maxy [ProofData] (f : ℝ → ℝ≥0∞) : ℝ≥0∞ :=
  ⨆ y : Set.Icc (√x) x, f y

/-- The supremum over `y ∈ [√x,x]` and unit residue classes modulo `q`. -/
noncomputable def maxya [ProofData] (q : ℕ) (f : ℝ → ZMod q → ℝ≥0∞) : ℝ≥0∞ :=
  ⨆ a : (ZMod q)ˣ, maxy (fun y ↦ f y a)

theorem le_maxy [ProofData] {f : ℝ → ℝ≥0∞} {y : ℝ}
    (hy1 : √x ≤ y) (hy2 : y ≤ x) : f y ≤ maxy f := by
  exact le_iSup (fun z : Set.Icc (√x) x ↦ f z) ⟨y, hy1, hy2⟩

theorem maxy_le [ProofData] {f : ℝ → ℝ≥0∞} {M : ℝ≥0∞}
    (hf : ∀ y, √x ≤ y → y ≤ x → f y ≤ M) : maxy f ≤ M := by
  refine iSup_le fun y ↦ ?_
  exact hf y y.2.1 y.2.2

theorem le_maxya [ProofData] {q : ℕ} {f : ℝ → ZMod q → ℝ≥0∞}
    {y : ℝ} {a : ZMod q} (ha : IsUnit a) (hy1 : √x ≤ y) (hy2 : y ≤ x) :
    f y a ≤ maxya q f := by
  obtain ⟨a, rfl⟩ := ha
  exact (le_maxy hy1 hy2).trans (le_iSup (fun u : (ZMod q)ˣ ↦ maxy (fun z ↦ f z u)) a)

theorem maxya_le [ProofData] {q : ℕ} {f : ℝ → ZMod q → ℝ≥0∞} {M : ℝ≥0∞}
    (hf : ∀ y, √x ≤ y → y ≤ x → ∀ a, f y a ≤ M) : maxya q f ≤ M := by
  refine iSup_le fun a ↦ maxy_le ?_
  intro y hy1 hy2
  exact hf y hy1 hy2 a

/-- Units-only version of `maxya_le`. -/
theorem maxya_le_unit [ProofData] {q : ℕ} {f : ℝ → ZMod q → ℝ≥0∞} {M : ℝ≥0∞}
    (hf : ∀ y, √x ≤ y → y ≤ x → ∀ a : ZMod q, IsUnit a → f y a ≤ M) :
    maxya q f ≤ M := by
  refine iSup_le fun a ↦ maxy_le ?_
  intro y hy1 hy2
  exact hf y hy1 hy2 a a.isUnit

theorem maxy_ne_top_of_le_ofReal [ProofData] {f : ℝ → ℝ≥0∞} {B : ℝ}
    (h : maxy f ≤ ENNReal.ofReal B) : maxy f ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.ofReal_ne_top h

theorem maxya_ne_top_of_le_ofReal [ProofData] {q : ℕ} {f : ℝ → ZMod q → ℝ≥0∞} {B : ℝ}
    (h : maxya q f ≤ ENNReal.ofReal B) : maxya q f ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.ofReal_ne_top h

/-- Real-valued view of `maxy`. This is meaningful once finiteness has been proved. -/
noncomputable def maxyReal [ProofData] (f : ℝ → ℝ≥0∞) : ℝ := (maxy f).toReal

theorem maxyReal_le_of_le_ofReal [ProofData] {f : ℝ → ℝ≥0∞} {B : ℝ} (hB : 0 ≤ B)
    (h : maxy f ≤ ENNReal.ofReal B) : maxyReal f ≤ B := by
  rw [maxyReal]
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top h).trans_eq (ENNReal.toReal_ofReal hB)

theorem le_maxyReal_of_ne_top [ProofData] {f : ℝ → ℝ≥0∞} {y : ℝ}
    (hy1 : √x ≤ y) (hy2 : y ≤ x) (hfin : maxy f ≠ ⊤) :
    (f y).toReal ≤ maxyReal f := ENNReal.toReal_mono hfin (le_maxy hy1 hy2)

theorem maxyReal_ofReal_le [ProofData] {f : ℝ → ℝ} {B : ℝ} (hB : 0 ≤ B)
    (hf : ∀ y, √x ≤ y → y ≤ x → f y ≤ B) :
    maxyReal (fun y ↦ ENNReal.ofReal (f y)) ≤ B := by
  apply maxyReal_le_of_le_ofReal hB
  exact maxy_le fun y hy1 hy2 ↦ ENNReal.ofReal_le_ofReal (hf y hy1 hy2)

theorem le_maxyReal_ofReal [ProofData] {f : ℝ → ℝ} {y : ℝ}
    (hy1 : √x ≤ y) (hy2 : y ≤ x) {B : ℝ}
    (hf0 : 0 ≤ f y) (hf : ∀ z, √x ≤ z → z ≤ x → f z ≤ B) :
    f y ≤ maxyReal (fun z ↦ ENNReal.ofReal (f z)) := by
  have hmax : maxy (fun z ↦ ENNReal.ofReal (f z)) ≤ ENNReal.ofReal B :=
    maxy_le fun z hz1 hz2 ↦ ENNReal.ofReal_le_ofReal (hf z hz1 hz2)
  have hfin := maxy_ne_top_of_le_ofReal hmax
  simpa [ENNReal.toReal_ofReal hf0] using
    (le_maxyReal_of_ne_top (f := fun z ↦ ENNReal.ofReal (f z)) hy1 hy2 hfin)

theorem toReal_iSup_of_finite {ι : Sort*} {f : ι → ℝ≥0∞} (hf : ∀ i, f i ≠ ⊤) :
    (⨆ i, f i).toReal = ⨆ i, (f i).toReal := ENNReal.toReal_iSup hf

theorem toReal_finset_sum {ι : Type*} (s : Finset ι) (f : ι → ℝ≥0∞)
    (hf : ∀ i ∈ s, f i ≠ ⊤) :
    (∑ i ∈ s, f i).toReal = ∑ i ∈ s, (f i).toReal := ENNReal.toReal_sum hf

@[simp] theorem toReal_ofReal_of_nonneg {r : ℝ} (hr : 0 ≤ r) :
    (ENNReal.ofReal r).toReal = r := ENNReal.toReal_ofReal hr

@[simp] theorem toReal_enorm {E : Type*} [SeminormedAddGroup E] (v : E) :
    ‖v‖ₑ.toReal = ‖v‖ := by
  rw [← ofReal_norm, ENNReal.toReal_ofReal (norm_nonneg v)]

@[simp] theorem toReal_enorm_real (r : ℝ) : ‖r‖ₑ.toReal = |r| := by
  simpa [Real.norm_eq_abs] using toReal_enorm r

theorem ofReal_abs_eq_enorm (r : ℝ) : ENNReal.ofReal |r| = ‖r‖ₑ := by
  simpa [Real.norm_eq_abs] using ofReal_norm r

end BV
