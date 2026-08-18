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
  grind

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

/-- Bound `maxy` of an `ENNReal.ofReal`-valued function by a pointwise real bound.
No nonnegativity or boundedness side conditions are needed. -/
theorem maxy_ofReal_le [ProofData] {f : ℝ → ℝ} {B : ℝ}
    (hf : ∀ y, √x ≤ y → y ≤ x → f y ≤ B) :
    maxy (fun y ↦ ENNReal.ofReal (f y)) ≤ ENNReal.ofReal B :=
  maxy_le fun y hy1 hy2 ↦ ENNReal.ofReal_le_ofReal (hf y hy1 hy2)

/-- Bound an `ℝ≥0∞`-valued sum termwise by `ENNReal.ofReal` of a real sum. -/
theorem sum_le_ofReal_sum {ι : Type*} {s : Finset ι} {f : ι → ℝ≥0∞} {g : ι → ℝ}
    (hg : ∀ i ∈ s, 0 ≤ g i) (h : ∀ i ∈ s, f i ≤ ENNReal.ofReal (g i)) :
    ∑ i ∈ s, f i ≤ ENNReal.ofReal (∑ i ∈ s, g i) := by
  rw [ENNReal.ofReal_sum_of_nonneg hg]
  exact Finset.sum_le_sum h

/-- Bound `ENNReal.ofReal` of a real sum termwise by an `ℝ≥0∞`-valued sum. -/
theorem ofReal_sum_le_sum {ι : Type*} {s : Finset ι} {f : ι → ℝ≥0∞} {g : ι → ℝ}
    (hg : ∀ i ∈ s, 0 ≤ g i) (h : ∀ i ∈ s, ENNReal.ofReal (g i) ≤ f i) :
    ENNReal.ofReal (∑ i ∈ s, g i) ≤ ∑ i ∈ s, f i := by
  rw [ENNReal.ofReal_sum_of_nonneg hg]
  exact Finset.sum_le_sum h

/-! ### `ℝ≥0∞`-cast bridging lemmas

These push `ENNReal.ofReal` through the coefficient patterns `(n : ℝ≥0∞)⁻¹ * _` and
`(q : ℝ≥0∞) * (m : ℝ≥0∞)⁻¹ * _` that appear alongside `maxy` in weighted character sums. -/

theorem natCast_inv_eq_ofReal {n : ℕ} (hn : n ≠ 0) :
    (n : ℝ≥0∞)⁻¹ = ENNReal.ofReal ((n : ℝ)⁻¹) := by
  rw [ENNReal.ofReal_inv_of_pos (by positivity), ENNReal.ofReal_natCast]

theorem natCast_inv_mul_ofReal {n : ℕ} (hn : n ≠ 0) (t : ℝ) :
    (n : ℝ≥0∞)⁻¹ * ENNReal.ofReal t = ENNReal.ofReal ((n : ℝ)⁻¹ * t) := by
  rw [ENNReal.ofReal_mul (by positivity), natCast_inv_eq_ofReal hn]

theorem natCast_mul_natCast_inv_mul_ofReal (q : ℕ) {m : ℕ} (hm : m ≠ 0) (t : ℝ) :
    (q : ℝ≥0∞) * (m : ℝ≥0∞)⁻¹ * ENNReal.ofReal t
      = ENNReal.ofReal ((q : ℝ) * (m : ℝ)⁻¹ * t) := by
  rw [mul_assoc, natCast_inv_mul_ofReal hm, ← ENNReal.ofReal_natCast q,
    ← ENNReal.ofReal_mul (by positivity), mul_assoc]

theorem pow_two_inv_mul_ofReal (j : ℕ) (t : ℝ) :
    ((2 : ℝ≥0∞) ^ j)⁻¹ * ENNReal.ofReal t = ENNReal.ofReal (((2 : ℝ) ^ j)⁻¹ * t) := by
  rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_inv_of_pos (by positivity),
    ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_ofNat]

/-- `(m*n)⁻¹ = m⁻¹ * n⁻¹` for `ℕ`-casts in `ℝ≥0∞`; holds without any hypotheses. -/
theorem natCast_mul_inv (m n : ℕ) :
    ((m * n : ℕ) : ℝ≥0∞)⁻¹ = (m : ℝ≥0∞)⁻¹ * (n : ℝ≥0∞)⁻¹ := by
  push_cast
  rw [ENNReal.mul_inv (Or.inr (ENNReal.natCast_ne_top n)) (Or.inl (ENNReal.natCast_ne_top m))]

/-- Antitonicity of `(· : ℝ≥0∞)⁻¹` along `ℕ`-casts. -/
theorem natCast_inv_le_natCast_inv {m n : ℕ} (h : m ≤ n) :
    (n : ℝ≥0∞)⁻¹ ≤ (m : ℝ≥0∞)⁻¹ :=
  ENNReal.inv_le_inv' (by exact_mod_cast h)

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
