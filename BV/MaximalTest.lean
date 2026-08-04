import BV.Maximal

open ProofData
open scoped ENNReal

namespace BV

private lemma sqrt_x_le_x [ProofData] : √x ≤ x := by
  rw [Real.sqrt_le_iff]
  exact ⟨x_nonneg, le_self_pow₀ (by linarith [le_x]) (by norm_num)⟩

example [ProofData] : maxy (fun _ ↦ 0) = 0 := by
  simp [maxy]

example [ProofData] (c : ℝ≥0∞) : maxy (fun _ ↦ c) = c := by
  apply le_antisymm
  · exact maxy_le fun _ _ _ ↦ le_rfl
  · exact le_maxy le_rfl sqrt_x_le_x

example [ProofData] {f g : ℝ → ℝ≥0∞}
    (hfg : ∀ y, √x ≤ y → y ≤ x → f y ≤ g y) : maxy f ≤ maxy g := by
  exact maxy_le fun y hy₁ hy₂ ↦ (hfg y hy₁ hy₂).trans (le_maxy hy₁ hy₂)

example [ProofData] {f : ℝ → ℝ≥0∞} {B : ℝ}
    (hf : ∀ y, √x ≤ y → y ≤ x → f y ≤ ENNReal.ofReal B) : maxy f ≠ ⊤ := by
  exact maxy_ne_top_of_le_ofReal (maxy_le hf)

/-- A finite-valued but unbounded family has infinite canonical supremum; it is
not silently collapsed as it would be by a conditionally complete real `iSup`. -/
example [ProofData] :
    maxy (fun y ↦ ENNReal.ofReal ((x - √x) / (x - y))) = ⊤ := by
  apply ENNReal.eq_top_of_forall_nnreal_le
  intro r
  let d := x - √x
  let t := (r : ℝ) + 1
  let y := x - d / t
  have hd : 0 < d := by
    dsimp [d]
    exact sub_pos.mpr (Real.sqrt_lt_self_iff.mpr (by linarith [le_x]))
  have ht : 0 < t := by dsimp [t]; positivity
  have ht1 : 1 ≤ t := by
    dsimp [t]
    have hr : 0 ≤ (r : ℝ) := r.2
    linarith
  have hdiv : d / t ≤ d := by
    rw [div_le_iff₀ ht]
    nlinarith
  have hy1 : √x ≤ y := by dsimp [y, d] at hdiv ⊢; linarith
  have hy2 : y ≤ x := by dsimp [y]; exact sub_le_self _ (div_nonneg hd.le ht.le)
  have heval : (x - √x) / (x - y) = t := by
    have hxy : x - y = d / t := by dsimp [y]; ring
    rw [hxy, div_div_eq_mul_div]
    dsimp [d] at hd ⊢
    field_simp [ne_of_gt hd]
  calc
    (r : ℝ≥0∞) = ENNReal.ofReal (r : ℝ) := by simp
    _ ≤ ENNReal.ofReal t := ENNReal.ofReal_le_ofReal (by dsimp [t]; linarith)
    _ = ENNReal.ofReal ((x - √x) / (x - y)) := by rw [heval]
    _ ≤ maxy (fun z ↦ ENNReal.ofReal ((x - √x) / (x - z))) := le_maxy hy1 hy2

end BV
