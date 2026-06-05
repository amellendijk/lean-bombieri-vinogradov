import Mathlib.Order.Filter.ZeroAndBoundedAtFilter

import PrimeNumberTheoremAnd.MellinCalculus

import BV.Mathlib.MeasureTheory.Function.LocallyIntegrable

local notation (name := mellintransform) "𝓜" => mellin

open Filter Set Complex MeasureTheory Real Asymptotics

theorem ContinuousAt.boundedAtFilter {X Y : Type*} [TopologicalSpace X] [SeminormedAddCommGroup Y]
    (f : X → Y) (x : X) (hf : ContinuousAt f x) :
    (nhds x).BoundedAtFilter f := by
  simp [BoundedAtFilter]
  simp [IsBigO_def, IsBigOWith_def]
  exact ⟨_, hf.tendsto.eventually ((continuous_norm (E := Y)).tendsto (f x)
    |>.eventually_le_const (u := ‖f x‖ + 1) (by grind))⟩

/-- Variant of MellinOfPsi on aribtrary vertial strips. `hσ₂` is unnecessary but harmless.  -/
lemma MellinOfPsi_better {σ₁ σ₂ : ℝ} (hσ₂ : 0 ≤ σ₂) {ν : ℝ → ℝ} (diffν : ContDiff ℝ 1 ν)
    (suppν : ν.support ⊆ Set.Icc (1 / 2) 2) :
    ∃ C > 0, ∀ (s : ℂ) (_ : s ≠ 0) (_ : σ₁ ≤ s.re) (_ : s.re ≤ σ₂),
    ‖𝓜 (fun x ↦ (ν x : ℂ)) s‖ ≤ C * ‖s‖⁻¹ := by
  let f := fun (x : ℝ) ↦ ‖deriv ν x‖
  have cont : ContinuousOn f (Icc (1 / 2) 2) :=
    (Continuous.comp (by continuity) <| diffν.continuous_deriv (by norm_num)).continuousOn
  obtain ⟨a, _, max⟩ := isCompact_Icc.exists_isMaxOn (f := f) (by norm_num) cont
  let C : ℝ := f a * (2 ^ σ₂ ⊔ (1 / 2) ^ σ₁) * (3 / 2)
  have mainBnd : ∀ (s : ℂ), s ≠ 0 → σ₁ ≤ s.re → s.re ≤ σ₂ →
      ‖𝓜 (fun x ↦ (ν x : ℂ)) s‖ ≤ C * ‖s‖⁻¹ := by
    intro s hs₁ hσ₁s hs₂
    simp only [mellin, f, MellinOfPsi_aux diffν suppν hs₁, norm_mul, smul_eq_mul, mul_comm]
    gcongr
    · simp
    calc
      _ ≤ ∫ (x : ℝ) in Ioi 0, ‖(deriv ν x * (x : ℂ) ^ s)‖ := ?_
      _ = ∫ (x : ℝ) in Icc (1 / 2) 2, ‖(deriv ν x * (x : ℂ) ^ s)‖ := ?_
      _ ≤ ‖∫ (x : ℝ) in Icc (1 / 2) 2, ‖(deriv ν x * (x : ℂ) ^ s)‖‖ :=
          le_abs_self _
      _ ≤ _ := ?_
    · simp_rw [norm_integral_le_integral_norm]
    · apply SetIntegral.integral_eq_integral_inter_of_support_subset_Icc
      · simp only [Function.support_abs, Function.support_mul, Function.support_ofReal]
        apply subset_trans (by apply inter_subset_left) <| Function.support_deriv_subset_Icc suppν
      · exact (Icc_subset_Ioi_iff (by norm_num)).mpr (by norm_num)
    · have := intervalIntegral.norm_integral_le_of_norm_le_const' (C := f a * (2 ^ σ₂ ⊔ (1 / 2)^σ₁))
        (f := fun x ↦ f x * ‖(x : ℂ) ^ s‖) (a := (1 / 2 : ℝ)) ( b := 2) (by norm_num) ?_
      · simp only [Real.norm_eq_abs, norm_real, norm_mul] at this ⊢
        rwa [(by norm_num: |(2 : ℝ) - 1 / 2| = 3 / 2),
            intervalIntegral.integral_of_le (by norm_num), ← integral_Icc_eq_integral_Ioc] at this
      · intro x hx;
        have f_bound := isMaxOn_iff.mp max x hx
        have pow_bound : ‖(x : ℂ) ^ s‖ ≤ (2 ^ σ₂ ⊔ (1 / 2)^(σ₁)) := by
          rw [norm_cpow_eq_rpow_re_of_pos (by linarith [mem_Icc.mp hx])]
          have xpos : 0 ≤ x := by linarith [(mem_Icc.mp hx).1]
          simp only [le_sup_iff]
          by_cases hs_pn : 0 ≤ s.re
          · left
            grw [hx.2]
            gcongr
            norm_num
          by_cases hx' : 1 ≤ x
          · left
            grw [hs₂, hx.2]
            · exact hx'
          · push Not at hx' hs_pn
            right
            trans ((1 / 2) ^ s.re)
            · apply Real.rpow_le_rpow_of_nonpos
              · norm_num
              · exact hx.1
              · exact hs_pn.le
            · apply Real.rpow_le_rpow_of_exponent_ge_of_imp
              · norm_num
              · norm_num
              · exact hσ₁s
              · simp
        convert mul_le_mul f_bound pow_bound (norm_nonneg _) ?_ using 1 <;> simp [f]
  have Cnonneg : 0 ≤ C := by
    simp [C, f]
    positivity
  by_cases CeqZero : C = 0
  · refine ⟨1, by linarith, ?_⟩
    intro s hs₁ hσ₁s hs₂
    have := mainBnd s hs₁ hσ₁s hs₂
    rw [CeqZero, zero_mul] at this
    have : 0 ≤ 1 * ‖s‖⁻¹ := by positivity
    linarith
  · exact ⟨C, lt_of_le_of_ne Cnonneg fun a ↦ CeqZero (id (Eq.symm a)), mainBnd⟩


lemma MellinOfPsi_filter {σ₁ σ₂ : ℝ} (hσ₂ : 0 ≤ σ₂) {ν : ℝ → ℝ} (diffν : ContDiff ℝ 1 ν)
    (suppν : ν.support ⊆ Set.Icc (1 / 2) 2) :
    𝓜 (fun x ↦ (ν x : ℂ)) =O[principal {s | σ₁ ≤ s.re ∧ s.re ≤ σ₂ ∧ s ≠ 0}]
      fun s ↦ s⁻¹ := by
  simp [IsBigO_def]
  peel MellinOfPsi_better hσ₂ (σ₁ := σ₁) diffν suppν with c hc
  grind

attribute [fun_prop] Continuous.locallyIntegrable LocallyIntegrable.locallyIntegrableOn

lemma mellin_bump_differentiable
    {ν : ℝ → ℝ} (diffν : ContDiff ℝ 1 ν)
    (suppν : ν.support ⊆ Set.Icc (1 / 2) 2) :
    Differentiable ℂ (𝓜 fun x ↦ (ν x : ℂ)) := by
  intro s
  apply mellin_differentiableAt_of_isBigO_rpow (a := s.re + 1) (b := s.re - 1)
  · -- I'd like fun_prop to solve this...
    apply ((continuous_ofReal).comp diffν.continuous |>.locallyIntegrable.locallyIntegrableOn _)
  · apply Filter.Eventually.isBigO
    filter_upwards [eventually_gt_atTop 2] with x hx
    have := Set.notMem_subset suppν (a := x)
    simp only [one_div, mem_Icc, not_and, not_le, hx, implies_true, Function.mem_support, ne_eq,
      Decidable.not_not, forall_const] at this
    simp [this]
    positivity
  · simp
  · apply Filter.Eventually.isBigO
    filter_upwards [eventually_lt_nhds (show (0 : ℝ) < 1/2 by norm_num)
      |>.filter_mono (nhdsWithin_le_nhds), eventually_mem_nhdsWithin] with x hx hx'
    have := Set.notMem_subset suppν (a := x)
    simp only [one_div, mem_Icc, not_and, not_le, Function.mem_support, ne_eq,
      Decidable.not_not] at this
    simp only [mem_Ioi] at hx'
    rw [this]
    · simp only [ofReal_zero, norm_zero, neg_sub, ge_iff_le]
      positivity
    · grind
  · simp


lemma Complex.inv_isBigO_one {r : ℝ} (hr : 0 < r) :
    (fun s : ℂ ↦ s⁻¹) =O[principal {z | r ≤ ‖z‖}] fun _ ↦ (1 : ℝ) := by
  apply IsBigOWith.isBigO (c := r⁻¹)
  rw [IsBigOWith_def]
  simp only [norm_inv, one_mem, CStarRing.norm_of_mem_unitary, mul_one, eventually_principal,
    mem_setOf_eq]
  intro s hs
  gcongr

lemma exists_radius_eventually_of_nhds {X : Type*} {x : X} [PseudoMetricSpace X]
    {P : X → Prop} (hP : ∀ᶠ s in nhds x, P s) :
    ∃ r > 0, ∀ᶠ s in (principal {s | dist s x < r}), P s := by
  rw [Metric.nhds_basis_ball (x := x) |>.eventually_iff] at hP
  obtain ⟨r, hr, h⟩ := hP
  simp only [Metric.mem_ball] at h
  use r
  simp +contextual [h, hr]

open scoped Topology in
lemma eventually_principal_of_nhds {X : Type*} [PseudoMetricSpace X]
    {x : X} {P : X → Prop} (hP : ∀ᶠ s in nhds x, P s) :
    ∀ᶠ r in 𝓝[>] 0, ∀ᶠ s in (principal {s | dist s x < r}), P s := by
  obtain ⟨r, hr_pos, hr⟩ := exists_radius_eventually_of_nhds hP
  filter_upwards [eventually_lt_nhds hr_pos |>.filter_mono nhdsWithin_le_nhds]
  intro a ha
  apply hr.filter_mono
  simp
  grind

open scoped Topology in
lemma isBigO_nhds_eventually_principal {X E F : Type*} [PseudoMetricSpace X] [Norm E] [Norm F]
    {f : X → E} {g : X → F} {x : X} (h : f =O[nhds x] g) :
    ∀ᶠ r in 𝓝[>] 0, f =O[principal {s | dist s x < r}] g := by
  have ⟨c, hc⟩ := h.isBigOWith
  filter_upwards [eventually_principal_of_nhds hc.bound] with r hr
  rw [IsBigO_def]
  use c
  simpa using hr

lemma test
    {ν : ℝ → ℝ} (diffν : ContDiff ℝ 1 ν)
    (suppν : ν.support ⊆ Set.Icc (1 / 2) 2) :
    (fun s ↦ 𝓜 (fun x ↦ (ν x : ℂ)) s) =O[nhds 0] fun _ ↦ (1:ℝ) := by
  exact mellin_bump_differentiable diffν suppν
    |>.continuous.continuousAt (x := 0) |>.boundedAtFilter

lemma mellin_bump_bounded {σ₁ σ₂ : ℝ} (hσ₂ : 0 ≤ σ₂) {ν : ℝ → ℝ} (diffν : ContDiff ℝ 1 ν)
    (suppν : ν.support ⊆ Set.Icc (1 / 2) 2) :
    𝓜 (fun x ↦ (ν x : ℂ)) =O[principal {s | σ₁ ≤ s.re ∧ s.re ≤ σ₂ ∧ s ≠ 0}] fun _ ↦ (1 : ℝ) := by
  obtain ⟨r, hr⟩ := eventually_mem_nhdsWithin.and
    (isBigO_nhds_eventually_principal (X := ℂ) (test diffν suppν)) |>.exists
  simp only [mem_Ioi, dist_zero_right] at hr
  have h₄ :
    (𝓜 fun x => ↑(ν x : ℂ)) =O[𝓟 {s | σ₁ ≤ s.re ∧ s.re ≤ σ₂ ∧ s ≠ 0 ∧ r ≤ ‖s‖}]
      fun s => (1 : ℝ) :=
    ((MellinOfPsi_filter (σ₁ := σ₁) hσ₂ diffν suppν).mono ?_).trans
      ((Complex.inv_isBigO_one hr.1).mono ?_)
  · have := h₄.sup hr.2
    simp only [ne_eq, sup_principal, ← setOf_or] at this
    apply this.mono
    simp only [ne_eq, le_principal_iff, mem_principal, setOf_subset_setOf, and_imp]
    grind
  · simp
    grind
  · simp

lemma mellin_partial_int {σ₁ σ₂ : ℝ}
    {ν : ℝ → ℝ} {k : ℕ} (diffν : ContDiff ℝ k ν)
    (suppν : ν.support ⊆ Set.Icc (1 / 2) 2) (s : ℂ) :
    mellin (fun x ↦ (ν x : ℂ)) s = s⁻¹ * mellin (fun x ↦ (↑(deriv ν x) : ℂ)) (s+1) := by
  sorry

lemma mellin_isBigO_pow {σ₁ σ₂ : ℝ}
    {ν : ℝ → ℝ} {k : ℕ} (diffν : ContDiff ℝ k ν)
    (suppν : ν.support ⊆ Set.Icc (1 / 2) 2) :
    𝓜 (fun x ↦ (ν x : ℂ))
      =O[principal (Complex.re ⁻¹' (Set.Icc σ₁ σ₂))]
      fun s ↦ (1+‖s‖)^k := by
  sorry
