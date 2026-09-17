import Architect
import Mathlib.Order.Filter.ZeroAndBoundedAtFilter
import Mathlib.Analysis.MellinInversion

import PrimeNumberTheoremAnd.MellinCalculus
import PrimeNumberTheoremAnd.MediumPNT

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

/-- The Mellin transform of *any* function is strongly measurable, with no hypotheses on `f`:
either `f` is a.e. strongly measurable on `Ioi 0` and the parametric-integral machinery applies,
or the integrand is non-measurable for every `s` (the kernel `x ^ (s - 1)` never vanishes on
`Ioi 0`), so `mellin f ≡ 0`. -/
theorem stronglyMeasurable_mellin {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (f : ℝ → E) : StronglyMeasurable (𝓜 f) := by
  by_cases hf : AEStronglyMeasurable f (volume.restrict (Ioi 0))
  · obtain ⟨g, hg, hfg⟩ := hf
    have heq : 𝓜 f = fun s => ∫ x in Ioi (0:ℝ), Complex.exp ((s - 1) * Real.log x) • g x := by
      funext s
      show ∫ x in Ioi (0:ℝ), (x:ℂ) ^ (s - 1) • f x = _
      refine integral_congr_ae ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioi, hfg] with x hx hfgx
      rw [hfgx, Complex.cpow_def_of_ne_zero (ofReal_ne_zero.mpr hx.ne'),
        ← Complex.ofReal_log hx.le, mul_comm]
    rw [heq]
    have hF : StronglyMeasurable fun p : ℂ × ℝ =>
        Complex.exp ((p.1 - 1) * Real.log p.2) • g p.2 :=
      ((Complex.measurable_exp.comp ((measurable_fst.sub measurable_const).mul
        (Complex.measurable_ofReal.comp (Real.measurable_log.comp
          measurable_snd)))).stronglyMeasurable).smul (hg.comp_measurable measurable_snd)
    exact hF.integral_prod_right'
  · have h0 : 𝓜 f = fun _ => 0 := by
      funext s
      refine integral_undef fun hInt => hf ?_
      have hker : Measurable fun x : ℝ => (Complex.exp ((s - 1) * Real.log x))⁻¹ :=
        (Complex.measurable_exp.comp (measurable_const.mul
          (Complex.measurable_ofReal.comp Real.measurable_log))).inv
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

@[fun_prop]
theorem measurable_mellin {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [MeasurableSpace E] [BorelSpace E] (f : ℝ → E) : Measurable (𝓜 f) :=
  (stronglyMeasurable_mellin f).measurable

/-- Composition form so that `fun_prop` can close `StronglyMeasurable` goals about
`fun a => 𝓜 f (g a)` (e.g. along a vertical line `g = fun t => σ + t * I`). -/
@[fun_prop]
theorem stronglyMeasurable_mellin_comp {α : Type*} [MeasurableSpace α]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (f : ℝ → E)
    {g : α → ℂ} (hg : Measurable g) :
    StronglyMeasurable (fun a => 𝓜 f (g a)) :=
  (stronglyMeasurable_mellin f).comp_measurable hg

/-- Composition form so that `fun_prop` can close `AEStronglyMeasurable` goals about
`fun a => 𝓜 f (g a)` (it does not route them through `Measurable` on its own). -/
@[fun_prop]
theorem aestronglyMeasurable_mellin_comp {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (f : ℝ → E)
    {g : α → ℂ} (hg : Measurable g) :
    AEStronglyMeasurable (fun a => 𝓜 f (g a)) μ :=
  (stronglyMeasurable_mellin_comp f hg).aestronglyMeasurable

/-- Variant of MellinOfPsi on aribtrary vertial strips. `hσ₂` is unnecessary but harmless.  -/
@[blueprint "mellin_bump_bounded" (latexEnv := "lemma")]
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
      · grind
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
          · push Not at hx' hs_pn
            right
            trans ((1 / 2) ^ s.re)
            · apply Real.rpow_le_rpow_of_nonpos
              · positivity
              · exact hx.1
              · exact hs_pn.le
            · apply Real.rpow_le_rpow_of_exponent_ge_of_imp
              · positivity
              · norm_num
              · exact hσ₁s
              · simp
        rw [norm_mul]
        convert mul_le_mul f_bound pow_bound (norm_nonneg _) ?_ using 1
        · rfl
        · simp [f]
        · positivity
  have Cnonneg : 0 ≤ C := by
    positivity
  by_cases CeqZero : C = 0
  · refine ⟨1, by positivity, ?_⟩
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
    filter_upwards [eventually_lt_nhds (show (0 : ℝ) < 1/2 by positivity)
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

lemma mellin_bump_bounded_aux
    {ν : ℝ → ℝ} (diffν : ContDiff ℝ 1 ν)
    (suppν : ν.support ⊆ Set.Icc (1 / 2) 2) :
    (fun s ↦ 𝓜 (fun x ↦ (ν x : ℂ)) s) =O[nhds 0] fun _ ↦ (1:ℝ) := by
  exact mellin_bump_differentiable diffν suppν
    |>.continuous.continuousAt (x := 0) |>.boundedAtFilter

@[blueprint (latexEnv := "lemma") (title := /-- The Mellin transform of a bump is bounded on strips -/) (statement := /--
Let $\nu \in C^1(\R)$ be supported in $[1/2, 2]$ and let $\sigma_1 \le \sigma_2$ with $\sigma_2 \ge 0$. Then
there is a constant $C$ such that $\|\mathcal{M}[\nu](s)\| \le C \|s\|^{-1}$ for all $s \ne 0$ with
$\sigma_1 \le \Re s \le \sigma_2$; consequently $\mathcal M[\nu]$ is bounded on the whole strip
$\{\sigma_1 \le \Re s \le \sigma_2\}$.
-/) (proof := /--
Integration by parts (valid since $\nu$ has compact support in $(0,\infty)$) gives
$\mathcal M[\nu](s) = \int_0^\infty \nu(u) u^{s-1}\,\mathrm{d}u = -\frac{1}{s} \int_0^\infty \nu'(u) u^{s}\,\mathrm{d}u$
for $s \ne 0$. On $[1/2, 2]$ we have $|u^s| = u^{\Re s} \le \max(2^{\sigma_2}, 2^{-\sigma_1})$, and $|\nu'|$ is
bounded by its maximum on $[1/2,2]$; the interval has length $3/2$. This gives the first bound with
$C = \tfrac32 \max|\nu'| \cdot \max(2^{\sigma_2}, 2^{-\sigma_1})$. For boundedness on the strip, note that
$\mathcal M[\nu]$ is entire (the Mellin integral of a compactly supported $C^1$ function converges for
every $s$), hence bounded near $s = 0$; away from a small ball around $0$ the first bound applies.
-/)]
lemma mellin_bump_bounded {σ₁ σ₂ : ℝ} (hσ₂ : 0 ≤ σ₂) {ν : ℝ → ℝ} (diffν : ContDiff ℝ 1 ν)
    (suppν : ν.support ⊆ Set.Icc (1 / 2) 2) :
    𝓜 (fun x ↦ (ν x : ℂ)) =O[principal {s | σ₁ ≤ s.re ∧ s.re ≤ σ₂}] fun _ ↦ (1 : ℝ) := by
  obtain ⟨r, hr⟩ := eventually_mem_nhdsWithin.and
    (isBigO_nhds_eventually_principal (X := ℂ) (mellin_bump_bounded_aux diffν suppν)) |>.exists
  simp only [mem_Ioi, dist_zero_right] at hr
  have h₄ :
    (𝓜 fun x => ↑(ν x : ℂ)) =O[𝓟 {s | σ₁ ≤ s.re ∧ s.re ≤ σ₂ ∧ s ≠ 0 ∧ r ≤ ‖s‖}]
      fun s => (1 : ℝ) :=
    ((MellinOfPsi_filter (σ₁ := σ₁) hσ₂ diffν suppν).mono ?_).trans
      ((Complex.inv_isBigO_one hr.1).mono ?_)
  · have := h₄.sup hr.2
    simp only [ne_eq, sup_principal, ← setOf_or] at this
    apply this.mono
    simp only [le_principal_iff, mem_principal, setOf_subset_setOf, and_imp]
    intro s hs₁ hs₂
    by_cases hs : ‖s‖ < r
    · simp [hs]
    · push Not at hs
      left
      simp [hs]
      refine ⟨hs₁, hs₂, ?_⟩
      rintro rfl
      simp only [norm_zero] at hs
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

/--
Written by Claude:

In case the comments don't give it away, this lemma is written by claude. It's adapting a result
that was implicit in MediumPNT.

The Mellin transform of the smoothed indicator `Smooth1 ν ε` is vertically integrable along the
line `Re s = σ`, for any `0 < σ ≤ 2`. The integrand is `O(1/(σ² + t²))` by `MellinOfSmooth1b`, and
`t ↦ (σ² + t²)⁻¹` is integrable since `σ ≠ 0`. (This is the content of
`SmoothedChebyshevDirichlet_aux_integrable` in `MediumPNT`, generalised from `1 < σ` to `0 < σ`.) -/
@[blueprint "Smooth1_mellinInv_mellin_eq" (latexEnv := "lemma")]
lemma Smooth1_verticalIntegrable
    {ν : ℝ → ℝ}
    (diffν : ContDiff ℝ 1 ν)
    (νpos : ∀ x > 0, 0 ≤ ν x)
    (suppν : ν.support ⊆ Icc (1 / 2) 2)
    (mass_one : ∫ x in Ioi 0, ν x / x = 1)
    {ε : ℝ} (εpos : 0 < ε) (ε_lt_one : ε < 1)
    {σ : ℝ} (σ_pos : 0 < σ) (σ_le : σ ≤ 2) :
    VerticalIntegrable (𝓜 (fun x ↦ (Smooth1 ν ε x : ℂ))) σ := by
  -- Abbreviation for the `(σ + t*I).re = σ` simplification used repeatedly below.
  have hre : ∀ t : ℝ, ((σ : ℂ) + t * I).re = σ := fun t => by simp
  obtain ⟨c, cpos, hc⟩ := MellinOfSmooth1b diffν suppν
  have hσ : σ ≠ 0 := σ_pos.ne'
  have hg : Integrable (fun t : ℝ ↦ (σ ^ 2 + t ^ 2)⁻¹) := by
    have key : Integrable (fun t : ℝ ↦ (σ ^ 2)⁻¹ * (1 + (σ⁻¹ * t) ^ 2)⁻¹) :=
      (integrable_inv_one_add_sq.comp_mul_left' (inv_ne_zero hσ)).const_mul _
    field_simp at key ⊢
    exact key
  refine Integrable.mono' (hg.const_mul (c / ε)) ?_ (Filter.Eventually.of_forall fun t ↦ ?_)
  · -- Strong measurability via continuity (`𝓜 …` is differentiable on `re > 0`).
    apply Continuous.aestronglyMeasurable
    refine continuous_iff_continuousAt.mpr fun t ↦ ?_
    have hline : ContinuousAt (fun y : ℝ ↦ (σ : ℂ) + y * I) t := by fun_prop
    exact ContinuousAt.comp (g := fun s : ℂ ↦ 𝓜 (fun x ↦ (Smooth1 ν ε x : ℂ)) s)
      (f := fun y : ℝ ↦ (σ : ℂ) + y * I)
      (Smooth1MellinDifferentiable diffν suppν ⟨εpos, ε_lt_one⟩ νpos mass_one
        (s := σ + t * I) (by simpa)).continuousAt hline
  · -- Pointwise `O(1/(σ² + t²))` bound from `MellinOfSmooth1b`.
    calc ‖𝓜 (fun x ↦ (Smooth1 ν ε x : ℂ)) (σ + t * I)‖
        ≤ c * (ε * ‖(σ : ℂ) + t * I‖ ^ 2)⁻¹ :=
          hc (σ / 2) (by positivity) (σ + t * I) (by grind) (by simp [σ_le])
            ε εpos ε_lt_one
      _ = c / ε * (σ ^ 2 + t ^ 2)⁻¹ := by
          rw [Complex.sq_norm, Complex.normSq_add_mul_I, mul_inv]; ring

/--
In case the comments don't give it away, this lemma is written by claude. It's adapting a result
that was implicit in MediumPNT

The smoothed indicator `Smooth1 ν ε` equals the inverse Mellin transform of its own
Mellin transform — equation (*) of `notes/theorem26_6_smooth.md`. This is the specialization of
`mellinInv_mellin_eq` to `f = fun x ↦ (Smooth1 ν ε x : ℂ)`, proved implicitly inside
`SmoothedChebyshevDirichlet` in `PrimeNumberTheoremAnd.MediumPNT`. The vertical integrability of
the Mellin transform is established inline (as in `SmoothedChebyshevDirichlet_aux_integrable`) from
the `O(1/‖s‖²)` decay of `MellinOfSmooth1b`, valid for any `0 < σ ≤ 2`. -/
@[blueprint (latexEnv := "lemma") (title := /-- Mellin inversion for the smoothed cutoff -/) (statement := /--
Let $\nu$ be a bump function (\Cref{Flat.Bump}; only $\nu \in C^1$ is needed), $0 < \varepsilon < 1$ and
$0 < \sigma \le 2$. Then $t \mapsto \mathcal M[\widetilde 1_\varepsilon](\sigma + it)$ is integrable on $\R$ and,
for every $u > 0$,
$$\widetilde{1}_\varepsilon(u) = \frac{1}{2\pi} \int_{-\infty}^{\infty} u^{-(\sigma + it)}\, \mathcal{M}[\widetilde 1_\varepsilon](\sigma + it)\, \mathrm{d}t .$$
-/) (proof := /--
Integrability: by the bound $\|\mathcal M[\widetilde 1_\varepsilon](s)\| \ll_\nu 1/(\varepsilon \|s\|^2)$ on the strip
$\sigma/2 \le \Re s \le 2$ (\Cref{MellinOfSmooth1b}), the integrand is dominated by a constant multiple of
$(\sigma^2 + t^2)^{-1}$, which is integrable; measurability
follows from continuity of $\mathcal M[\widetilde 1_\varepsilon]$ on $\Re s > 0$. The inversion formula is then
Mathlib's Mellin inversion theorem (\texttt{mellinInv\_mellin\_eq}), whose hypotheses are: convergence
of the Mellin integral at $\sigma$ (\texttt{Smooth1MellinConvergent}), vertical integrability of the
transform (just shown), and continuity of $\widetilde 1_\varepsilon$ at $u$ (\texttt{Smooth1ContinuousAt}).
-/)]
lemma Smooth1_mellinInv_mellin_eq
    {ν : ℝ → ℝ}
    (diffν : ContDiff ℝ 1 ν)
    (νpos : ∀ x > 0, 0 ≤ ν x)
    (suppν : ν.support ⊆ Icc (1 / 2) 2)
    (mass_one : ∫ x in Ioi 0, ν x / x = 1)
    {ε : ℝ} (εpos : 0 < ε) (ε_lt_one : ε < 1)
    {σ : ℝ} (σ_pos : 0 < σ) (σ_le : σ ≤ 2)
    {x : ℝ} (hx : 0 < x) :
    mellinInv σ (𝓜 (fun x ↦ (Smooth1 ν ε x : ℂ))) x
      = (Smooth1 ν ε x : ℂ) := by
  apply mellinInv_mellin_eq σ (fun x ↦ (Smooth1 ν ε x : ℂ)) hx
  · -- `MellinConvergent` at `σ`.
    exact Smooth1MellinConvergent diffν suppν ⟨εpos, ε_lt_one⟩ νpos mass_one
      (by positivity)
  · -- `VerticalIntegrable (𝓜 …) σ`.
    exact Smooth1_verticalIntegrable diffν νpos suppν mass_one εpos ε_lt_one σ_pos σ_le
  · -- `ContinuousAt` of `fun x ↦ ↑(Smooth1 ν ε x)` at `x`.
    exact (Smooth1ContinuousAt diffν νpos suppν εpos hx).ofReal
