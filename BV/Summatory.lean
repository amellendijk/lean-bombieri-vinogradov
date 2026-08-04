import Mathlib

import BV.ForMathlib.IsLocallyBounded

noncomputable def Nat.Icc (x y : ℝ) : Finset ℕ :=
  if x ≤ y ∧ 0 ≤ y then Finset.Icc (⌈x⌉₊) (⌊y⌋₊) else ∅

@[simp]
theorem Nat.mem_Icc (x : ℝ) {y : ℝ} (n : ℕ) :
    n ∈ Nat.Icc x y ↔ x ≤ n ∧ n ≤ y := by
  by_cases h : y < x
  · grind [Nat.Icc]
  by_cases hy : 0 ≤ y
  · rw [Nat.Icc, if_pos (by grind)]
    simp [Nat.le_floor_iff hy]
  · grind [Nat.Icc]

theorem Nat.mem_Icc_zero {x : ℝ} (n : ℕ) :
    n ∈ Nat.Icc 0 x ↔ n ≤ x := by simp

theorem Nat.Icc_zero_nonempty {x : ℝ} (hx : 0 ≤ x) : (Nat.Icc 0 x).Nonempty := by
  use 0
  simp [hx]

@[simp]
theorem card_natIcc (x : ℝ) {y : ℝ} (hy : 0 ≤ y):
    (Nat.Icc x y).card = ⌊y⌋₊ + 1 - ⌈x⌉₊ := by
  by_cases hxy : x ≤ y
  · simp [Nat.Icc, hxy, hy]
  · simp [Nat.Icc, hxy]
    rw [eq_comm, Nat.sub_eq_zero_iff_le]
    simp only [Order.add_one_le_iff]
    push Not at hxy
    grw [Nat.floor_lt hy]
    calc _ < x := hxy
    _ ≤ _ := Nat.le_ceil x

@[simp]
theorem card_natIcc_zero (x : ℝ) (hx : 0 ≤ x) :
    (Nat.Icc 0 x).card = ⌊x⌋₊ + 1 := by
  simp [card_natIcc _ hx]

@[simp]
theorem Nat.Icc_eq_empty_of_neg (x : ℝ) {y : ℝ} (hy : y < 0) : Nat.Icc x y = ∅ := by
  simp [Nat.Icc, hy]

@[simp]
theorem Nat.Icc_eq_empty_of_lt (x : ℝ) {y : ℝ} (hy : y < x) : Nat.Icc x y = ∅ := by
  simp [Nat.Icc, hy]

@[grind =>]
theorem Nat.Icc_mono_left {x₁ x₂ y : ℝ} (hx : x₁ ≤ x₂) : Nat.Icc x₂ y ⊆ Nat.Icc x₁ y := by
  intro n
  simp only [mem_Icc, and_imp]
  grind

@[grind =>]
theorem Nat.Icc_mono_right {x y₁ y₂ : ℝ} (hy : y₁ ≤ y₂) : Nat.Icc x y₁ ⊆ Nat.Icc x y₂ := by
  intro n
  simp only [mem_Icc, and_imp]
  grind

noncomputable def summatory {R : Type*} [AddCommMonoid R] (f : ℕ → R) (x : ℝ) : R :=
  ∑ i ∈ Finset.Ioc 0 ⌊x⌋₊, f i

theorem summatory_nonneg {R : Type*} [AddCommMonoid R] [PartialOrder R] [IsOrderedAddMonoid R]
    (f : ℕ → R) (x : ℝ) (hf : ∀ n : ℕ, n ≤ x → 0 ≤ f n ) : 0 ≤ summatory f x := by
  apply Finset.sum_nonneg
  intro n hn
  apply hf
  rw [← Nat.le_floor_iff]
  · exact (Finset.mem_Ioc.mp hn).2
  · by_cases hx : 0 ≤ x
    · exact hx
    · have : ⌊x⌋₊ = 0 := Nat.floor_eq_zero.mpr (by linarith)
      simp [this] at hn

theorem summatory_of_neg {R : Type*} [AddCommMonoid R]
    {f : ℕ → R} {x : ℝ} (hx : x < 0) :
    summatory f x = 0 := by
  have hfloor : ⌊x⌋₊ = 0 := Nat.floor_eq_zero.mpr (by linarith)
  simp [summatory, hfloor]

theorem summatory_of_nonpos {R : Type*} [AddCommMonoid R]
    {f : ℕ → R} {x : ℝ} (hx : x ≤ 0) :
    summatory f x = 0 := by
  have hfloor : ⌊x⌋₊ = 0 := Nat.floor_eq_zero.mpr (by linarith)
  simp [summatory, hfloor]

theorem summatory_apply {R : Type*} [AddCommMonoid R] {f : ℕ → R} {x : ℝ} :
    summatory f x = ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, f n := rfl

theorem Finset.mem_Ioc_zero_floor (x : ℝ) (n : ℕ) :
    n ∈ Finset.Ioc 0 ⌊x⌋₊ ↔ (1 : ℝ) ≤ n ∧ (n : ℝ) ≤ x := by
  by_cases hx : 0 ≤ x
  · rw [Finset.mem_Ioc, Nat.le_floor_iff hx]
    constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨by exact_mod_cast h1, h2⟩
  · have hx' : x < 0 := lt_of_not_ge hx
    have hfloor : ⌊x⌋₊ = 0 := Nat.floor_eq_zero.mpr (by linarith)
    simp [hfloor]
    intro _
    linarith

theorem summatory_eq_zero {R : Type*} [AddCommMonoid R]
    {f : ℕ → R} {x : ℝ} (hf : ∀ n : ℕ, 0 < n → n ≤ x → f n = 0) :
    summatory f x = 0 := by
  by_cases hx : x < 0
  · apply summatory_of_neg hx
  rw [summatory_apply]
  apply Finset.sum_eq_zero
  simp only [Finset.mem_Ioc, and_imp]
  intro n hn hnx
  apply hf n hn
  -- lia now fails here.
  rw [← Nat.le_floor_iff (by linarith)]
  exact hnx

@[congr]
theorem summatory_congr {R : Type*} [AddCommMonoid R]
    {f g : ℕ → R} {x y : ℝ} (hxy : x = y) (h : ∀ n : ℕ, 0 < n → n ≤ x → f n = g n) :
    summatory f x = summatory g y := by
  subst hxy
  apply Finset.sum_congr rfl fun n hn ↦ ?_
  rw [Finset.mem_Ioc] at hn
  apply h n hn.1
  have hx0 : 0 ≤ x := by
    by_contra hx
    have hfloor : ⌊x⌋₊ = 0 := Nat.floor_eq_zero.mpr (by linarith)
    omega
  exact_mod_cast calc n ≤ (⌊x⌋₊ : ℝ) := mod_cast hn.2
    _ ≤ x := Nat.floor_le hx0

@[gcongr]
theorem summatory_le_summatory {R : Type*} [AddCommMonoid R] [PartialOrder R] [IsOrderedAddMonoid R]
    {f g : ℕ → R} {x : ℝ} (h : ∀ n : ℕ, 0 < n → n ≤ x → f n ≤ g n) :
    summatory f x ≤ summatory g x := by
  by_cases hx : x < 0
  · simp [hx, summatory_of_neg]
  · simp_rw [summatory_apply]
    gcongr with n hn
    simp only [Finset.mem_Ioc] at hn
    apply h n hn.1 _
    exact_mod_cast calc n ≤ (⌊x⌋₊ : ℝ) := mod_cast hn.2
      _ ≤ x := Nat.floor_le (by grind)

theorem summatory_congr_fun {R : Type*} [AddCommMonoid R]
    {f g : ℕ → R} {x : ℝ} (h : ∀ n : ℕ, 0 < n → n ≤ x → f n = g n) :
    summatory f x = summatory g x := by
  apply Finset.sum_congr rfl fun n hn ↦ ?_
  rw [Finset.mem_Ioc] at hn
  apply h n hn.1
  have hx0 : 0 ≤ x := by
    by_contra hx
    have hfloor : ⌊x⌋₊ = 0 := Nat.floor_eq_zero.mpr (by linarith)
    omega
  exact_mod_cast calc n ≤ (⌊x⌋₊ : ℝ) := mod_cast hn.2
    _ ≤ x := Nat.floor_le hx0

@[gcongr]
theorem summatory_eq_summatory_of_lt_of_eq_zero {R : Type*} [AddCommMonoid R] [PartialOrder R] [IsOrderedAddMonoid R]
    (f : ℕ → R) (x y : ℝ) (hxy : x ≤ y) (hf : ∀ n : ℕ, x < n ∧ n ≤ y → f n = 0) :
    summatory f x = summatory f y := by
  simp only [summatory]
  apply Finset.sum_subset
  · intro n hn
    rw [Finset.mem_Ioc] at hn ⊢
    exact ⟨hn.1, hn.2.trans (Nat.floor_mono hxy)⟩
  simp only [Finset.mem_Ioc]
  intro n hy hx
  apply hf n
  constructor
  · by_contra hnx
    have hnle : (n : ℝ) ≤ x := le_of_not_gt hnx
    have hx0 : 0 ≤ x := le_trans (by exact_mod_cast hy.1.le) hnle
    have : n ≤ ⌊x⌋₊ := (Nat.le_floor_iff hx0).mpr hnle
    exact hx ⟨hy.1, this⟩
  · have hy0 : 0 ≤ y := by
      by_contra hny
      have hfloor : ⌊y⌋₊ = 0 := Nat.floor_eq_zero.mpr (by linarith)
      omega
    exact_mod_cast calc n ≤ (⌊y⌋₊ : ℝ) := mod_cast hy.2
      _ ≤ y := Nat.floor_le hy0

@[push]
theorem summatory_add_distrib {R : Type*} [AddCommMonoid R] {f g : ℕ → R} {x : ℝ} :
    summatory (fun n ↦ f n + g n) x = summatory f x + summatory g x := by
  simp [summatory, Finset.sum_add_distrib]

@[push]
theorem summatory_sub_distrib {R : Type*} [AddCommGroup R] {f g : ℕ → R} {x : ℝ} :
    summatory (fun n ↦ f n - g n) x = summatory f x - summatory g x := by
  simp [summatory]

@[push]
theorem summatory_neg {R : Type*} [AddCommGroup R] {f : ℕ → R} {x : ℝ} :
    summatory (fun n ↦ - f n) x = - summatory f x := by
  simp [summatory]

@[push]
theorem mul_summatory {R : Type*} [Semiring R] {f : ℕ → R} {c : R} {x : ℝ} :
    summatory (fun n ↦ c * f n) x = c * summatory f x := by
  simp [summatory, Finset.mul_sum]

@[push]
theorem summatory_mul {R : Type*} [Semiring R] {f : ℕ → R} {c : R} {x : ℝ} :
    summatory (fun n ↦ f n * c) x = summatory f x * c := by
  simp [summatory, Finset.sum_mul]

@[simp, push]
theorem summatory_zero {R : Type*} [AddCommMonoid R] {x : ℝ} :
    summatory (fun _ ↦ (0 : R)) x = 0 := by
  simp [summatory]

@[simp, push]
theorem map_summatory {M N : Type*} [AddCommMonoid M] [AddCommMonoid N] {G : Type*} [FunLike G M N] [AddMonoidHomClass G M N] (g : G) (f : ℕ → M) (x : ℝ) :
    g (summatory (fun n ↦ f n) x) = summatory (fun n ↦ g (f n)) x := by
  simp [summatory_apply]

theorem norm_summatory_le {M : Type*} [SeminormedAddCommGroup M] (f : ℕ → M) (x : ℝ) : ‖summatory f x‖ ≤ summatory (fun n ↦ ‖f n‖) x := by
  simp_rw [summatory_apply]
  grw [norm_sum_le]

/- This positivity extension was written by an LLM. -/
open Qq Lean Meta Mathlib.Meta.Positivity in
@[positivity summatory _ _]
def summatory_positivity : PositivityExt where eval {u α} zα pα? e :=
  match pα? with | none => pure .none | some pα => do
  match u, α, e with
  | 0, ~q(ℝ), ~q(summatory $f $x) =>
    let i : Q(ℕ) ← mkFreshExprMVarQ q(ℕ) .syntheticOpaque
    have body : Q(ℝ) := .betaRev f #[i]
    let rbody ← core zα pα body
    match rbody.toNonneg with
    | some pbody =>
      let pr : Q(∀ i, 0 ≤ $f i) ← mkLambdaFVars #[i] pbody
      assumeInstancesCommute
      return .nonnegative q(summatory_nonneg $f $x (fun n _ => $pr n))
    | none => throwError "body not nonneg"
  | _, _, _ => throwError "not summatory"

theorem summatory_le_UB {R : Type*} {f : ℕ → R}
    [NormedAddCommGroup R] [Lattice R] [IsOrderedAddMonoid R] (x : ℝ) (hx : 0 ≤ x) (M : ℝ) (hf : ∀ n : ℕ, n ≤ x → ‖f n‖ ≤ M) :
  ‖summatory f x‖ ≤ x * M := by
  have hM : 0 ≤ M := by
    grw [← hf 0 (mod_cast hx)]
    simp
  grw [summatory, norm_sum_le]
  trans ∑ i ∈ Finset.Ioc 0 ⌊x⌋₊, M
  · gcongr with n hn
    apply hf
    rw [Finset.mem_Ioc] at hn
    exact_mod_cast calc n ≤ (⌊x⌋₊ : ℝ) := mod_cast hn.2
      _ ≤ x := Nat.floor_le hx
  · simp [hx]
    gcongr
    exact Nat.floor_le hx

theorem summatory_le_support_mul_UB {R : Type*} {f : ℕ → R}
    [NormedAddCommGroup R] [Lattice R] [IsOrderedAddMonoid R] (x S : ℝ)
    (hS : 0 ≤ S) (M : ℝ) (hf : ∀ n : ℕ, n ≤ S → ‖f n‖ ≤ M)
    (hf_support : ∀ n : ℕ, n > S → f n = 0) :
  ‖summatory f x‖ ≤ S * M := by
  have hM : 0 ≤ M := by
    grw [← hf 0 (mod_cast hS)]
    simp
  by_cases hx : x < 0
  · rw [summatory_of_neg hx]
    simp only [norm_zero, ge_iff_le]
    positivity
  push Not at hx
  by_cases hyS : x ≤ S
  · apply le_trans <| summatory_le_UB x (by gcongr) M _
    · gcongr
    · grind
  · push Not at hyS
    calc _ = ‖summatory f S‖ := ?A
     _ ≤ _ := summatory_le_UB S hS M hf
    congr 1
    apply (summatory_eq_summatory_of_lt_of_eq_zero ..).symm
    · linarith only [hyS]
    · grind

open Filter
open scoped Topology


open MeasureTheory in
@[fun_prop]
theorem aeStronglyMeasurable_summatory
    {R : Type*} [NormedAddCommGroup R] [MeasurableSpace R] {f : ℕ → R} :
    AEStronglyMeasurable (summatory f) := by
  have : summatory f = (fun n : ℕ ↦ ∑ i ∈ Finset.Ioc 0 n, f i) ∘ (⌊·⌋₊) := by
    ext x; simp [summatory_apply]
  rw [this]
  apply AEStronglyMeasurable.comp_measurable
  · fun_prop
  · fun_prop

@[fun_prop]
theorem measurable_summatory
    {R : Type*} [NormedAddCommGroup R] [MeasurableSpace R] {f : ℕ → R} :
    Measurable (summatory f) := by
  /- This proof was written by Claude Sonnet 4.6 -/
  have : summatory f = (fun n : ℕ ↦ ∑ i ∈ Finset.Ioc 0 n, f i) ∘ (⌊·⌋₊) := by
    ext x; simp [summatory_apply]
  rw [this]
  exact Measurable.of_discrete.comp Nat.measurable_floor

theorem summatory_tendsTo_right
    {R : Type*} [NormedAddCommGroup R] {f : ℕ → R} (x : ℝ) :
    Tendsto (summatory f) (𝓝[≥] x) (𝓝 (summatory f x)) := by
  -- This proof was generated by Claude Sonnet 4.6, using 35% of the Pro session limit.
  apply tendsto_nhds_of_eventually_eq
  filter_upwards [Ico_mem_nhdsGE (Nat.lt_floor_add_one x)] with y hy
  simp only [summatory_apply]
  congr 1; congr 1
  apply le_antisymm
  · exact Nat.lt_succ_iff.mp ((Nat.floor_lt' (Nat.succ_ne_zero _)).mpr (by push_cast; exact hy.2))
  · exact Nat.floor_le_floor hy.1

theorem summatory_tendsTo_left
    {R : Type*} [NormedAddCommGroup R] {f : ℕ → R} (x : ℝ) :
    Tendsto (summatory f) (𝓝[<] x) (𝓝 (∑ n ∈ Finset.Ioo 0 (⌈x⌉₊), f n)) := by
  -- This proof was generated by Claude sonnet 4.6, using 55% of the Pro session limit.
  by_cases hx : 0 ≤ x
  · apply tendsto_nhds_of_eventually_eq
    have hlt_nhd : (⌈x⌉₊ : ℝ) - 1 < x := by linarith [Nat.ceil_lt_add_one hx]
    filter_upwards [Ioc_mem_nhdsLT hlt_nhd, self_mem_nhdsWithin] with y hy hlt
    simp only [summatory_apply]
    apply Finset.sum_congr _ (fun _ _ => rfl)
    ext n
    simp only [Finset.mem_Ioc, Finset.mem_Ioo]
    constructor
    · intro ⟨hn0, hny⟩
      exact ⟨hn0, Nat.lt_ceil.mpr (lt_of_le_of_lt ((Nat.le_floor_iff' (by omega)).mp hny) hlt)⟩
    · intro ⟨hn0, hnx⟩
      refine ⟨hn0, (Nat.le_floor_iff' (by omega)).mpr ?_⟩
      have h1 : (n : ℝ) + 1 ≤ (⌈x⌉₊ : ℝ) := by exact_mod_cast Nat.succ_le_of_lt hnx
      linarith [hy.1]
  · have hx' : x < 0 := not_le.mp hx
    have hceil : ⌈x⌉₊ = 0 := Nat.ceil_eq_zero.mpr hx'.le
    simp only [hceil, Finset.Ioo_self, Finset.sum_empty]
    apply tendsto_nhds_of_eventually_eq
    filter_upwards [self_mem_nhdsWithin] with y hlt
    exact summatory_of_neg (lt_trans hlt hx')

@[fun_prop]
theorem summatory_isLocallyBounded
    {R : Type*} [NormedAddCommGroup R] {f : ℕ → R} :
    IsLocallyBounded (summatory f) := by
  constructor
  intro x
  rw [Filter.BoundedAtFilter]
  have : Set.univ = Set.Iio x ∪ Set.Ici x := by
    simp
  rw [nhds_eq_nhdsWithin_sup_nhdsWithin x this]
  simp only [Asymptotics.isBigO_sup]
  constructor
  · apply Filter.Tendsto.isBigO_one _ (summatory_tendsTo_left _)
  · apply Filter.Tendsto.isBigO_one _ (summatory_tendsTo_right _)

theorem monotone_summatory (g : ℕ → ℝ) (hg : ∀ n, 0 ≤ g n) : Monotone (summatory g) := by
  intro x y hxy
  simp only [summatory]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro n hn
    rw [Finset.mem_Ioc] at hn ⊢
    exact ⟨hn.1, hn.2.trans (Nat.floor_mono hxy)⟩
  intros i _ _
  exact hg i

open MeasureTheory in
theorem summatory_locallyIntegrable (f : ℕ → ℝ) :
    MeasureTheory.LocallyIntegrable (summatory f) := by
  /- This proof (and monotone_summatory) was written by Claude Opus 4.7 with xhigh effort.
  It used 50% of my Pro plan session limit. That's around 75k tokens, mostly output tokens apparently,
  or around $1.80 by API pricing.
  -/
  have heq : summatory f =
      summatory (fun n => max (f n) 0) - summatory (fun n => max (- f n) 0) := by
    funext x
    rw [Pi.sub_apply, ← summatory_sub_distrib]
    apply summatory_congr_fun
    intro n _ _
    rcases le_total 0 (f n) with h | h
    · rw [max_eq_left h, max_eq_right (neg_nonpos_of_nonneg h)]; ring
    · rw [max_eq_right h, max_eq_left (neg_nonneg.mpr h)]; ring
  rw [heq]
  exact (monotone_summatory _ (fun _ => le_max_right _ _)).locallyIntegrable.sub
    (monotone_summatory _ (fun _ => le_max_right _ _)).locallyIntegrable

open MeasureTheory in
theorem summatory_locallyIntegrable_complex (f : ℕ → ℂ) :
    MeasureTheory.LocallyIntegrable (summatory f) := by
  /- This proof was written by Claude Opus 4.7 with medium effort. It used almost half of my Pro subscription session limit. It appears to have used significantly fewer tokens (~1/2 or 2/3), but I did not reset the context.
  prompt:
  ❯ Ah, but the function I care about is complex valued. Please prove that result (potentially as a corollary)
  -/
  have heq : summatory f =
      (fun x => ((summatory (fun n => (f n).re) x : ℝ) : ℂ)) +
      Complex.I • (fun x => ((summatory (fun n => (f n).im) x : ℝ) : ℂ)) := by
    funext x
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, summatory]
    push_cast [← Complex.re_sum, ← Complex.im_sum]
    rw [mul_comm, Complex.re_add_im]
  have hlift : ∀ g : ℕ → ℝ, LocallyIntegrable
      (fun x : ℝ => ((summatory g x : ℝ) : ℂ)) := fun g => by
    rw [locallyIntegrable_iff]
    intro K hK
    exact Complex.ofRealCLM.integrable_comp
      ((locallyIntegrable_iff.mp (summatory_locallyIntegrable g)) K hK)
  rw [heq]
  exact (hlift _).add ((hlift _).smul Complex.I)
