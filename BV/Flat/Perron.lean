import Mathlib

import PrimeNumberTheoremAnd.SmoothExistence

import BV.Mellin
import BV.Delta



namespace Mathlib.Meta.Positivity
open Qq Lean Meta

/-- The `positivity` extension which proves that `⨆ i, f i` is nonnegative for a real-valued
function `f`, provided each `f i` is nonnegative. This also handles the bounded supremum
`⨆ i ∈ s, f i`, which unfolds to a nested `iSup`. -/
@[positivity ⨆ _, _]
def evalRealiSup : PositivityExt where eval {u α} zα pα e := do
  match u, α, e with
  | 0, ~q(ℝ), ~q(@iSup ℝ $ι $instSup $f) =>
    let i : Q($ι) ← mkFreshExprMVarQ q($ι) .syntheticOpaque
    have body : Q(ℝ) := .betaRev f #[i]
    let rbody ← core zα pα body
    let some pbody := rbody.toNonneg | throwError "idk"
    let pr : Q(∀ i, 0 ≤ $f i) ← mkLambdaFVars #[i] pbody
    assertInstancesCommute
    return .nonnegative q(Real.iSup_nonneg $pr)
  | _, _, _ => throwError "not a real-valued iSup"

end Mathlib.Meta.Positivity


open ArithmeticFunction Set

class Flat.FG where
  f : ArithmeticFunction ℂ
  g : ArithmeticFunction ℂ
  M : ℝ
  hM_pos : 0 < M
  N : ℝ
  hN_pos : 0 < N
  hf : ∀ n : ℕ, n > M → f n = 0
  hg : ∀ n : ℕ, n > N → g n = 0

open MeasureTheory Set Real ContDiff

class Flat.Bump where
  ν : ℝ → ℝ
  diffν : ContDiff ℝ ∞ ν
  suppν : ν.support ⊆ Icc (1 / 2) 2
  νpos : ∀ x, 0 ≤ ν x
  mass_one : ∫ x in Ici 0, ν x / x = 1

class Flat.ProofData extends FG, Bump where

open Flat.FG Flat.Bump

noncomputable def Flat.T [Bump] [FG] {q : ℕ} (ε y : ℝ) (χ : DirichletCharacter ℂ q) : ℂ :=
  summatory (fun m ↦ summatory (fun n ↦ f m * χ m * g n * χ n * Smooth1 ν ε (m*n/y)) N) M

namespace Flat

open Complex

theorem T_eq_sum_integral {σ : ℝ} (hσ_pos : 0 < σ) (hσ : σ ≤ 2)
    [Bump] [FG] {q : ℕ} {ε : ℝ} (hε_pos : 0 < ε) {χ : DirichletCharacter ℂ q} (y : ℝ) (hy : 1 ≤ y) (hε_one : ε < 1) :
  T ε y χ =
    summatory (fun m ↦ summatory (fun n ↦
      f m * χ m * g n * χ n *
     (1 / (2 * π)) • ∫ t : ℝ, (m*n/y : ℂ) ^ (-(σ + t * I)) •
     mellin (fun x ↦ (Smooth1 ν ε x : ℂ)) (σ + t * I)) N ) M := by
  rw [T]
  congr! 2 with m hm_pos hm n hn_pos hn
  rw [← Smooth1_mellinInv_mellin_eq (σ := σ) (ε := ε) _ (fun x _ ↦ νpos x) suppν _ hε_pos hε_one hσ_pos hσ]
  · rw [mellinInv]
    simp
  · positivity
  · apply diffν.of_le
    simp
  · rw [← MeasureTheory.integral_Ici_eq_integral_Ioi]
    apply mass_one



/--
Written by Claude:
A single term `f m χ(m) m^{-s} · g n χ(n) n^{-s} · (1/y)^{-s} · 𝓜(Smooth1 ν ε)(s)` is
integrable along the vertical line `s = σ + t·I`. The `r^{-(σ+t·I)}` factors all have constant
norm `r^{-σ}`, so the integrand is a bounded (in `t`) multiple of `𝓜(Smooth1 ν ε)(σ + t·I)`, which
is integrable by `Smooth1_verticalIntegrable`. This is the common engine behind the two
integrability side-goals in `T_eq_integral_sum`. -/
theorem integrable_term {σ : ℝ} (hσ_pos : 0 < σ) (hσ : σ ≤ 2)
    [Bump] [FG] {q : ℕ} {ε : ℝ} (hε_pos : 0 < ε) (hε_one : ε < 1)
    {χ : DirichletCharacter ℂ q} {y : ℝ} (hy : 1 ≤ y) (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :
    Integrable (fun t : ℝ =>
      f m * χ ↑m * (m : ℂ) ^ (-((σ : ℂ) + ↑t * I)) *
        (g n * χ ↑n * (n : ℂ) ^ (-((σ : ℂ) + ↑t * I))) *
        (1 / (y : ℂ)) ^ (-((σ : ℂ) + ↑t * I)) •
        mellin (fun x => (↑(Smooth1 ν ε x) : ℂ)) ((σ : ℂ) + ↑t * I)) := by
  have hy0 : 0 < y := by linarith
  -- The Mellin factor is vertically integrable (our new lemma, with `Bump` data adapted).
  have hVI : Integrable (fun t : ℝ =>
      mellin (fun x => (↑(Smooth1 ν ε x) : ℂ)) ((σ : ℂ) + ↑t * I)) :=
    Smooth1_verticalIntegrable (diffν.of_le (by simp)) (fun x _ => νpos x) suppν
      (by rw [← MeasureTheory.integral_Ici_eq_integral_Ioi]; exact mass_one) hε_pos hε_one hσ_pos hσ
  -- The prefactor `Q` collects everything except the Mellin factor.
  have hcont : Continuous (fun t : ℝ => -((σ : ℂ) + ↑t * I)) := by fun_prop
  have e1 : Continuous (fun t : ℝ => (m : ℂ) ^ (-((σ : ℂ) + ↑t * I))) :=
    hcont.const_cpow (Or.inl (by exact_mod_cast hm.ne'))
  have e2 : Continuous (fun t : ℝ => (n : ℂ) ^ (-((σ : ℂ) + ↑t * I))) :=
    hcont.const_cpow (Or.inl (by exact_mod_cast hn.ne'))
  have e3 : Continuous (fun t : ℝ => (1 / (y : ℂ)) ^ (-((σ : ℂ) + ↑t * I))) :=
    hcont.const_cpow (Or.inl (one_div_ne_zero (by exact_mod_cast hy0.ne')))
  have hQcont : Continuous (fun t : ℝ =>
      f m * χ ↑m * g n * χ ↑n * (m : ℂ) ^ (-((σ : ℂ) + ↑t * I)) *
        (n : ℂ) ^ (-((σ : ℂ) + ↑t * I)) * (1 / (y : ℂ)) ^ (-((σ : ℂ) + ↑t * I))) :=
    (((((continuous_const.mul continuous_const).mul continuous_const).mul
      continuous_const).mul e1).mul e2).mul e3
  -- The prefactor has constant norm, hence is bounded.
  have hnorm : ∀ t : ℝ, ‖f m * χ ↑m * g n * χ ↑n * (m : ℂ) ^ (-((σ : ℂ) + ↑t * I)) *
        (n : ℂ) ^ (-((σ : ℂ) + ↑t * I)) * (1 / (y : ℂ)) ^ (-((σ : ℂ) + ↑t * I))‖ =
      ‖f m‖ * ‖χ (↑m : ZMod q)‖ * ‖g n‖ * ‖χ (↑n : ZMod q)‖ *
        ((m : ℝ) ^ (-σ) * (n : ℝ) ^ (-σ) * (1 / y) ^ (-σ)) := by
    intro t
    have hre : (-((σ : ℂ) + ↑t * I)).re = -σ := by simp
    simp only [norm_mul]
    rw [Complex.norm_natCast_cpow_of_pos hm, Complex.norm_natCast_cpow_of_pos hn,
      show (1 / (y : ℂ)) = ((1 / y : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_cpow_eq_rpow_re_of_pos (by positivity), hre]
    ring
  -- Bounded × integrable, then reassociate to the target shape.
  refine (hVI.bdd_mul hQcont.aestronglyMeasurable
    (Filter.Eventually.of_forall fun t => (hnorm t).le)).congr
    (Filter.Eventually.of_forall fun t => ?_)
  simp only [smul_eq_mul]; ring


-- lemma summaotry_mul_char_mul_pow_ll (f : ℕ → ℂ) {σ : ℝ} (hσ_pos : 0 < σ) {t : ℝ} :
--     ‖summatory (fun m ↦ f m * χ m * m ^ (-(σ + t * I))) M‖ ≤

theorem T_eq_integral_sum {σ : ℝ} (hσ_pos : 0 < σ) (hσ : σ ≤ 2)
    [Bump] [FG] {q : ℕ} {ε : ℝ} (hε_pos : 0 < ε) {χ : DirichletCharacter ℂ q} (y : ℝ) (hy : 1 ≤ y) (hε_one : ε < 1) :
  T ε y χ =
     (1 / (2 * π)) • ∫ t : ℝ,
    summatory (fun m ↦ f m * χ m * m ^ (-(σ + t * I))) M *
    summatory (fun n ↦ g n * χ n * n ^ (-(σ + t * I))) N *
     (1/y : ℂ) ^ (-(σ + t * I)) •
     mellin (fun x ↦ (Smooth1 ν ε x : ℂ)) (σ + t * I) := by
  rw [T_eq_sum_integral hσ_pos hσ hε_pos y hy hε_one]
  pull summatory
  simp_rw [summatory_apply]
  rw [MeasureTheory.integral_finset_sum, Finset.smul_sum, Finset.sum_comm]
  congr! with n hn
  rw [MeasureTheory.integral_finset_sum, Finset.smul_sum]
  · congr! 1 with m hm
    simp [← integral_const_mul]
    congr! 2 with t
    simp_rw [div_eq_mul_inv]
    norm_cast
    rw [Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg]
    push_cast
    rw [show (m * n : ℂ) = ((m:ℝ) * (n:ℝ) : ℂ) by simp, Complex.mul_cpow_ofReal_nonneg]
    simp
    ring
    · positivity
    · positivity
    · positivity
    · positivity
  -- The two integrability conditions were proven by Claude
  · -- Inner sum (over `m ≤ M`), `n` fixed: each term is integrable by `integrable_term`.
    intro m hm
    exact integrable_term hσ_pos hσ hε_pos hε_one hy m n
      (Finset.mem_Ioc.mp hm).1 (Finset.mem_Ioc.mp hn).1
  · -- Outer sum (over `n ≤ N`): a finite sum of `integrable_term` terms.
    intro i hi
    refine integrable_finset_sum _ fun m hm => ?_
    exact integrable_term hσ_pos hσ hε_pos hε_one hy m i
      (Finset.mem_Ioc.mp hm).1 (Finset.mem_Ioc.mp hi).1

theorem sup_summatory_eq_sup_nat {f : ℕ → ℂ}
    {x : ℝ} (hx : 1 ≤ x) :
  open Classical in
      ⨆ y ∈ Set.Icc 1 x, ‖summatory f y‖ =
      ⨆ K ∈ Set.Icc 1 ⌊x⌋₊, ‖summatory f (K + 2⁻¹)‖ := by
  have hfloor_add_half {n : ℕ} : ⌊(n + 2⁻¹: ℝ)⌋₊ = n := by
    rw [add_comm, Nat.floor_add_natCast (show 0 ≤ (2⁻¹ : ℝ) by norm_num)]
    norm_num
  apply le_antisymm
  · apply Real.iSup_le _ (by positivity)
    intro y
    apply Real.iSup_le _ (by positivity)
    intro h
    have : Finset.Icc 1 ⌊x⌋₊ = Icc 1 ⌊x⌋₊ := by simp
    rw [← this]
    grw [← le_ciSup (c := ⌊y⌋₊)]
    · have : ⌊y⌋₊ ∈ Icc 1 (⌊x⌋₊) := by
        simp only [mem_Icc, Nat.one_le_floor_iff]
        simp only [mem_Icc] at h
        refine ⟨h.1, ?_⟩
        gcongr
        exact h.2
      simp only [Finset.coe_Icc, this, ciSup_unique, ge_iff_le]
      apply le_of_eq
      simp_rw [summatory_apply, hfloor_add_half]
    · -- NOTE: This subproof is a claudeism. Frankly I'd like to avoid having
      -- a subgoal this ugly in the first place
      refine ⟨∑ k ∈ Finset.Icc 1 ⌊x⌋₊, ‖summatory f (k + 2⁻¹)‖, ?_⟩
      rintro v ⟨K, rfl⟩
      exact Real.iSup_le
        (fun hK ↦ Finset.single_le_sum (f := fun k : ℕ ↦ ‖summatory f ((k : ℝ) + 2⁻¹)‖)
          (fun _ _ ↦ norm_nonneg _) (Finset.mem_coe.mp hK))
        (Finset.sum_nonneg fun k _ ↦ norm_nonneg (summatory f ((k : ℝ) + 2⁻¹)))
  · apply Real.iSup_le _ (by positivity)
    intro K
    apply Real.iSup_le _ (by positivity)
    intro h
    grw [← le_ciSup (c := (K : ℝ))]
    · have : ↑K ∈ Icc 1 x := by
        simp only [mem_Icc, Nat.one_le_cast] at h ⊢
        refine ⟨h.1, ?_⟩
        rw [Nat.le_floor_iff] at h
        · exact h.2
        · grind
      simp [this, ciSup_unique, ge_iff_le]
      simp [summatory_apply, hfloor_add_half]
    · -- NOTE: This subproof is a claudeism. (see similar comment above)
      refine ⟨summatory (fun n ↦ ‖f n‖) x, ?_⟩
      rintro v ⟨y, rfl⟩
      apply Real.iSup_le _ (summatory_nonneg _ _ fun n _ ↦ norm_nonneg _)
      intro hy
      calc ‖summatory f y‖ ≤ summatory (fun n ↦ ‖f n‖) y := by
            rw [summatory, summatory]
            exact norm_sum_le _ _
        _ ≤ summatory (fun n ↦ ‖f n‖) x := by
            rw [summatory, summatory]
            exact Finset.sum_le_sum_of_subset_of_nonneg (Nat.Icc_mono_right hy.2)
              fun _ _ _ ↦ norm_nonneg _


theorem temp [fg : FG]
    {x Q : ℝ} (hx : 1 ≤ x) :
  open Classical in
    summatory (fun q ↦ ∑ χ : DirichletCharacter ℂ q with χ.IsPrimitive,
      q * (q.totient : ℝ)⁻¹ * ⨆ y ∈ Set.Icc 1 x, ‖summatory (fun n ↦ (f * g) n * χ n) y‖) Q =
    summatory (fun q ↦ ∑ χ : DirichletCharacter ℂ q with χ.IsPrimitive,
      q * (q.totient : ℝ)⁻¹ * ⨆ K ∈ Set.Icc 1 ⌊x⌋₊, ‖summatory (fun n ↦ (f * g) n * χ n) (K + 2⁻¹)‖) Q := by
  simp_rw [sup_summatory_eq_sup_nat hx]

section ClaudeFable

/- Everything in this section was generated by Claude Fable 5. It made a couple of changes elsewhere in the file. Where these are significant, I have added a comment. Most significanlty it added a (1+log x) factor to the final theorem, which was introduced by the smoothing argument.

This used ~ 60k input and 640k output tokens. This is ~32 USD at API prices, and it consumed 13% of the weekly usage limit of a 20 USD/month PRO subscription
-/

/-! ### The smoothing kernel: pointwise bounds and the integral `J`

Following Steps 2–4 of `notes/theorem26_6_smooth.md`: the Mellin transform of the smoothed
indicator satisfies `‖𝓜(Smooth1 ν ε)(s)‖ ≤ C/‖s‖` on the strip `0 < Re s ≤ 2` (uniformly in
`ε`), and `‖𝓜(Smooth1 ν ε)(s)‖ ≤ C/(ε ‖s‖²)` (PNT+'s `MellinOfSmooth1b`). Splitting the
vertical integral at height `1/ε` gives `J ≪ 1 + log (1/(σε))`. -/

lemma MellinOfSmooth1_central {ν : ℝ → ℝ} (diffν : ContDiff ℝ 1 ν)
    (suppν : ν.support ⊆ Icc (1 / 2) 2) :
    ∃ C, 0 < C ∧ ∀ {ε : ℝ}, 0 < ε → ε < 1 → ∀ {s : ℂ}, 0 < s.re → s.re ≤ 2 →
      ‖mellin (fun x ↦ (Smooth1 ν ε x : ℂ)) s‖ ≤ C * ‖s‖⁻¹ := by
  obtain ⟨c, hc⟩ := (mellin_bump_bounded (σ₁ := 0) (σ₂ := 2) (by norm_num) diffν
    suppν).isBigOWith
  rw [Asymptotics.IsBigOWith_def] at hc
  simp only [Filter.eventually_principal, Set.mem_setOf_eq, norm_one, mul_one] at hc
  refine ⟨max c 1, by positivity, ?_⟩
  intro ε hε hε1 s hs hs2
  rw [MellinOfSmooth1a diffν suppν hε hs, norm_mul, norm_inv, mul_comm]
  gcongr
  refine le_trans (hc (ε * s) ⟨?_, ?_⟩) (le_max_left _ _)
  · rw [Complex.re_ofReal_mul]
    positivity
  · rw [Complex.re_ofReal_mul]
    nlinarith

open MeasureTheory in
lemma kernel_integral_le {ν : ℝ → ℝ} (diffν : ContDiff ℝ 1 ν) (νpos : ∀ x > 0, 0 ≤ ν x)
    (suppν : ν.support ⊆ Icc (1 / 2) 2) (mass_one : ∫ x in Ioi 0, ν x / x = 1) :
    ∃ C, 0 < C ∧ ∀ {ε σ : ℝ}, 0 < ε → ε < 1 → 0 < σ → σ ≤ 2 → σ * ε ≤ 1 →
      (∫ t : ℝ, ‖mellin (fun x ↦ (Smooth1 ν ε x : ℂ)) (σ + t * I)‖) ≤
        (C * (1 + Real.log ((σ * ε)⁻¹))) := by
  obtain ⟨C₁, hC₁pos, hC₁⟩ := MellinOfSmooth1_central diffν suppν
  obtain ⟨C₂, hC₂pos, hC₂⟩ := MellinOfSmooth1b diffν suppν
  refine ⟨4 * C₁ + 2 * C₂, by positivity, ?_⟩
  intro ε σ hε hε1 hσ hσ2 hσε
  have hσε_pos : 0 < σ * ε := by positivity
  have hL0 : 0 ≤ Real.log ((σ * ε)⁻¹) := by
    apply Real.log_nonneg
    rw [le_inv_comm₀ one_pos hσε_pos, inv_one]
    exact hσε
  set L := Real.log ((σ * ε)⁻¹) with hLdef
  set T := ε⁻¹ with hTdef
  have hT_pos : 0 < T := by positivity
  set K := fun t : ℝ ↦ ‖mellin (fun x ↦ (Smooth1 ν ε x : ℂ)) ((σ : ℂ) + t * I)‖ with hKdef
  have hK_int : Integrable K :=
    (Smooth1_verticalIntegrable diffν νpos suppν mass_one hε hε1 hσ hσ2).norm
  have hre : ∀ t : ℝ, ((σ : ℂ) + t * I).re = σ := fun t ↦ by simp
  have him : ∀ t : ℝ, ((σ : ℂ) + t * I).im = t := fun t ↦ by simp
  -- pointwise central bound
  have hcent : ∀ t : ℝ, K t ≤ 2 * C₁ * (σ + |t|)⁻¹ := by
    intro t
    have h1 : K t ≤ C₁ * ‖(σ : ℂ) + t * I‖⁻¹ :=
      hC₁ hε hε1 (by rw [hre]; exact hσ) (by rw [hre]; exact hσ2)
    have h2 : (σ + |t|) / 2 ≤ ‖(σ : ℂ) + t * I‖ := by
      have hre' := Complex.abs_re_le_norm ((σ : ℂ) + t * I)
      have him' := Complex.abs_im_le_norm ((σ : ℂ) + t * I)
      rw [hre, abs_of_pos hσ] at hre'
      rw [him] at him'
      linarith
    grw [h1]
    rw [show 2 * C₁ * (σ + |t|)⁻¹ = C₁ * ((σ + |t|) / 2)⁻¹ by field_simp]
    gcongr
  -- pointwise tail bound
  have htail : ∀ t : ℝ, K t ≤ C₂ * ε⁻¹ * (σ ^ 2 + t ^ 2)⁻¹ := by
    intro t
    have h1 := hC₂ σ hσ ((σ : ℂ) + t * I) (by rw [hre]) (by rw [hre]; exact hσ2) ε hε hε1
    calc K t ≤ C₂ * (ε * ‖(σ : ℂ) + t * I‖ ^ 2)⁻¹ := h1
      _ = C₂ * ε⁻¹ * (σ ^ 2 + t ^ 2)⁻¹ := by
        rw [Complex.sq_norm, Complex.normSq_add_mul_I, mul_inv]
        ring
  -- integrability of the Cauchy-kernel dominator
  have hg : Integrable (fun t : ℝ ↦ (σ ^ 2 + t ^ 2)⁻¹) := by
    have key : Integrable (fun t : ℝ ↦ (σ ^ 2)⁻¹ * (1 + (σ⁻¹ * t) ^ 2)⁻¹) :=
      (integrable_inv_one_add_sq.comp_mul_left' (inv_ne_zero hσ.ne')).const_mul _
    refine key.congr (Filter.Eventually.of_forall fun t ↦ ?_)
    have h1 : σ ^ 2 + t ^ 2 ≠ 0 := by positivity
    have h2 : (1 : ℝ) + (σ⁻¹ * t) ^ 2 ≠ 0 := by positivity
    field_simp
  -- split the integral at |t| = T
  have hsplit : (∫ t, K t) = (∫ t in Icc (-T) T, K t) + ∫ t in (Icc (-T) T)ᶜ, K t :=
    (integral_add_compl measurableSet_Icc hK_int).symm
  -- the central piece
  have hcont_dom : Continuous fun t : ℝ ↦ 2 * C₁ * (σ + |t|)⁻¹ := by
    apply continuous_const.mul (Continuous.inv₀ (by fun_prop) ?_)
    intro t
    positivity
  have hcent_le : (∫ t in Icc (-T) T, K t) ≤ ∫ t in Icc (-T) T, 2 * C₁ * (σ + |t|)⁻¹ :=
    setIntegral_mono_on hK_int.integrableOn (hcont_dom.integrableOn_Icc)
      measurableSet_Icc (fun t _ ↦ hcent t)
  have habs : ∫ t in (0 : ℝ)..T, (σ + |t|)⁻¹ = Real.log ((σ + T) / σ) := by
    rw [intervalIntegral.integral_congr (g := fun t ↦ (σ + t)⁻¹) ?_]
    · rw [show (fun t : ℝ ↦ (σ + t)⁻¹) = fun t : ℝ ↦ (fun u : ℝ ↦ u⁻¹) (σ + t) from rfl,
        intervalIntegral.integral_comp_add_left (fun u : ℝ ↦ u⁻¹) σ, add_zero,
        integral_inv_of_pos hσ (by linarith)]
    · intro t ht
      rw [Set.uIcc_of_le (by linarith)] at ht
      simp only [abs_of_nonneg ht.1]
  have hcont₀ : Continuous fun t : ℝ ↦ (σ + |t|)⁻¹ := by
    apply Continuous.inv₀ (by fun_prop)
    intro t
    positivity
  -- value of the central piece
  have hcent_val : (∫ t in Icc (-T) T, 2 * C₁ * (σ + |t|)⁻¹) ≤ 4 * C₁ * (1 + L) := by
    rw [MeasureTheory.integral_const_mul]
    have h1 : (∫ t in Icc (-T) T, (σ + |t|)⁻¹) = ∫ t in (-T)..T, (σ + |t|)⁻¹ := by
      rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith)]
    have e1 : ∫ t in (-T)..(0 : ℝ), (σ + |t|)⁻¹ = ∫ t in (0 : ℝ)..T, (σ + |t|)⁻¹ := by
      have h := intervalIntegral.integral_comp_neg (a := (0 : ℝ)) (b := T)
        (f := fun t ↦ (σ + |t|)⁻¹)
      simp only [abs_neg, neg_zero] at h
      rw [← h]
    have h2 : ∫ t in (-T)..T, (σ + |t|)⁻¹ = 2 * Real.log ((σ + T) / σ) := by
      rw [← intervalIntegral.integral_add_adjacent_intervals (a := -T) (b := 0) (c := T)
        (hcont₀.intervalIntegrable _ _) (hcont₀.intervalIntegrable _ _), e1, habs]
      ring
    have hlog : Real.log ((σ + T) / σ) ≤ 1 + L := by
      have hTσ : (σ + T) / σ = 1 + (σ * ε)⁻¹ := by
        rw [hTdef]
        field_simp
      have hinv1 : 1 ≤ (σ * ε)⁻¹ := by
        rw [le_inv_comm₀ one_pos hσε_pos, inv_one]
        exact hσε
      have h3 : Real.log ((σ + T) / σ) ≤ Real.log (2 * (σ * ε)⁻¹) := by
        apply Real.log_le_log (by rw [hTσ]; positivity)
        rw [hTσ]
        linarith
      rw [Real.log_mul (by norm_num) (by positivity)] at h3
      have := Real.log_two_lt_d9
      rw [hLdef]
      linarith
    rw [h1, h2]
    nlinarith
  -- the tail piece
  have hrpow_eq : ∀ t ∈ Ioi T, t ^ ((-2 : ℝ)) = (t ^ 2)⁻¹ := by
    intro t ht
    rw [Real.rpow_neg (hT_pos.trans ht).le, Real.rpow_two]
  have hint_Ioi : IntegrableOn (fun t : ℝ ↦ (t ^ 2)⁻¹) (Ioi T) :=
    (integrableOn_Ioi_rpow_of_lt (a := (-2 : ℝ)) (by norm_num) hT_pos).congr_fun
      (fun t ht ↦ hrpow_eq t ht) measurableSet_Ioi
  have hIoi_val : (∫ t in Ioi T, (t ^ 2)⁻¹) = ε := by
    have h1 : (∫ t in Ioi T, (t ^ 2)⁻¹) = ∫ t in Ioi T, t ^ ((-2 : ℝ)) :=
      MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
        (fun t ht ↦ (hrpow_eq t ht).symm)
    rw [h1, integral_Ioi_rpow_of_lt (by norm_num) hT_pos]
    norm_num [Real.rpow_neg_one, hTdef]
  have hIoi : (∫ t in Ioi T, (σ ^ 2 + t ^ 2)⁻¹) ≤ ε := by
    rw [← hIoi_val]
    apply setIntegral_mono_on hg.integrableOn hint_Ioi measurableSet_Ioi
    intro t ht
    have ht0 : 0 < t := hT_pos.trans ht
    gcongr
    nlinarith
  have hIio : (∫ t in Iio (-T), (σ ^ 2 + t ^ 2)⁻¹) ≤ ε := by
    have h := integral_comp_neg_Iic (-T) (fun t : ℝ ↦ (σ ^ 2 + t ^ 2)⁻¹)
    simp only [neg_sq, neg_neg] at h
    rw [← integral_Iic_eq_integral_Iio, h]
    exact hIoi
  have hcompl : (Icc (-T) T)ᶜ = Iio (-T) ∪ Ioi T := by
    ext u
    simp only [Set.mem_compl_iff, Set.mem_Icc, not_and_or, not_le, Set.mem_union, Set.mem_Iio,
      Set.mem_Ioi]
  have htail_int : (∫ t in (Icc (-T) T)ᶜ, K t) ≤ C₂ * ε⁻¹ * (2 * ε) := by
    calc (∫ t in (Icc (-T) T)ᶜ, K t)
        ≤ ∫ t in (Icc (-T) T)ᶜ, C₂ * ε⁻¹ * (σ ^ 2 + t ^ 2)⁻¹ :=
          setIntegral_mono_on hK_int.integrableOn ((hg.const_mul _).integrableOn)
            measurableSet_Icc.compl (fun t _ ↦ htail t)
      _ = C₂ * ε⁻¹ * ∫ t in (Icc (-T) T)ᶜ, (σ ^ 2 + t ^ 2)⁻¹ :=
          MeasureTheory.integral_const_mul _ _
      _ ≤ C₂ * ε⁻¹ * (2 * ε) := by
          gcongr
          rw [hcompl, setIntegral_union (Iio_disjoint_Ioi_of_le (by linarith))
            measurableSet_Ioi hg.integrableOn hg.integrableOn]
          linarith
  -- combine
  rw [hsplit]
  have hKpos : (0 : ℝ) ≤ ∫ t in Icc (-T) T, K t :=
    setIntegral_nonneg measurableSet_Icc (fun t _ ↦ norm_nonneg _)
  calc (∫ t in Icc (-T) T, K t) + ∫ t in (Icc (-T) T)ᶜ, K t
      ≤ 4 * C₁ * (1 + L) + C₂ * ε⁻¹ * (2 * ε) := by
        grw [hcent_le, hcent_val, htail_int]
    _ = 4 * C₁ * (1 + L) + 2 * C₂ := by
        field_simp
    _ ≤ (4 * C₁ + 2 * C₂) * (1 + L) := by nlinarith

/-! ### Dirichlet polynomials and the large sieve

The inner sums `F_s(χ) = ∑_{m ≤ M} f(m) χ(m) m^{-s}` appearing after Mellin inversion. The large
sieve axiom (Theorem 25.15) bounds their mean square over primitive characters of modulus `≤ Q`.
We use `max C_LS 0` throughout since the axiomatized constant `C_LS` carries no sign
information. -/

/-- The truncated Dirichlet polynomial `∑_{m ≤ X} h(m) χ(m) m^{-s}`. -/
noncomputable def dpoly (h : ℕ → ℂ) (X : ℝ) {q : ℕ} (χ : DirichletCharacter ℂ q) (s : ℂ) : ℂ :=
  summatory (fun m ↦ h m * χ m * (m : ℂ) ^ (-s)) X

theorem norm_dpoly_le {h : ℕ → ℂ} {X : ℝ} {q : ℕ} {χ : DirichletCharacter ℂ q} {s : ℂ}
    (hs : 0 ≤ s.re) : ‖dpoly h X χ s‖ ≤ summatory (fun m ↦ ‖h m‖) X := by
  rw [dpoly, summatory, summatory]
  grw [norm_sum_le]
  apply Finset.sum_le_sum
  intro m hm
  obtain ⟨hm1, -⟩ := (Nat.mem_Icc _ _).mp hm
  have hm0 : 0 < m := by exact_mod_cast lt_of_lt_of_le one_pos hm1
  calc ‖h m * χ m * (m : ℂ) ^ (-s)‖ = ‖h m‖ * ‖χ (m : ZMod q)‖ * ‖(m : ℂ) ^ (-s)‖ := by
        simp
    _ ≤ ‖h m‖ * 1 * 1 := by
        gcongr
        · exact χ.norm_le_one _
        · rw [Complex.norm_natCast_cpow_of_pos hm0]
          exact Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hm1)
            (by simpa using hs)
    _ = ‖h m‖ := by ring

theorem continuous_dpoly_line (h : ℕ → ℂ) (X : ℝ) {q : ℕ} (χ : DirichletCharacter ℂ q) (σ : ℝ) :
    Continuous fun t : ℝ ↦ dpoly h X χ ((σ : ℂ) + t * I) := by
  simp only [dpoly, summatory_apply]
  apply continuous_finset_sum
  intro m hm
  simp only [Finset.mem_Ioc] at hm
  have hm0 : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  exact continuous_const.mul (Continuous.const_cpow (by fun_prop) (Or.inl hm0))

open _root_.Classical in
theorem dpoly_large_sieve (h : ℕ → ℂ) (X : ℝ) {Q : ℝ} (hQ : 1 ≤ Q) {s : ℂ} (hs : 0 ≤ s.re) :
    ∑ q ∈ Finset.Ioc 0 ⌊Q⌋₊, ∑ χ : DirichletCharacter ℂ q with χ.IsPrimitive,
      (q : ℝ) * ((q.totient : ℝ))⁻¹ * ‖dpoly h X χ s‖ ^ 2 ≤
    max C_LS 0 * (X + Q ^ 2) * summatory (fun m ↦ ‖h m‖ ^ 2) X := by
  by_cases hX : 1 ≤ X
  case neg =>
    have hempty : Nat.Icc 1 X = ∅ := Nat.Icc_eq_empty_of_lt _ (by linarith)
    simp [dpoly, summatory, hempty]
  case pos =>
    have hX0 : (0 : ℝ) ≤ X := by linarith
    have hN : 0 < ⌊X⌋₊ := Nat.floor_pos.mpr hX
    set c : ℤ → ℂ := fun n ↦ if 0 < n then h n.toNat * ((n.toNat : ℕ) : ℂ) ^ (-s) else 0
      with hcdef
    have key := large_sieve Q hQ 0 ⌊X⌋₊ hN c
    have reindex : ∀ {R : Type} [AddCommMonoid R] (G : ℤ → R),
        ∑ n ∈ Finset.Ioc (0 : ℤ) (0 + (⌊X⌋₊ : ℤ)), G n =
        ∑ m ∈ Finset.Ioc 0 ⌊X⌋₊, G (m : ℤ) := by
      intro R _ G
      rw [zero_add]
      apply Finset.sum_nbij' (i := fun n : ℤ ↦ n.toNat) (j := fun m : ℕ ↦ (m : ℤ))
      · intro a ha
        simp only [Finset.mem_Ioc] at ha ⊢
        omega
      · intro a ha
        simp only [Finset.mem_Ioc] at ha ⊢
        omega
      · intro a ha
        simp only [Finset.mem_Ioc] at ha
        omega
      · intro a ha
        simp only [Int.toNat_natCast]
      · intro a ha
        simp only [Finset.mem_Ioc] at ha
        rw [Int.toNat_of_nonneg (by omega)]
    have hc_apply : ∀ m ∈ Finset.Ioc 0 ⌊X⌋₊, c (m : ℤ) = h m * (m : ℂ) ^ (-s) := by
      intro m hm
      simp only [Finset.mem_Ioc] at hm
      rw [hcdef]
      simp only [Int.toNat_natCast]
      rw [if_pos (by exact_mod_cast hm.1)]
    have hchar_sum : ∀ {q : ℕ} (χ : DirichletCharacter ℂ q),
        ∑ n ∈ Finset.Ioc (0 : ℤ) (0 + (⌊X⌋₊ : ℤ)), c n * χ n = dpoly h X χ s := by
      intro q χ
      rw [reindex, dpoly, summatory_apply]
      apply Finset.sum_congr rfl
      intro m hm
      rw [hc_apply m hm]
      push_cast
      ring
    have hcoef_sum : ∑ n ∈ Finset.Ioc (0 : ℤ) (0 + (⌊X⌋₊ : ℤ)), ‖c n‖ ^ 2 ≤
        summatory (fun m ↦ ‖h m‖ ^ 2) X := by
      rw [reindex (fun n ↦ ‖c n‖ ^ 2), summatory_apply]
      apply Finset.sum_le_sum
      intro m hm
      rw [hc_apply m hm]
      simp only [Finset.mem_Ioc] at hm
      rw [norm_mul, Complex.norm_natCast_cpow_of_pos hm.1]
      have h1 : (m : ℝ) ^ (-s).re ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hm.1) (by simpa using hs)
      have h2 : (0 : ℝ) ≤ (m : ℝ) ^ (-s).re := Real.rpow_nonneg (by positivity) _
      calc (‖h m‖ * (m : ℝ) ^ (-s).re) ^ 2 = ‖h m‖ ^ 2 * ((m : ℝ) ^ (-s).re) ^ 2 := by ring
        _ ≤ ‖h m‖ ^ 2 * 1 := by gcongr; nlinarith
        _ = ‖h m‖ ^ 2 := mul_one _
    simp only [div_eq_mul_inv] at key
    simp only [hchar_sum] at key
    calc ∑ q ∈ Finset.Ioc 0 ⌊Q⌋₊, ∑ χ : DirichletCharacter ℂ q with χ.IsPrimitive,
        (q : ℝ) * ((q.totient : ℝ))⁻¹ * ‖dpoly h X χ s‖ ^ 2
        ≤ ∑ q ∈ Finset.Ioc 0 ⌊Q⌋₊, ∑ χ : DirichletCharacter ℂ q,
            (q : ℝ) * ((q.totient : ℝ))⁻¹ * ‖dpoly h X χ s‖ ^ 2 := by
          apply Finset.sum_le_sum
          intro q hq
          apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          intro χ _ _
          positivity
      _ ≤ C_LS * ((⌊X⌋₊ : ℝ) + Q ^ 2) *
            ∑ n ∈ Finset.Ioc (0 : ℤ) (0 + (⌊X⌋₊ : ℤ)), ‖c n‖ ^ 2 := key
      _ ≤ max C_LS 0 * ((⌊X⌋₊ : ℝ) + Q ^ 2) *
            ∑ n ∈ Finset.Ioc (0 : ℤ) (0 + (⌊X⌋₊ : ℤ)), ‖c n‖ ^ 2 := by
          have hsum_nonneg : (0 : ℝ) ≤ ∑ n ∈ Finset.Ioc (0 : ℤ) (0 + (⌊X⌋₊ : ℤ)), ‖c n‖ ^ 2 :=
            Finset.sum_nonneg fun _ _ ↦ by positivity
          have hA : (0 : ℝ) ≤ (⌊X⌋₊ : ℝ) + Q ^ 2 := by positivity
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (le_max_left _ _) hA) hsum_nonneg
      _ ≤ max C_LS 0 * (X + Q ^ 2) *
            ∑ n ∈ Finset.Ioc (0 : ℤ) (0 + (⌊X⌋₊ : ℤ)), ‖c n‖ ^ 2 := by
          gcongr
          exact Nat.floor_le hX0
      _ ≤ max C_LS 0 * (X + Q ^ 2) * summatory (fun m ↦ ‖h m‖ ^ 2) X := by
          gcongr

open _root_.Classical in
/-- Cauchy–Schwarz over pairs `(q, χ)` followed by two applications of the large sieve, as in
Step 4 of `notes/theorem26_6_smooth.md`. -/
theorem dpoly_large_sieve_mul [FG] {Q : ℝ} (hQ : 1 ≤ Q) {s : ℂ} (hs : 0 ≤ s.re) :
    ∑ q ∈ Finset.Ioc 0 ⌊Q⌋₊, ∑ χ : DirichletCharacter ℂ q with χ.IsPrimitive,
      (q : ℝ) * ((q.totient : ℝ))⁻¹ * (‖dpoly f M χ s‖ * ‖dpoly g N χ s‖) ≤
    max C_LS 0 * √((M + Q ^ 2) * (N + Q ^ 2)) *
      (√(summatory (fun m ↦ ‖f m‖ ^ 2) M) * √(summatory (fun n ↦ ‖g n‖ ^ 2) N)) := by
  have hM0 : (0 : ℝ) ≤ M := hM_pos.le
  have hN0 : (0 : ℝ) ≤ N := hN_pos.le
  have hA : (0 : ℝ) ≤ summatory (fun m ↦ ‖f m‖ ^ 2) M :=
    summatory_nonneg _ _ (fun n _ ↦ by positivity)
  have hB : (0 : ℝ) ≤ summatory (fun n ↦ ‖g n‖ ^ 2) N :=
    summatory_nonneg _ _ (fun n _ ↦ by positivity)
  set S := (Finset.Ioc 0 ⌊Q⌋₊).sigma
    (fun q ↦ Finset.univ.filter (fun χ : DirichletCharacter ℂ q ↦ χ.IsPrimitive)) with hS
  have key := Finset.sum_sq_le_sum_mul_sum_of_sq_eq_mul S
    (r := fun p ↦ (p.1 : ℝ) * ((p.1.totient : ℝ))⁻¹ * (‖dpoly f M p.2 s‖ * ‖dpoly g N p.2 s‖))
    (f := fun p ↦ (p.1 : ℝ) * ((p.1.totient : ℝ))⁻¹ * ‖dpoly f M p.2 s‖ ^ 2)
    (g := fun p ↦ (p.1 : ℝ) * ((p.1.totient : ℝ))⁻¹ * ‖dpoly g N p.2 s‖ ^ 2)
    (fun p _ ↦ by positivity) (fun p _ ↦ by positivity) (fun p _ ↦ by ring)
  have hf_sum : (∑ p ∈ S, (p.1 : ℝ) * ((p.1.totient : ℝ))⁻¹ * ‖dpoly f M p.2 s‖ ^ 2) ≤
      max C_LS 0 * (M + Q ^ 2) * summatory (fun m ↦ ‖f m‖ ^ 2) M := by
    rw [hS, Finset.sum_sigma]
    exact dpoly_large_sieve f M hQ hs
  have hg_sum : (∑ p ∈ S, (p.1 : ℝ) * ((p.1.totient : ℝ))⁻¹ * ‖dpoly g N p.2 s‖ ^ 2) ≤
      max C_LS 0 * (N + Q ^ 2) * summatory (fun n ↦ ‖g n‖ ^ 2) N := by
    rw [hS, Finset.sum_sigma]
    exact dpoly_large_sieve g N hQ hs
  have hf_nonneg : (0 : ℝ) ≤ ∑ p ∈ S, (p.1 : ℝ) * ((p.1.totient : ℝ))⁻¹ * ‖dpoly f M p.2 s‖ ^ 2 :=
    Finset.sum_nonneg fun p _ ↦ by positivity
  have hg_nonneg : (0 : ℝ) ≤ ∑ p ∈ S, (p.1 : ℝ) * ((p.1.totient : ℝ))⁻¹ * ‖dpoly g N p.2 s‖ ^ 2 :=
    Finset.sum_nonneg fun p _ ↦ by positivity
  calc ∑ q ∈ Finset.Ioc 0 ⌊Q⌋₊, ∑ χ : DirichletCharacter ℂ q with χ.IsPrimitive,
      (q : ℝ) * ((q.totient : ℝ))⁻¹ * (‖dpoly f M χ s‖ * ‖dpoly g N χ s‖)
      = ∑ p ∈ S, (p.1 : ℝ) * ((p.1.totient : ℝ))⁻¹ * (‖dpoly f M p.2 s‖ * ‖dpoly g N p.2 s‖) := by
        rw [hS, Finset.sum_sigma]
    _ ≤ √((∑ p ∈ S, (p.1 : ℝ) * ((p.1.totient : ℝ))⁻¹ * ‖dpoly f M p.2 s‖ ^ 2) *
          ∑ p ∈ S, (p.1 : ℝ) * ((p.1.totient : ℝ))⁻¹ * ‖dpoly g N p.2 s‖ ^ 2) := by
        rw [Real.le_sqrt (Finset.sum_nonneg fun p _ ↦ by positivity)
          (mul_nonneg hf_nonneg hg_nonneg)]
        exact key
    _ ≤ √((max C_LS 0 * (M + Q ^ 2) * summatory (fun m ↦ ‖f m‖ ^ 2) M) *
          (max C_LS 0 * (N + Q ^ 2) * summatory (fun n ↦ ‖g n‖ ^ 2) N)) := by
        apply Real.sqrt_le_sqrt
        exact mul_le_mul hf_sum hg_sum hg_nonneg (by positivity)
    _ = max C_LS 0 * √((M + Q ^ 2) * (N + Q ^ 2)) *
          (√(summatory (fun m ↦ ‖f m‖ ^ 2) M) * √(summatory (fun n ↦ ‖g n‖ ^ 2) N)) := by
        rw [show (max C_LS 0 * (M + Q ^ 2) * summatory (fun m ↦ ‖f m‖ ^ 2) M) *
            (max C_LS 0 * (N + Q ^ 2) * summatory (fun n ↦ ‖g n‖ ^ 2) N) =
            (max C_LS 0) ^ 2 * (((M + Q ^ 2) * (N + Q ^ 2)) *
              (summatory (fun m ↦ ‖f m‖ ^ 2) M * summatory (fun n ↦ ‖g n‖ ^ 2) N)) by ring,
          Real.sqrt_mul (by positivity), Real.sqrt_sq (le_max_right _ _),
          Real.sqrt_mul (by positivity), Real.sqrt_mul hA]
        ring

/-- Trivial uniform bound: since `0 ≤ Smooth1 ν ε ≤ 1` and `‖χ‖ ≤ 1`,
`‖T ε y χ‖ ≤ ‖f‖₁ ‖g‖₁` for every `y > 0`. -/
theorem norm_T_le_const [Bump] [FG] {q : ℕ} {ε : ℝ} (hε_pos : 0 < ε)
    {χ : DirichletCharacter ℂ q} {y : ℝ} (hy : 0 < y) :
    ‖T ε y χ‖ ≤ summatory (fun m ↦ ‖f m‖) M * summatory (fun n ↦ ‖g n‖) N := by
  have hmass : ∫ x in Ioi 0, ν x / x = 1 := by
    rw [← MeasureTheory.integral_Ici_eq_integral_Ioi]
    exact mass_one
  rw [T]
  have hstep : ∀ m ∈ Nat.Icc 1 M,
      ‖summatory (fun n ↦ f m * χ m * g n * χ n * (Smooth1 ν ε (m * n / y) : ℂ)) N‖ ≤
      ‖f m‖ * summatory (fun n ↦ ‖g n‖) N := by
    intro m hm
    obtain ⟨hm1, -⟩ := (Nat.mem_Icc _ _).mp hm
    have hm0 : 0 < m := by exact_mod_cast lt_of_lt_of_le one_pos hm1
    rw [summatory, summatory, Finset.mul_sum]
    grw [norm_sum_le]
    apply Finset.sum_le_sum
    intro n hn
    obtain ⟨hn1, -⟩ := (Nat.mem_Icc _ _).mp hn
    have hn0 : 0 < n := by exact_mod_cast lt_of_lt_of_le one_pos hn1
    have hpos : 0 < (m : ℝ) * n / y := by positivity
    have hS0 : 0 ≤ Smooth1 ν ε ((m : ℝ) * n / y) :=
      Smooth1Nonneg (fun x _ ↦ νpos x) hpos hε_pos
    have hS1 : Smooth1 ν ε ((m : ℝ) * n / y) ≤ 1 :=
      Smooth1LeOne (fun x _ ↦ νpos x) hmass hε_pos hpos
    calc ‖f m * χ m * g n * χ n * (Smooth1 ν ε (m * n / y) : ℂ)‖
        = ‖f m‖ * ‖χ (m : ZMod q)‖ * ‖g n‖ * ‖χ (n : ZMod q)‖ *
          ‖(Smooth1 ν ε (m * n / y) : ℂ)‖ := by simp
      _ ≤ ‖f m‖ * 1 * ‖g n‖ * 1 * 1 := by
          gcongr
          · exact χ.norm_le_one _
          · exact χ.norm_le_one _
          · rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hS0]
            exact hS1
      _ = ‖f m‖ * ‖g n‖ := by ring
  calc ‖summatory (fun m ↦ summatory
        (fun n ↦ f m * χ m * g n * χ n * (Smooth1 ν ε (m * n / y) : ℂ)) N) M‖
      ≤ summatory (fun m ↦ ‖f m‖ * summatory (fun n ↦ ‖g n‖) N) M := by
        rw [summatory, summatory]
        grw [norm_sum_le]
        exact Finset.sum_le_sum hstep
    _ = summatory (fun m ↦ ‖f m‖) M * summatory (fun n ↦ ‖g n‖) N := by
        simp only [summatory]
        rw [← Finset.sum_mul]

/-! ### Bounding `T` by the vertical integral (Step 3) -/

theorem norm_T_le [Bump] [FG] {σ : ℝ} (hσ_pos : 0 < σ) (hσ : σ ≤ 2) {q : ℕ} {ε : ℝ}
    (hε_pos : 0 < ε) (hε_one : ε < 1) {χ : DirichletCharacter ℂ q} {y : ℝ} (hy : 1 ≤ y) :
    ‖T ε y χ‖ ≤ (2 * π)⁻¹ * y ^ σ *
      ∫ t : ℝ, ‖dpoly f M χ ((σ : ℂ) + t * I)‖ * ‖dpoly g N χ ((σ : ℂ) + t * I)‖ *
        ‖mellin (fun x ↦ (Smooth1 ν ε x : ℂ)) ((σ : ℂ) + t * I)‖ := by
  have hy0 : (0 : ℝ) < y := by linarith
  rw [T_eq_integral_sum hσ_pos hσ hε_pos y hy hε_one, norm_smul]
  have hnorm_pt : ∀ t : ℝ,
      ‖summatory (fun m ↦ f m * χ m * (m : ℂ) ^ (-((σ : ℂ) + t * I))) M *
        summatory (fun n ↦ g n * χ n * (n : ℂ) ^ (-((σ : ℂ) + t * I))) N *
        (1 / (y : ℂ)) ^ (-((σ : ℂ) + t * I)) •
          mellin (fun x ↦ (Smooth1 ν ε x : ℂ)) ((σ : ℂ) + t * I)‖
      = y ^ σ * (‖dpoly f M χ ((σ : ℂ) + t * I)‖ * ‖dpoly g N χ ((σ : ℂ) + t * I)‖ *
        ‖mellin (fun x ↦ (Smooth1 ν ε x : ℂ)) ((σ : ℂ) + t * I)‖) := by
    intro t
    have hpow : ‖(1 / (y : ℂ)) ^ (-((σ : ℂ) + t * I))‖ = y ^ σ := by
      rw [show (1 / (y : ℂ)) = ((1 / y : ℝ) : ℂ) by push_cast; ring,
        Complex.norm_cpow_eq_rpow_re_of_pos (by positivity),
        show (-((σ : ℂ) + t * I)).re = -σ by simp, one_div,
        Real.inv_rpow hy0.le, Real.rpow_neg hy0.le, inv_inv]
    rw [norm_mul, norm_mul, norm_smul, hpow, dpoly, dpoly]
    ring
  have hπ : ‖(1 / (2 * π) : ℝ)‖ = (2 * π)⁻¹ := by
    rw [Real.norm_eq_abs, abs_of_pos (by positivity), one_div]
  calc ‖(1 / (2 * π) : ℝ)‖ * ‖∫ t : ℝ,
        summatory (fun m ↦ f m * χ m * (m : ℂ) ^ (-((σ : ℂ) + t * I))) M *
        summatory (fun n ↦ g n * χ n * (n : ℂ) ^ (-((σ : ℂ) + t * I))) N *
        (1 / (y : ℂ)) ^ (-((σ : ℂ) + t * I)) •
          mellin (fun x ↦ (Smooth1 ν ε x : ℂ)) ((σ : ℂ) + t * I)‖
      ≤ ‖(1 / (2 * π) : ℝ)‖ * ∫ t : ℝ,
        ‖summatory (fun m ↦ f m * χ m * (m : ℂ) ^ (-((σ : ℂ) + t * I))) M *
        summatory (fun n ↦ g n * χ n * (n : ℂ) ^ (-((σ : ℂ) + t * I))) N *
        (1 / (y : ℂ)) ^ (-((σ : ℂ) + t * I)) •
          mellin (fun x ↦ (Smooth1 ν ε x : ℂ)) ((σ : ℂ) + t * I)‖ := by
        gcongr
        exact norm_integral_le_integral_norm _
    _ = ‖(1 / (2 * π) : ℝ)‖ * ∫ t : ℝ, y ^ σ *
          (‖dpoly f M χ ((σ : ℂ) + t * I)‖ * ‖dpoly g N χ ((σ : ℂ) + t * I)‖ *
          ‖mellin (fun x ↦ (Smooth1 ν ε x : ℂ)) ((σ : ℂ) + t * I)‖) := by
        rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hnorm_pt)]
    _ = (2 * π)⁻¹ * y ^ σ *
          ∫ t : ℝ, ‖dpoly f M χ ((σ : ℂ) + t * I)‖ * ‖dpoly g N χ ((σ : ℂ) + t * I)‖ *
          ‖mellin (fun x ↦ (Smooth1 ν ε x : ℂ)) ((σ : ℂ) + t * I)‖ := by
        rw [MeasureTheory.integral_const_mul, hπ]
        ring

/-- The integrand `‖F_χ‖ ‖G_χ‖ ‖𝓜(Smooth1 ν ε)‖` of the vertical integral is integrable: the
Dirichlet polynomial factors are continuous and bounded, and the Mellin factor is integrable by
`Smooth1_verticalIntegrable`. -/
theorem integrable_dpoly_mul_mellin [Bump] [FG] {σ : ℝ} (hσ_pos : 0 < σ) (hσ : σ ≤ 2)
    {ε : ℝ} (hε_pos : 0 < ε) (hε_one : ε < 1) {q : ℕ} (χ : DirichletCharacter ℂ q) :
    Integrable (fun t : ℝ ↦ ‖dpoly f M χ ((σ : ℂ) + t * I)‖ *
      ‖dpoly g N χ ((σ : ℂ) + t * I)‖ *
      ‖mellin (fun x ↦ (Smooth1 ν ε x : ℂ)) ((σ : ℂ) + t * I)‖) := by
  have hK : Integrable (fun t : ℝ ↦ ‖mellin (fun x ↦ (Smooth1 ν ε x : ℂ)) ((σ : ℂ) + t * I)‖) :=
    (Smooth1_verticalIntegrable (diffν.of_le (by simp)) (fun x _ ↦ νpos x) suppν
      (by rw [← MeasureTheory.integral_Ici_eq_integral_Ioi]; exact mass_one)
      hε_pos hε_one hσ_pos hσ).norm
  have hre : ∀ t : ℝ, (((σ : ℂ) + t * I)).re = σ := fun t ↦ by simp
  have hcont : Continuous fun t : ℝ ↦ ‖dpoly f M χ ((σ : ℂ) + t * I)‖ *
      ‖dpoly g N χ ((σ : ℂ) + t * I)‖ :=
    ((continuous_dpoly_line f M χ σ).norm).mul ((continuous_dpoly_line g N χ σ).norm)
  apply (hK.bdd_mul (c := summatory (fun m ↦ ‖f m‖) M * summatory (fun n ↦ ‖g n‖) N)
    hcont.aestronglyMeasurable ?_).congr (Filter.Eventually.of_forall fun t ↦ by ring)
  filter_upwards with t
  have h1 : ‖dpoly f M χ ((σ : ℂ) + t * I)‖ ≤ summatory (fun m ↦ ‖f m‖) M :=
    norm_dpoly_le (by rw [hre]; exact hσ_pos.le)
  have h2 : ‖dpoly g N χ ((σ : ℂ) + t * I)‖ ≤ summatory (fun n ↦ ‖g n‖) N :=
    norm_dpoly_le (by rw [hre]; exact hσ_pos.le)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have h3 : (0 : ℝ) ≤ summatory (fun m ↦ ‖f m‖) M :=
    summatory_nonneg _ _ fun n _ ↦ norm_nonneg _
  exact mul_le_mul h1 h2 (norm_nonneg _) h3

open _root_.Classical in
/-- Combining Steps 3 and 4: the weighted sum over moduli `q ≤ Q` and primitive characters of the
sup over `y ≤ x + 1` of `‖T ε y χ‖` is bounded by the large-sieve constant times the kernel
integral `J`. -/
theorem summatory_sup_T_le [Bump] [FG] {ε σ Q x : ℝ} (hε_pos : 0 < ε) (hε_one : ε < 1)
    (hσ_pos : 0 < σ) (hσ2 : σ ≤ 2) (hx : 1 ≤ x) (hQ : 1 ≤ Q) :
    summatory (fun q ↦ ∑ χ : DirichletCharacter ℂ q with χ.IsPrimitive,
      (q : ℝ) * ((q.totient : ℝ))⁻¹ * ⨆ y ∈ Icc 1 (x + 1), ‖T ε y χ‖) Q ≤
    (2 * π)⁻¹ * (x + 1) ^ σ *
      (max C_LS 0 * √((M + Q ^ 2) * (N + Q ^ 2)) *
        (√(summatory (fun m ↦ ‖f m‖ ^ 2) M) * √(summatory (fun n ↦ ‖g n‖ ^ 2) N))) *
      ∫ t : ℝ, ‖mellin (fun x ↦ (Smooth1 ν ε x : ℂ)) ((σ : ℂ) + t * I)‖ := by
  have hre : ∀ t : ℝ, (((σ : ℂ) + t * I)).re = σ := fun t ↦ by simp
  set K : ℝ → ℝ := fun t ↦ ‖mellin (fun x ↦ (Smooth1 ν ε x : ℂ)) ((σ : ℂ) + t * I)‖ with hKdef
  set P : (q : ℕ) → DirichletCharacter ℂ q → ℝ → ℝ := fun q χ t ↦
    ‖dpoly f M χ ((σ : ℂ) + t * I)‖ * ‖dpoly g N χ ((σ : ℂ) + t * I)‖ with hPdef
  set w : ℕ → ℝ := fun q ↦ (q : ℝ) * ((q.totient : ℝ))⁻¹ with hwdef
  set CS : ℝ := max C_LS 0 * √((M + Q ^ 2) * (N + Q ^ 2)) *
    (√(summatory (fun m ↦ ‖f m‖ ^ 2) M) * √(summatory (fun n ↦ ‖g n‖ ^ 2) N)) with hCSdef
  have hK_int : Integrable K :=
    (Smooth1_verticalIntegrable (diffν.of_le (by simp)) (fun x _ ↦ νpos x) suppν
      (by rw [← MeasureTheory.integral_Ici_eq_integral_Ioi]; exact mass_one)
      hε_pos hε_one hσ_pos hσ2).norm
  have hK_nonneg : ∀ t, 0 ≤ K t := fun t ↦ norm_nonneg _
  have hw_nonneg : ∀ q, 0 ≤ w q := fun q ↦ by rw [hwdef]; positivity
  have hPK_int : ∀ (q : ℕ) (χ : DirichletCharacter ℂ q), Integrable (fun t ↦ P q χ t * K t) :=
    fun q χ ↦ integrable_dpoly_mul_mellin hσ_pos hσ2 hε_pos hε_one χ
  have hwPK_int : ∀ (q : ℕ) (χ : DirichletCharacter ℂ q),
      Integrable (fun t ↦ (w q * P q χ t) * K t) := fun q χ ↦
    ((hPK_int q χ).const_mul (w q)).congr (Filter.Eventually.of_forall fun t ↦ by ring)
  -- Step 3: the sup over `y` of `‖T ε y χ‖` is bounded by the `y`-free vertical integral.
  have hsup : ∀ (q : ℕ) (χ : DirichletCharacter ℂ q),
      (⨆ y ∈ Icc 1 (x + 1), ‖T ε y χ‖) ≤
        (2 * π)⁻¹ * (x + 1) ^ σ * ∫ t, P q χ t * K t := by
    intro q χ
    have hb : 0 ≤ (2 * π)⁻¹ * (x + 1) ^ σ * ∫ t, P q χ t * K t := by positivity
    apply Real.iSup_le _ hb
    intro y
    apply Real.iSup_le _ hb
    intro hy
    simp only [mem_Icc] at hy
    calc ‖T ε y χ‖
        ≤ (2 * π)⁻¹ * y ^ σ * ∫ t, P q χ t * K t :=
          norm_T_le hσ_pos hσ2 hε_pos hε_one hy.1
      _ ≤ (2 * π)⁻¹ * (x + 1) ^ σ * ∫ t, P q χ t * K t := by
          gcongr
          · linarith
          · exact hy.2
  -- per-term rearrangement
  have hterm : ∀ (q : ℕ) (χ : DirichletCharacter ℂ q),
      w q * ((2 * π)⁻¹ * (x + 1) ^ σ * ∫ t, P q χ t * K t) =
      (2 * π)⁻¹ * (x + 1) ^ σ * ∫ t, (w q * P q χ t) * K t := by
    intro q χ
    rw [show (fun t ↦ (w q * P q χ t) * K t) = fun t ↦ w q * (P q χ t * K t) by
      funext t; ring, MeasureTheory.integral_const_mul]
    ring
  -- pointwise large sieve bound at height t
  have hpt : ∀ t : ℝ, (∑ q ∈ Finset.Ioc 0 ⌊Q⌋₊, ∑ χ : DirichletCharacter ℂ q with χ.IsPrimitive,
      (w q * P q χ t) * K t) ≤ CS * K t := by
    intro t
    have hLS := dpoly_large_sieve_mul (Q := Q) hQ (s := (σ : ℂ) + t * I)
      (by rw [hre]; exact hσ_pos.le)
    calc ∑ q ∈ Finset.Ioc 0 ⌊Q⌋₊, ∑ χ : DirichletCharacter ℂ q with χ.IsPrimitive,
        (w q * P q χ t) * K t
        = (∑ q ∈ Finset.Ioc 0 ⌊Q⌋₊, ∑ χ : DirichletCharacter ℂ q with χ.IsPrimitive,
            w q * P q χ t) * K t := by
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro q hq
          rw [Finset.sum_mul]
      _ ≤ CS * K t := mul_le_mul_of_nonneg_right hLS (hK_nonneg t)
  -- assemble
  rw [summatory_apply]
  calc ∑ q ∈ Finset.Ioc 0 ⌊Q⌋₊, ∑ χ : DirichletCharacter ℂ q with χ.IsPrimitive,
      w q * ⨆ y ∈ Icc 1 (x + 1), ‖T ε y χ‖
      ≤ ∑ q ∈ Finset.Ioc 0 ⌊Q⌋₊, ∑ χ : DirichletCharacter ℂ q with χ.IsPrimitive,
          (2 * π)⁻¹ * (x + 1) ^ σ * ∫ t, (w q * P q χ t) * K t := by
        apply Finset.sum_le_sum
        intro q hq
        apply Finset.sum_le_sum
        intro χ hχ
        rw [← hterm q χ]
        exact mul_le_mul_of_nonneg_left (hsup q χ) (hw_nonneg q)
    _ = (2 * π)⁻¹ * (x + 1) ^ σ * ∫ t, ∑ q ∈ Finset.Ioc 0 ⌊Q⌋₊,
          ∑ χ : DirichletCharacter ℂ q with χ.IsPrimitive, (w q * P q χ t) * K t := by
        rw [MeasureTheory.integral_finset_sum _ (fun q hq ↦
          integrable_finset_sum _ fun χ hχ ↦ hwPK_int q χ), Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro q hq
        rw [MeasureTheory.integral_finset_sum _ (fun χ hχ ↦ hwPK_int q χ), Finset.mul_sum]
    _ ≤ (2 * π)⁻¹ * (x + 1) ^ σ * ∫ t, CS * K t := by
        apply mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact MeasureTheory.integral_mono (integrable_finset_sum _ fun q hq ↦
          integrable_finset_sum _ fun χ hχ ↦ hwPK_int q χ) (hK_int.const_mul CS) hpt
    _ = (2 * π)⁻¹ * (x + 1) ^ σ * (CS * ∫ t, K t) := by
        rw [MeasureTheory.integral_const_mul]
    _ = (2 * π)⁻¹ * (x + 1) ^ σ * CS * ∫ t, K t := by ring

/-- A canonical bump function, so that statements mentioning `C_LSC` do not need to construct
their own `Bump` instance. Local `[Bump]` hypotheses take precedence over this instance. -/
noncomputable instance Bump.instDefault : Bump where
  ν := SmoothExistence.choose
  diffν := SmoothExistence.choose_spec.1
  νpos := SmoothExistence.choose_spec.2.1
  suppν := SmoothExistence.choose_spec.2.2.1
  mass_one := SmoothExistence.choose_spec.2.2.2

-- set_option maxHeartbeats 1000000 in
#count_heartbeats in
open _root_.Classical in
/-- Theorem 26.6 of Koukoulopoulos, smoothed form (existential version): there is a constant
`C` (depending only on the bump `ν`) such that for `x ≥ 1`, `Q > 0` and the calibrated smoothing
width `ε = ((6 log 2) x)⁻¹`,
$$ \sum_{q \le Q} \sum_{\chi \bmod q}^{*} \frac{q}{\varphi(q)}
   \max_{1 \le y \le x+1} |T_\varepsilon(y,\chi)| \le
   C (\sqrt{MN} + \sqrt{M} Q + \sqrt{N} Q + Q^2)(1 + \log x) \|f\|_2 \|g\|_2 .$$
The proof follows `notes/theorem26_6_smooth.md`: Mellin inversion (`T_eq_integral_sum`),
the choice `σ = 1/\log(x+1)` so that `y^σ ≤ e ≤ 3`, Cauchy–Schwarz plus the large sieve at each
height `t` (`dpoly_large_sieve_mul`), and the kernel integral bound `J ≪ 1 + log x`
(`kernel_integral_le`). -/
theorem summatory_T_ll_exists [Bump] :
    ∃ C, 0 < C ∧ ∀ [FG], ∀ {ε Q x : ℝ}, 0 < Q → 1 ≤ x → ε = (6 * Real.log 2)⁻¹ * x⁻¹ →
      summatory (fun q ↦ ∑ χ : DirichletCharacter ℂ q with χ.IsPrimitive,
        (q : ℝ) * ((q.totient : ℝ))⁻¹ * ⨆ y ∈ Icc 1 (x + 1), ‖T ε y χ‖) Q ≤
      C * (√(N * M) + √M * Q + √N * Q + Q ^ 2) * (1 + Real.log x) *
        √(summatory (fun m ↦ ‖f m‖ ^ 2) M) * √(summatory (fun n ↦ ‖g n‖ ^ 2) N) := by
  obtain ⟨C_J, hC_J_pos, hC_J⟩ := kernel_integral_le (diffν.of_le (by simp))
    (fun x _ ↦ νpos x) suppν
    (by rw [← MeasureTheory.integral_Ici_eq_integral_Ioi]; exact mass_one)
  refine ⟨(2 * π)⁻¹ * 3 * (max C_LS 0 * (C_J * 3)) + 1, by positivity, ?_⟩
  intro fg ε Q x hQ hx hε
  have hx0 : (0 : ℝ) < x := by linarith
  have hlog2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hlog2' : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  have hlog : 0 < Real.log (x + 1) := Real.log_pos (by linarith)
  have hlog_ge : Real.log 2 ≤ Real.log (x + 1) := Real.log_le_log (by norm_num) (by linarith)
  have hlogx : 0 ≤ Real.log x := Real.log_nonneg hx
  have h1logx : (0 : ℝ) ≤ 1 + Real.log x := by linarith
  set σ : ℝ := (Real.log (x + 1))⁻¹ with hσdef
  have hσ_pos : 0 < σ := by positivity
  have hσ2 : σ ≤ 2 := by
    rw [hσdef, inv_le_comm₀ hlog (by norm_num)]
    linarith
  have h6log2 : (0 : ℝ) < 6 * Real.log 2 := by linarith
  have hε_pos : 0 < ε := by
    rw [hε]
    positivity
  have h4x : (4 : ℝ) ≤ 6 * Real.log 2 * x := by
    have h4 : (4 : ℝ) ≤ 6 * Real.log 2 := by linarith
    calc (4 : ℝ) = 4 * 1 := by norm_num
      _ ≤ 6 * Real.log 2 * x := mul_le_mul h4 hx (by norm_num) (by linarith)
  have hprod_pos : 0 < Real.log (x + 1) * (6 * Real.log 2 * x) :=
    mul_pos hlog (mul_pos h6log2 hx0)
  have hprod : 1 ≤ Real.log (x + 1) * (6 * Real.log 2 * x) := by
    have h2x : (1 / 2 : ℝ) ≤ Real.log (x + 1) := by linarith
    have := mul_le_mul h2x h4x (by norm_num) hlog.le
    linarith
  have hε1 : ε < 1 := by
    rw [hε, ← mul_inv, inv_lt_one₀ (by nlinarith)]
    nlinarith
  have hinv_eq : (Real.log (x + 1))⁻¹ * ((6 * Real.log 2)⁻¹ * x⁻¹) =
      (Real.log (x + 1) * (6 * Real.log 2 * x))⁻¹ := by
    rw [mul_inv (Real.log (x + 1)) (6 * Real.log 2 * x), mul_inv (6 * Real.log 2) x]
  have hσε : σ * ε ≤ 1 := by
    rw [hε, hσdef, hinv_eq, inv_le_one₀ hprod_pos]
    exact hprod
  by_cases hQ1 : 1 ≤ Q
  case neg =>
    rw [summatory, Nat.Icc_eq_empty_of_lt _ (by linarith), Finset.sum_empty]
    positivity
  case pos =>
    have hM0 : (0 : ℝ) ≤ M := hM_pos.le
    have hN0 : (0 : ℝ) ≤ N := hN_pos.le
    have hQ0 : (0 : ℝ) ≤ Q := hQ.le
    have hB' : 0 ≤ √(N * M) + √M * Q + √N * Q + Q ^ 2 := by positivity
    -- `(x+1)^σ = e ≤ 3`
    have hxσ : (x + 1) ^ σ ≤ 3 := by
      rw [Real.rpow_def_of_pos (by linarith), hσdef, mul_inv_cancel₀ hlog.ne']
      linarith [Real.exp_one_lt_d9]
    -- `√((M+Q²)(N+Q²)) ≤ √(NM) + √M Q + √N Q + Q²`
    have hsqrt : √((M + Q ^ 2) * (N + Q ^ 2)) ≤ √(N * M) + √M * Q + √N * Q + Q ^ 2 := by
      have hnm : √(N * M) = √N * √M := Real.sqrt_mul hN0 M
      have hkey : (M + Q ^ 2) * (N + Q ^ 2) ≤ (√(N * M) + √M * Q + √N * Q + Q ^ 2) ^ 2 := by
        have h {M : ℝ} (hM : 0 ≤ M) : (M + Q^2) ≤ (√M + Q)^2 := by
          conv_lhs => rw [← Real.sq_sqrt hM]
          nlinarith only [hQ0, Real.sqrt_nonneg M]
        grw [h hM0, h hN0, hnm]
        apply le_of_eq
        ring
      grw [hkey, Real.sqrt_sq hB']
    -- the kernel integral is `≪ 1 + log x`
    have hJ : (∫ t : ℝ, ‖mellin (fun x ↦ (Smooth1 ν ε x : ℂ)) ((σ : ℂ) + t * I)‖) ≤
        C_J * (3 * (1 + Real.log x)) := by
      have h1 : (σ * ε)⁻¹ = Real.log (x + 1) * (6 * Real.log 2 * x) := by
        rw [hε, hσdef, hinv_eq, inv_inv]
      have h2 : Real.log ((σ * ε)⁻¹) =
          Real.log (Real.log (x + 1)) + (Real.log (6 * Real.log 2) + Real.log x) := by
        rw [h1, Real.log_mul hlog.ne' (mul_pos h6log2 hx0).ne',
          Real.log_mul h6log2.ne' hx0.ne']
      have h3 : Real.log (Real.log (x + 1)) ≤ Real.log x := by
        apply Real.log_le_log hlog
        linarith [Real.log_le_sub_one_of_pos (show (0 : ℝ) < x + 1 by linarith)]
      have h4 : Real.log (6 * Real.log 2) ≤ 2 := by
        have hexp2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
          rw [← Real.exp_add]; norm_num
        have h6 : (6 : ℝ) * Real.log 2 ≤ Real.exp 2 := by
          nlinarith [Real.exp_one_gt_d9]
        calc Real.log (6 * Real.log 2) ≤ Real.log (Real.exp 2) := Real.log_le_log h6log2 h6
          _ = 2 := Real.log_exp 2
      calc (∫ t : ℝ, ‖mellin (fun x ↦ (Smooth1 ν ε x : ℂ)) ((σ : ℂ) + t * I)‖)
          ≤ C_J * (1 + Real.log ((σ * ε)⁻¹)) := hC_J hε_pos hε1 hσ_pos hσ2 hσε
        _ ≤ C_J * (3 * (1 + Real.log x)) := by
            apply mul_le_mul_of_nonneg_left _ hC_J_pos.le
            rw [h2]
            linarith
    calc summatory (fun q ↦ ∑ χ : DirichletCharacter ℂ q with χ.IsPrimitive,
        (q : ℝ) * ((q.totient : ℝ))⁻¹ * ⨆ y ∈ Icc 1 (x + 1), ‖T ε y χ‖) Q
        ≤ (2 * π)⁻¹ * (x + 1) ^ σ *
            (max C_LS 0 * √((M + Q ^ 2) * (N + Q ^ 2)) *
              (√(summatory (fun m ↦ ‖f m‖ ^ 2) M) * √(summatory (fun n ↦ ‖g n‖ ^ 2) N))) *
            ∫ t : ℝ, ‖mellin (fun x ↦ (Smooth1 ν ε x : ℂ)) ((σ : ℂ) + t * I)‖ :=
          summatory_sup_T_le hε_pos hε1 hσ_pos hσ2 hx hQ1
      _ ≤ (2 * π)⁻¹ * 3 *
            (max C_LS 0 * (√(N * M) + √M * Q + √N * Q + Q ^ 2) *
              (√(summatory (fun m ↦ ‖f m‖ ^ 2) M) * √(summatory (fun n ↦ ‖g n‖ ^ 2) N))) *
            (C_J * (3 * (1 + Real.log x))) := by
          gcongr
      _ = ((2 * π)⁻¹ * 3 * (max C_LS 0 * (C_J * 3))) *
            (√(N * M) + √M * Q + √N * Q + Q ^ 2) * (1 + Real.log x) *
            √(summatory (fun m ↦ ‖f m‖ ^ 2) M) * √(summatory (fun n ↦ ‖g n‖ ^ 2) N) := by
          ring
      _ ≤ ((2 * π)⁻¹ * 3 * (max C_LS 0 * (C_J * 3)) + 1) *
            (√(N * M) + √M * Q + √N * Q + Q ^ 2) * (1 + Real.log x) *
            √(summatory (fun m ↦ ‖f m‖ ^ 2) M) * √(summatory (fun n ↦ ‖g n‖ ^ 2) N) := by
          gcongr
          linarith

/-- The implied constant in the smoothed Theorem 26.6; depends only on the bump `ν`. -/
noncomputable def C_LSC [Bump] : ℝ := summatory_T_ll_exists.choose

theorem C_LSC_pos [Bump] : 0 < C_LSC := summatory_T_ll_exists.choose_spec.1

end ClaudeFable

open _root_.Classical in
theorem summatory_T_ll [Bump] [FG] {ε Q : ℝ} (hQ : 0 < Q) {x : ℝ} (hx : 1 ≤ x)
    (hε : ε = (6 * Real.log 2)⁻¹ * x⁻¹) :
    summatory (fun q => ∑ χ : DirichletCharacter ℂ q with χ.IsPrimitive,
      ↑q * (↑q.totient)⁻¹ * ⨆ y ∈ Icc 1 (x+1), ‖T ε y χ‖) Q ≤
    C_LSC * (√(N * M) + √M * Q + √N * Q + Q ^ 2) * (1 + Real.log x) *
      √(summatory (fun m => ‖f m‖ ^ 2) M) * √(summatory (fun n => ‖g n‖ ^ 2) N) :=
  summatory_T_ll_exists.choose_spec.2 hQ hx hε

open _root_.Classical in
theorem summatory_T_ll_nat [Bump] [FG] {ε Q : ℝ} (hQ : 0 < Q) {x : ℝ} (hx : 1 ≤ x)
    (hε : ε = (6 * Real.log 2)⁻¹ * x⁻¹) :
    summatory (fun q => ∑ χ : DirichletCharacter ℂ q with χ.IsPrimitive, ↑q * (↑q.totient)⁻¹ * ⨆ K ∈ Icc 1 ⌊x⌋₊, ‖T ε (↑K + 2⁻¹) χ‖) Q ≤ C_LSC *
    (√(N * M) + √M * Q + √N * Q + Q ^ 2) * (1 + Real.log x) *
    √(summatory (fun m => ‖f m‖ ^ 2) M) * √(summatory (fun n => ‖g n‖ ^ 2) N) := by
  trans summatory (fun q => ∑ χ : DirichletCharacter ℂ q with χ.IsPrimitive, ↑q * (↑q.totient)⁻¹ * ⨆ y ∈ Icc 1 (x+1), ‖T ε y χ‖) Q
  · gcongr with q hq hqQ χ hχ
    apply Real.iSup_le _ (by positivity)
    intro K
    apply le_ciSup_of_le (c := K + (2⁻¹ : ℝ))
    · --TODO: This subproof was written by Claude. I would like to avoid having it in the first place.
      refine ⟨summatory (fun m ↦ ‖f m‖) M * summatory (fun n ↦ ‖g n‖) N, ?_⟩
      rintro v ⟨y, rfl⟩
      have hB0 : 0 ≤ summatory (fun m ↦ ‖f m‖) M * summatory (fun n ↦ ‖g n‖) N :=
        mul_nonneg (summatory_nonneg _ _ fun n _ ↦ norm_nonneg _)
          (summatory_nonneg _ _ fun n _ ↦ norm_nonneg _)
      apply Real.iSup_le _ hB0
      intro hy
      simp only [mem_Icc] at hy
      have hε_pos : 0 < ε := by
        rw [hε]
        positivity
      exact norm_T_le_const hε_pos (by linarith [hy.1])
    by_cases h : K ∈ Icc 1 ⌊x⌋₊
    · have h' : K + (2 : ℝ)⁻¹ ∈ Icc 1 (x+1) := by
        simp only [mem_Icc] at h ⊢
        have : (1 : ℝ) ≤ K := by
          exact_mod_cast h.1
        have : (K : ℝ) ≤ x := by
          grw [h.2]
          apply Nat.floor_le
          grind
        grind
      simp only [h, h', ciSup_unique]
      rfl
    · simp only [h, iSup_of_isEmpty, mem_Icc]
      positivity
  apply summatory_T_ll hQ hx hε

theorem Nat.le_of_le_add_real {m n : ℕ} {x : ℝ} (hx_nonneg : 0 ≤ x) (hx : x < 1) (h : m ≤ n + x) : m ≤ n := by
  apply_fun Nat.floor (α := ℝ) at h
  · simp only [Nat.floor_natCast] at h
    rw [add_comm, Nat.floor_add_natCast, Nat.floor_eq_zero.mpr] at h
    · simpa using h
    · exact hx
    · exact hx_nonneg
  exact Nat.floor_mono

theorem Nat.le_of_add_real_le {m n : ℕ} {x : ℝ} (hx_pos : 0 < x) (hx : x ≤ 1) (h : m + x ≤ n) : m + 1 ≤ n := by
  have : Nat.ceil x = 1 := by
    rw [Nat.ceil_eq_iff]
    · simp [hx_pos, hx]
    · norm_num
  apply_fun Nat.ceil (α := ℝ) at h
  · simp only [Nat.ceil_natCast] at h
    rw [add_comm, Nat.ceil_add_natCast] at h
    · rw [this, add_comm] at h
      apply h
    · exact hx_pos.le
  exact Nat.ceil_mono


theorem T_eq_sharp {x : ℝ} (hx : 1 ≤ x) [Bump] [FG] {q : ℕ} {ε : ℝ} (hε_pos : 0 < ε) {χ : DirichletCharacter ℂ q} (K : ℕ) (hK : K ≤ x) (hε : ε ≤ (6 * Real.log 2)⁻¹ * x⁻¹) :
  Flat.T ε (K + 2⁻¹) χ =
    summatory (fun m ↦ summatory (fun n ↦ if m * n ≤ (K + 2⁻¹ : ℝ) then f m * χ m * g n * χ n else 0) N) M := by
  rw [T]
  congr! 2 with m hm hmM n hn hnN
  -- Interesting! `obtain` doesn't work here because of the ?A
  have ⟨_, _, rfl, h_below⟩ := Smooth1Properties_below suppν ?A
  case A =>
    rw [← MeasureTheory.integral_Ici_eq_integral_Ioi]
    apply mass_one
  have ⟨_, _, rfl, h_above⟩ := Smooth1Properties_above suppν
  split_ifs with h
  · rw [h_below]
    · simp
    · exact hε_pos
    · positivity
    · have : (m : ℝ) * n ≤ K := by
        norm_cast at h ⊢
        apply Nat.le_of_le_add_real (by norm_num) (by norm_num) h
      grw [hε, this]
      have : 0 < x + 1 := by linarith
      field_simp
      linarith
  · grw [h_above]
    · simp
    · simp [hε_pos]
      grw [hε]
      field_simp
      have := Real.log_two_gt_d9
      nlinarith
    · push Not at h
      grw [hε]
      have : (K : ℝ) + 1 ≤ m * n := by
        norm_cast at h ⊢
        apply Nat.le_of_add_real_le (by norm_num) (by norm_num) h.le
      grw [mul_assoc, ← this]
      field_simp
      nlinarith

theorem FG.summatory_mul [fg : FG] {y : ℝ} :
    summatory (fun n ↦ (f * g) n) y =
    summatory (fun m ↦ summatory (fun n ↦ if m * n ≤ y then f m * g n else 0) N) M := by
  by_cases hy : y ≤ 0
  · rw [summatory_of_nonpos hy, eq_comm]
    apply summatory_eq_zero
    intro m hm_pos hm
    apply summatory_eq_zero
    intro n hn_pos hn
    rw [if_neg]
    have : 0 < (m * n : ℝ) := by positivity
    grind
  replace hy : 0 < y := by grind
  rw [summatory_apply, ArithmeticFunction.sum_Ioc_mul_eq_sum_sum]
  simp_rw [Finset.mul_sum, summatory_apply]
  -- What follows is Claude's doing.
  replace hy : (0:ℝ) ≤ y := hy.le
  set K : ℕ := ⌊y⌋₊ + ⌊M⌋₊ + ⌊N⌋₊ with hKdef
  have key : ∀ m n : ℕ, 0 < m → ((↑m * ↑n : ℝ) ≤ y ↔ n ≤ ⌊y⌋₊ / m) := by
    intro m n hm
    rw [Nat.le_div_iff_mul_le hm, ← Nat.cast_mul, ← Nat.le_floor_iff hy, Nat.mul_comm]
  calc ∑ m ∈ Finset.Ioc 0 ⌊y⌋₊, ∑ n ∈ Finset.Ioc 0 (⌊y⌋₊ / m), f m * g n
      = ∑ m ∈ Finset.Ioc 0 ⌊y⌋₊, ∑ n ∈ Finset.Ioc 0 K,
          if (↑m * ↑n : ℝ) ≤ y then f m * g n else 0 := by
        refine Finset.sum_congr rfl fun m hm => ?_
        obtain ⟨hm0, -⟩ := Finset.mem_Ioc.mp hm
        rw [Finset.sum_congr rfl fun n hn =>
              (if_pos ((key m n hm0).mpr (Finset.mem_Ioc.mp hn).2)).symm]
        refine Finset.sum_subset (Finset.Ioc_subset_Ioc le_rfl
          (le_trans (Nat.div_le_self _ _) (by omega))) fun n hn hn' => ?_
        simp only [Finset.mem_Ioc] at hn hn'
        exact if_neg fun h => hn' ⟨hn.1, (key m n hm0).mp h⟩
    _ = ∑ m ∈ Finset.Ioc 0 K, ∑ n ∈ Finset.Ioc 0 K,
          if (↑m * ↑n : ℝ) ≤ y then f m * g n else 0 := by
        refine Finset.sum_subset (Finset.Ioc_subset_Ioc le_rfl (by omega)) fun m hm hm' => ?_
        simp only [Finset.mem_Ioc] at hm hm'
        refine Finset.sum_eq_zero fun n hn => ?_
        simp only [Finset.mem_Ioc] at hn
        refine if_neg fun h => ?_
        have := (key m n hm.1).mp h
        have : ⌊y⌋₊ / m = 0 := Nat.div_eq_of_lt (by omega)
        omega
    _ = ∑ m ∈ Finset.Ioc 0 ⌊M⌋₊, ∑ n ∈ Finset.Ioc 0 K,
          if (↑m * ↑n : ℝ) ≤ y then f m * g n else 0 := by
        refine .symm <| Finset.sum_subset (Finset.Ioc_subset_Ioc le_rfl (by omega))
          fun m hm hm' => ?_
        simp only [Finset.mem_Ioc] at hm hm'
        refine Finset.sum_eq_zero fun n _ => ?_
        rw [hf m ((Nat.floor_lt hM_pos.le).mp (by omega))]; simp
    _ = ∑ m ∈ Finset.Ioc 0 ⌊M⌋₊, ∑ n ∈ Finset.Ioc 0 ⌊N⌋₊,
          if (↑m * ↑n : ℝ) ≤ y then f m * g n else 0 := by
        refine Finset.sum_congr rfl fun m _ => .symm <|
          Finset.sum_subset (Finset.Ioc_subset_Ioc le_rfl (by omega)) fun n hn hn' => ?_
        simp only [Finset.mem_Ioc] at hn hn'
        rw [hg n ((Nat.floor_lt hN_pos.le).mp (by omega))]; simp


theorem FG.summatory_mul_char [fg : FG] {q : ℕ} {χ : DirichletCharacter ℂ q} {y : ℝ} : summatory (fun n ↦ (f * g) n * χ n) y =
    summatory (fun m ↦ summatory (fun n ↦ if m * n ≤ y then f m * χ m * g n * χ n else 0) N) M := by
  let inst : FG := {
    M, hM_pos, N, hN_pos,
    f := f.twist χ,
    g := g.twist χ
    hf := by simp +contextual [hf]
    hg := by simp +contextual [hg]
    }
  have := inst.summatory_mul (y := y)
  simp only [ twist_apply, Algebra.algebraMap_self, RingHom.id_apply, inst, ← mul_assoc] at this
  rw [← this]
  simp [Finset.sum_mul]
  congr! 2 with n hn_pos hny ⟨a, b⟩ hab
  simp only [Nat.mem_divisorsAntidiagonal, ne_eq] at hab
  simp [← hab.1]
  ring

theorem LargeSieve_convolution [fg : FG]
    {x Q : ℝ} (hx : 1 ≤ x) (hQ : 1 ≤ Q) :
  open Classical in
    summatory (fun q ↦ ∑ χ : DirichletCharacter ℂ q with χ.IsPrimitive,
      q * (q.totient : ℝ)⁻¹ * ⨆ y ∈ Set.Icc 1 x, ‖summatory (fun n ↦ (f * g) n * χ n) y‖) Q
      ≤ C_LSC * (√(N * M) + √M * Q + √N * Q + Q^2) * (1 + Real.log x) *
      √(summatory (fun m ↦ ‖f m‖^2) M) * √(summatory (fun n ↦ ‖g n‖^2) N) := by
  classical
  let ε := (6 * Real.log 2)⁻¹ * x⁻¹
  simp_rw [temp hx, FG.summatory_mul_char]
  calc
    _ = summatory (fun q ↦ ∑ χ : DirichletCharacter ℂ q with χ.IsPrimitive,
        q * (q.totient : ℝ)⁻¹ * ⨆ K ∈ Set.Icc 1 ⌊x⌋₊, ‖T ε (K + 2⁻¹) χ‖) Q := by
      congr! with q hq_pos hQ χ hχ K hK
      simp only [mem_Icc] at hK
      rw [Flat.T_eq_sharp _ _ _ le_rfl]
      rw [Nat.le_floor_iff] at hK
      · simp_rw [ε]
        grw [hK.2]
        norm_cast
        grind
      · linarith
      · exact_mod_cast hK.1
      · positivity
    _ ≤ _ := summatory_T_ll_nat (by linarith) hx rfl

end Flat
