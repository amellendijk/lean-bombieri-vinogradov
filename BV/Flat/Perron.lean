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
def evalRealiSup : PositivityExt where eval {u α} zα pα? e :=
  match pα? with | none => pure .none | some pα => do
  match u, α, e with
  | 0, ~q(ℝ), ~q(@iSup ℝ $ι $instSup $f) =>
    let i : Q($ι) ← mkFreshExprMVarQ q($ι) .syntheticOpaque
    have body : Q(ℝ) := .betaRev f #[i]
    let rbody ← core zα pα body
    let some pbody := rbody.toNonneg | return .none
    let pr : Q(∀ i, 0 ≤ $f i) ← mkLambdaFVars #[i] pbody
    assertInstancesCommute
    return .nonnegative q(Real.iSup_nonneg $pr)
  | _, _, _ => throwError "not a real-valued iSup"

end Mathlib.Meta.Positivity


-- The existing `fun_prop` rule for constant complex powers requires a `NeZero`
-- instance. This version also lets its discharger use nonvanishing hypotheses.
attribute [fun_prop] Continuous.const_cpow

/-- A finite summatory function is continuous in a parameter when its terms are. -/
@[fun_prop]
lemma continuous_summatory {α E : Type*} [TopologicalSpace α] [AddCommMonoid E]
    [TopologicalSpace E] [ContinuousAdd E] {F : ℕ → α → E} {x : ℝ}
    (hF : ∀ n ∈ Finset.Ioc 0 ⌊x⌋₊, Continuous (F n)) :
    Continuous (fun t ↦ summatory (fun n ↦ F n t) x) :=
  continuous_finsetSum _ hF

/-- Integration commutes with a finite summatory function. -/
lemma integral_summatory {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    [NormedSpace ℝ E] {μ : MeasureTheory.Measure α} {F : ℕ → α → E} {x : ℝ}
    (hF : ∀ n ∈ Finset.Ioc 0 ⌊x⌋₊, MeasureTheory.Integrable (F n) μ) :
    ∫ t, summatory (fun n ↦ F n t) x ∂μ = summatory (fun n ↦ ∫ t, F n t ∂μ) x :=
  MeasureTheory.integral_finsetSum _ hF

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

lemma Bump.mass_one_Ioi [Bump] : ∫ x in Ioi 0, ν x / x = 1 := by
  rw [← integral_Ici_eq_integral_Ioi, mass_one]

/-- The smoothed cutoff has an integrable Mellin transform on each relevant vertical line. -/
lemma Bump.verticalIntegrable [Bump] {ε σ : ℝ} (hε : 0 < ε) (hε1 : ε < 1)
    (hσ : 0 < σ) (hσ2 : σ ≤ 2) :
    Integrable (fun t : ℝ ↦ mellin (fun x ↦ (Smooth1 ν ε x : ℂ)) (σ + t * I)) :=
  Smooth1_verticalIntegrable (diffν.of_le (by simp)) (fun x _ ↦ νpos x) suppν
    Bump.mass_one_Ioi hε hε1 hσ hσ2

lemma Bump.norm_smooth1_le_one [Bump] {ε x : ℝ} (hε : 0 < ε) (hx : 0 < x) :
    ‖(Smooth1 ν ε x : ℂ)‖ ≤ 1 := by
  rw [Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Smooth1Nonneg (fun x _ ↦ νpos x) hx hε)]
  exact Smooth1LeOne (fun x _ ↦ νpos x) Bump.mass_one_Ioi hε hx

/-- A positive real base has constant norm along a vertical line of exponents. -/
lemma norm_cpow_neg_vertical {r : ℝ} (hr : 0 < r) (σ t : ℝ) :
    ‖(r : ℂ) ^ (-(σ + t * I))‖ = r ^ (-σ) := by
  simp [Complex.norm_cpow_eq_rpow_re_of_pos hr]

lemma norm_one_div_cpow_neg_vertical {y : ℝ} (hy : 0 < y) (σ t : ℝ) :
    ‖(1 / (y : ℂ)) ^ (-(σ + t * I))‖ = y ^ σ := by
  rw [show (1 / (y : ℂ)) = ((1 / y : ℝ) : ℂ) by simp,
    norm_cpow_neg_vertical (by positivity), one_div, Real.inv_rpow hy.le,
    ← Real.rpow_neg hy.le, neg_neg]

/-- A Dirichlet polynomial is continuous on a vertical line. -/
@[fun_prop]
lemma continuous_dirichletSum (c : ℕ → ℂ) (σ P : ℝ) :
    Continuous (fun t : ℝ ↦ summatory (fun m ↦ c m * (m : ℂ) ^ (-(σ + t * I))) P) := by
  apply continuous_summatory
  intro m hm
  have hm0 : (m : ℂ) ≠ 0 := by exact_mod_cast (Finset.mem_Ioc.mp hm).1.ne'
  fun_prop (disch := simp_all)

/-- The weighted ℓ¹ mass bounds a Dirichlet polynomial uniformly on a vertical line. -/
lemma norm_dirichletSum_le (c : ℕ → ℂ) (σ P t : ℝ) :
    ‖summatory (fun m ↦ c m * (m : ℂ) ^ (-(σ + t * I))) P‖ ≤
      summatory (fun m ↦ ‖c m‖ * (m : ℝ) ^ (-σ)) P := by
  refine (_root_.norm_summatory_le _ _).trans (summatory_le_summatory fun m hm _ ↦ ?_)
  rw [norm_mul, Complex.norm_natCast_cpow_of_pos hm]
  simp

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



/-- Each term of the Mellin representation is integrable: its prefactor has constant norm. -/
theorem integrable_term {σ : ℝ} (hσ_pos : 0 < σ) (hσ : σ ≤ 2)
    [Bump] [FG] {q : ℕ} {ε : ℝ} (hε_pos : 0 < ε) (hε_one : ε < 1)
    {χ : DirichletCharacter ℂ q} {y : ℝ} (hy : 1 ≤ y) (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :
    Integrable (fun t : ℝ =>
      f m * χ ↑m * (m : ℂ) ^ (-((σ : ℂ) + ↑t * I)) *
        (g n * χ ↑n * (n : ℂ) ^ (-((σ : ℂ) + ↑t * I))) *
        (1 / (y : ℂ)) ^ (-((σ : ℂ) + ↑t * I)) •
        mellin (fun x => (↑(Smooth1 ν ε x) : ℂ)) ((σ : ℂ) + ↑t * I)) := by
  have hm0 : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have hy0 : (y : ℂ) ≠ 0 := by exact_mod_cast (show 0 < y by positivity).ne'
  have hcont : Continuous (fun t : ℝ ↦
      f m * χ m * (m : ℂ) ^ (-(σ + t * I)) *
        (g n * χ n * (n : ℂ) ^ (-(σ + t * I))) *
        (1 / (y : ℂ)) ^ (-(σ + t * I))) := by
    fun_prop (disch := simp_all)
  simp only [smul_eq_mul, ← mul_assoc] at hcont ⊢
  refine (Bump.verticalIntegrable hε_pos hε_one hσ_pos hσ).bdd_mul
    hcont.aestronglyMeasurable (c := ‖f m * χ m‖ * (m : ℝ) ^ (-σ) *
      (‖g n * χ n‖ * (n : ℝ) ^ (-σ)) * y ^ σ) ?_
  filter_upwards with t
  simp only [norm_mul]
  rw [Complex.norm_natCast_cpow_of_pos hm, Complex.norm_natCast_cpow_of_pos hn,
    norm_one_div_cpow_neg_vertical (by positivity)]
  simp [mul_assoc]


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
  rw [MeasureTheory.integral_finsetSum, Finset.smul_sum, Finset.sum_comm]
  congr! with n hn
  rw [MeasureTheory.integral_finsetSum, Finset.smul_sum]
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
    refine integrable_finsetSum _ fun m hm => ?_
    exact integrable_term hσ_pos hσ hε_pos hε_one hy m i
      (Finset.mem_Ioc.mp hm).1 (Finset.mem_Ioc.mp hi).1

/-- A `range`-of-bounded-supremum function `z ↦ ⨆ (_ : z ∈ S), φ z` (with `φ` real-valued) is
bounded above as soon as `φ` is bounded by some nonnegative `B` on `S`: off `S` the inner
supremum is `0`, and on `S` it equals `φ z ≤ B`. This is the common engine behind the three
`BddAbove` side-goals produced by `le_ciSup`/`le_ciSup_of_le`. -/
private lemma bddAbove_range_biSup {α : Type*} {φ : α → ℝ} {S : Set α} {B : ℝ}
    (hB : 0 ≤ B) (hbound : ∀ z ∈ S, φ z ≤ B) :
    BddAbove (Set.range fun z => ⨆ (_ : z ∈ S), φ z) := by
  refine ⟨B, ?_⟩
  rintro _ ⟨z, rfl⟩
  exact Real.iSup_le (fun hz => hbound z hz) hB

/-- `‖summatory f z‖` is bounded by the total `ℓ¹` mass `summatory ‖f·‖ x` whenever `⌊z⌋₊ ≤ ⌊x⌋₊`:
the summatory is a sum over `Ioc 0 ⌊z⌋₊ ⊆ Ioc 0 ⌊x⌋₊` of terms whose norms are nonnegative. -/
private lemma norm_summatory_le {f : ℕ → ℂ} {z x : ℝ} (h : ⌊z⌋₊ ≤ ⌊x⌋₊) :
    ‖summatory f z‖ ≤ summatory (fun m => ‖f m‖) x := by
  rw [summatory_apply, summatory_apply]
  exact (norm_sum_le _ _).trans
    (Finset.sum_le_sum_of_subset_of_nonneg (Finset.Ioc_subset_Ioc le_rfl h)
      (fun i _ _ => norm_nonneg _))

/-- A uniform (in `y ≥ 1`) bound on `‖T ε y χ‖`: each summand carries a factor
`Smooth1 ν ε (mn/y) ∈ [0,1]`, so the double sum is dominated by the `y`-independent quantity
`∑_{m≤M} ∑_{n≤N} ‖f m‖‖χ m‖‖g n‖‖χ n‖`. -/
private lemma norm_T_le [Bump] [FG] {q : ℕ} {ε : ℝ} (hε_pos : 0 < ε)
    {χ : DirichletCharacter ℂ q} {y : ℝ} (hy : 1 ≤ y) :
    ‖T ε y χ‖ ≤ ∑ m ∈ Finset.Ioc 0 ⌊M⌋₊, ∑ n ∈ Finset.Ioc 0 ⌊N⌋₊,
      ‖f m‖ * ‖χ (m : ZMod q)‖ * ‖g n‖ * ‖χ (n : ZMod q)‖ := by
  rw [T, summatory_apply]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun m hm ↦ ?_)
  rw [summatory_apply]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun n hn ↦ ?_)
  obtain ⟨hm, _⟩ := Finset.mem_Ioc.mp hm
  obtain ⟨hn, _⟩ := Finset.mem_Ioc.mp hn
  simp only [norm_mul]
  exact mul_le_of_le_one_right (by positivity) (Bump.norm_smooth1_le_one hε_pos (by positivity))

theorem sup_summatory_eq_sup_nat {f : ℕ → ℂ}
    {x : ℝ} (hx : 1 ≤ x) :
  open Classical in
      ⨆ y ∈ Set.Icc 1 x, ‖summatory f y‖ =
      ⨆ K ∈ Set.Icc 1 ⌊x⌋₊, ‖summatory f (K + 2⁻¹)‖ := by
  have hfloor_add_half {n : ℕ} : ⌊(n + 2⁻¹: ℝ)⌋₊ = n := by
    rw [add_comm, Nat.floor_add_natCast (show 0 ≤ (2⁻¹ : ℝ) by positivity)]
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
    · refine bddAbove_range_biSup (B := summatory (fun m => ‖f m‖) x)
        (by positivity) ?_
      intro K hK
      simp only [Finset.coe_Icc, mem_Icc] at hK
      exact norm_summatory_le (by grind)
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
        · positivity
      simp [this, ciSup_unique, ge_iff_le]
      simp [summatory_apply, hfloor_add_half]
    · refine bddAbove_range_biSup (B := summatory (fun m => ‖f m‖) x)
        (by positivity) ?_
      intro y hy
      simp only [mem_Icc] at hy
      exact norm_summatory_le (Nat.floor_mono hy.2)


theorem temp [fg : FG]
    {x Q : ℝ} (hx : 1 ≤ x) :
  open Classical in
    summatory (fun q ↦ ∑ χ : DirichletCharacter ℂ q with χ.IsPrimitive,
      q * (q.totient : ℝ)⁻¹ * ⨆ y ∈ Set.Icc 1 x, ‖summatory (fun n ↦ (f * g) n * χ n) y‖) Q =
    summatory (fun q ↦ ∑ χ : DirichletCharacter ℂ q with χ.IsPrimitive,
      q * (q.totient : ℝ)⁻¹ * ⨆ K ∈ Set.Icc 1 ⌊x⌋₊, ‖summatory (fun n ↦ (f * g) n * χ n) (K + 2⁻¹)‖) Q := by
  simp_rw [sup_summatory_eq_sup_nat hx]


/-- Pointwise bound on `‖T ε y χ‖`: from the Mellin integral representation
`T_eq_integral_sum`, take norms inside the integral.  The factor
`‖(1/y)^{-(σ+t I)}‖ = y^σ` is constant in `t` and is pulled out. -/
theorem T_norm_le_integral [Bump] [FG] {q : ℕ} {ε : ℝ} (hε_pos : 0 < ε) (hε_one : ε < 1)
    {χ : DirichletCharacter ℂ q} {σ : ℝ} (hσ_pos : 0 < σ) (hσ : σ ≤ 2) {y : ℝ} (hy : 1 ≤ y) :
    ‖T ε y χ‖ ≤ (y ^ σ / (2 * π)) *
      ∫ t : ℝ, ‖summatory (fun m ↦ f m * χ m * (m : ℂ) ^ (-(σ + t * I))) M‖ *
        ‖summatory (fun n ↦ g n * χ n * (n : ℂ) ^ (-(σ + t * I))) N‖ *
        ‖mellin (fun x ↦ (Smooth1 ν ε x : ℂ)) (σ + t * I)‖ := by
  have hy0 : (0 : ℝ) < y := by positivity
  rw [T_eq_integral_sum hσ_pos hσ hε_pos y hy hε_one, norm_smul]
  have hnorm_const : ‖(1 / (2 * π) : ℝ)‖ = 1 / (2 * π) := by
    rw [Real.norm_eq_abs, abs_of_pos (by positivity)]
  rw [hnorm_const, show (y ^ σ / (2 * π)) = (1 / (2 * π)) * y ^ σ by ring, mul_assoc]
  gcongr
  calc ‖∫ t : ℝ, _‖
      ≤ ∫ t : ℝ, ‖summatory (fun m ↦ f m * χ m * (m : ℂ) ^ (-(σ + t * I))) M *
            summatory (fun n ↦ g n * χ n * (n : ℂ) ^ (-(σ + t * I))) N *
            (1 / (y : ℂ)) ^ (-(σ + t * I)) •
            mellin (fun x ↦ (Smooth1 ν ε x : ℂ)) (σ + t * I)‖ :=
        norm_integral_le_integral_norm _
    _ = ∫ t : ℝ, y ^ σ *
          (‖summatory (fun m ↦ f m * χ m * (m : ℂ) ^ (-(σ + t * I))) M‖ *
            ‖summatory (fun n ↦ g n * χ n * (n : ℂ) ^ (-(σ + t * I))) N‖ *
            ‖mellin (fun x ↦ (Smooth1 ν ε x : ℂ)) (σ + t * I)‖) := by
        apply MeasureTheory.integral_congr_ae
        filter_upwards with t
        simp only [norm_mul, smul_eq_mul]
        rw [norm_one_div_cpow_neg_vertical hy0]
        ring
    _ = y ^ σ * ∫ t : ℝ, _ := MeasureTheory.integral_const_mul _ _

/-! ### Auxiliary real-analysis lemmas for the `J`-integral (Step 4) -/

/-- `t ↦ (t²)⁻¹` is integrable on `(T, ∞)` for `T > 0`. -/
private lemma integrableOn_Ioi_inv_sq {T : ℝ} (hT : 0 < T) :
    MeasureTheory.IntegrableOn (fun t : ℝ => (t ^ 2)⁻¹) (Set.Ioi T) := by
  apply (integrableOn_Ioi_rpow_of_lt (a := -2) (by norm_num) hT).congr_fun ?_ measurableSet_Ioi
  intro t ht
  have htpos : 0 < t := hT.trans ht
  show t ^ (-2 : ℝ) = (t ^ 2)⁻¹
  rw [Real.rpow_neg htpos.le, show ((2 : ℝ)) = ((2 : ℕ) : ℝ) from by norm_num, Real.rpow_natCast]

/-- `∫_{(T,∞)} (t²)⁻¹ = T⁻¹` for `T > 0`. -/
private lemma integral_Ioi_inv_sq {T : ℝ} (hT : 0 < T) :
    ∫ t in Set.Ioi T, (t ^ 2)⁻¹ = T⁻¹ := by
  have h := integral_Ioi_rpow_of_lt (a := -2) (by norm_num) hT
  rw [show ((-2 : ℝ) + 1) = -1 by norm_num, Real.rpow_neg_one] at h
  rw [show (T⁻¹ : ℝ) = -T⁻¹ / (-1) by ring, ← h]
  refine setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
  have htpos : 0 < t := hT.trans ht
  show (t ^ 2)⁻¹ = t ^ (-2 : ℝ)
  rw [Real.rpow_neg htpos.le, show ((2 : ℝ)) = ((2 : ℕ) : ℝ) from by norm_num, Real.rpow_natCast]

/-- `t ↦ (t²)⁻¹` is integrable on `(-∞, -T)` for `T > 0`. -/
private lemma integrableOn_Iio_inv_sq {T : ℝ} (hT : 0 < T) :
    MeasureTheory.IntegrableOn (fun t : ℝ => (t ^ 2)⁻¹) (Set.Iio (-T)) := by
  have e : MeasurableEmbedding (fun x : ℝ => -x) :=
    (Homeomorph.neg ℝ).measurableEmbedding
  have key := (e.integrableOn_map_iff (μ := (volume : Measure ℝ))
    (f := fun t : ℝ => (t ^ 2)⁻¹) (s := Set.Iio (-T))).mpr
  rw [Measure.map_neg_eq_self] at key
  apply key
  have hset : (fun x : ℝ => -x) ⁻¹' Set.Iio (-T) = Set.Ioi T := by
    grind
  rw [hset]
  apply (integrableOn_Ioi_inv_sq hT).congr_fun ?_ measurableSet_Ioi
  intro x hx; simp [Function.comp]

/-- `∫_{(-∞,-T)} (t²)⁻¹ = T⁻¹` for `T > 0`. -/
private lemma integral_Iio_inv_sq {T : ℝ} (hT : 0 < T) :
    ∫ t in Set.Iio (-T), (t ^ 2)⁻¹ = T⁻¹ := by
  rw [setIntegral_congr_set (Iio_ae_eq_Iic), ← integral_Ioi_inv_sq hT]
  have key := integral_comp_neg_Iic (-T) (fun t => (t ^ 2)⁻¹)
  simp only [neg_neg, neg_sq] at key
  exact key

/-- `∫_{|t|>T} (t²)⁻¹ = 2T⁻¹` for `T > 0`. -/
private lemma integral_compl_Icc_inv_sq {T : ℝ} (hT : 0 < T) :
    ∫ t in (Set.Icc (-T) T)ᶜ, (t ^ 2)⁻¹ = 2 * T⁻¹ := by
  have hcompl : (Set.Icc (-T) T)ᶜ = Set.Iio (-T) ∪ Set.Ioi T := by
    grind
  rw [hcompl, setIntegral_union ?_ measurableSet_Ioi (integrableOn_Iio_inv_sq hT)
      (integrableOn_Ioi_inv_sq hT), integral_Iio_inv_sq hT, integral_Ioi_inv_sq hT]
  · ring
  · grind

/-- `∫_{0}^{T} (σ+t)⁻¹ = log(σ+T) - log σ` for `σ > 0`, `T ≥ 0`. -/
private lemma integral_inv_shift {σ T : ℝ} (hσ : 0 < σ) (hT : 0 ≤ T) :
    ∫ t in (0 : ℝ)..T, (σ + t)⁻¹ = Real.log (σ + T) - Real.log σ := by
  rw [intervalIntegral.integral_comp_add_left, add_zero,
    integral_inv (notMem_uIcc_of_lt hσ (by positivity)),
    Real.log_div (by positivity) hσ.ne']

/-- `∫_{[-T,T]} (σ+|t|)⁻¹ = 2(log(σ+T) - log σ)` for `σ > 0`, `T ≥ 0`. -/
private lemma integral_Icc_inv_abs {σ T : ℝ} (hσ : 0 < σ) (hT : 0 ≤ T) :
    ∫ t in Set.Icc (-T) T, (σ + |t|)⁻¹ = 2 * (Real.log (σ + T) - Real.log σ) := by
  have hcont : Continuous (fun t : ℝ => (σ + |t|)⁻¹) := by
    apply Continuous.inv₀
    · fun_prop
    · grind
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith : -T ≤ T),
    ← intervalIntegral.integral_add_adjacent_intervals (b := 0)
      (hcont.intervalIntegrable _ _) (hcont.intervalIntegrable _ _)]
  have hright : ∫ t in (0 : ℝ)..T, (σ + |t|)⁻¹ = Real.log (σ + T) - Real.log σ := by
    rw [← integral_inv_shift hσ hT]
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le hT, Set.mem_Icc] at ht
    show (σ + |t|)⁻¹ = (σ + t)⁻¹
    rw [abs_of_nonneg ht.1]
  have hleft : ∫ t in (-T : ℝ)..0, (σ + |t|)⁻¹ = Real.log (σ + T) - Real.log σ := by
    rw [← hright]
    simpa using (intervalIntegral.integral_comp_neg
      (fun t : ℝ ↦ (σ + |t|)⁻¹) (a := 0) (b := T)).symm
  rw [hleft, hright]
  ring

/-- Bound A of Step 4: on the vertical line `Re s = σ` with `0 < σ ≤ 2` and `0 < ε < 1`, the
Mellin transform of `Smooth1 ν ε` decays like `1/‖s‖`, with a constant depending only on `ν`.
Combines `MellinOfSmooth1a` with the strip bound `mellin_bump_bounded`. -/
lemma exists_mellin_smooth1_boundA [Bump] :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (ε σ t : ℝ), 0 < ε → ε < 1 → 0 < σ → σ ≤ 2 →
      ‖mellin (fun u ↦ (Smooth1 ν ε u : ℂ)) ((σ : ℂ) + t * I)‖
        ≤ C * ‖(σ : ℂ) + t * I‖⁻¹ := by
  obtain ⟨C, hC⟩ := (mellin_bump_bounded (σ₁ := 0) (σ₂ := 2) (by positivity)
    (diffν.of_le (by simp)) suppν).bound
  rw [Filter.eventually_principal] at hC
  simp only [mem_setOf_eq, norm_one, mul_one] at hC
  have hCnonneg : 0 ≤ C := le_trans (norm_nonneg _) (hC (1 : ℂ) (by simp))
  refine ⟨C, hCnonneg, fun ε σ t hε hε1 hσ hσ2 ↦ ?_⟩
  have hsre : ((σ : ℂ) + t * I).re = σ := by simp
  rw [MellinOfSmooth1a (diffν.of_le (by simp)) suppν hε (by grind),
    norm_mul, norm_inv, mul_comm]
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  apply hC
  have hre : ((ε : ℂ) * ((σ : ℂ) + t * I)).re = ε * σ := by simp [Complex.mul_re]
  rw [hre]
  exact ⟨by positivity, by nlinarith⟩

/-- Bound B of Step 4, specialised to the line `Re s = σ`: `‖𝓜(Smooth1 ν ε)(σ+tI)‖ ≤
C·(ε‖σ+tI‖²)⁻¹` for `0 < σ ≤ 2`, `0 < ε < 1`, with `C > 0` depending only on `ν`. -/
lemma exists_mellin_smooth1_boundB [Bump] :
    ∃ C : ℝ, 0 < C ∧ ∀ (σ : ℝ), 0 < σ → σ ≤ 2 → ∀ (ε t : ℝ), 0 < ε → ε < 1 →
      ‖mellin (fun u ↦ (Smooth1 ν ε u : ℂ)) ((σ : ℂ) + t * I)‖
        ≤ C * (ε * ‖(σ : ℂ) + t * I‖ ^ 2)⁻¹ := by
  obtain ⟨C, hCpos, hC⟩ := MellinOfSmooth1b (diffν.of_le (by simp)) suppν
  refine ⟨C, hCpos, fun σ hσ hσ2 ε t hε hε1 => ?_⟩
  have hre : ((σ : ℂ) + t * I).re = σ := by simp
  exact hC σ hσ ((σ : ℂ) + t * I) hre.ge (hre.le.trans hσ2) ε hε hε1

/-- The split-at-`1/ε` log estimate, abstracted: for `x ≥ 1` and `L = log(x+1)`,
`log(1 + 6 log 2 · x · L) ≤ (1 + 6 log 2) · L`. -/
lemma log_one_add_le {x L : ℝ} (hx : 1 ≤ x) (hL : L = Real.log (x + 1)) :
    Real.log (1 + 6 * Real.log 2 * x * L) ≤ (1 + 6 * Real.log 2) * L := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hLpos : 0 < L := by rw [hL]; exact Real.log_pos (by linarith)
  have hxpos : 0 < x := by positivity
  have ha_pos : 0 < 6 * Real.log 2 := by positivity
  have key : 1 + 6 * Real.log 2 * x * L ≤ (1 + x) * (1 + 6 * Real.log 2 * L) := by
    nlinarith [mul_pos ha_pos hLpos, hxpos, mul_pos hxpos (mul_pos ha_pos hLpos)]
  have h1 : Real.log (1 + 6 * Real.log 2 * x * L) ≤ Real.log ((1 + x) * (1 + 6 * Real.log 2 * L)) :=
    Real.log_le_log (by positivity) key
  rw [Real.log_mul (by positivity) (by positivity)] at h1
  have h2 : Real.log (1 + x) = L := by rw [hL, add_comm]
  have h3 : Real.log (1 + 6 * Real.log 2 * L) ≤ 6 * Real.log 2 * L := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 1 + 6 * Real.log 2 * L by positivity)
    linarith
  grind

/-- The constant in the `J`-integral estimate `∫ ‖𝓜(σ+tI)‖ dt ≤ C_J · log(x+1)`
(Step 4 of `notes/theorem26_6_smooth.md`), assembled from the bump-decay constants `CA`
(bound A, `exists_mellin_smooth1_boundA`) and `CB` (bound B, `MellinOfSmooth1b`). -/
noncomputable def C_J [Bump] : ℝ :=
  2 * Real.sqrt 2 * (1 + 6 * Real.log 2) * exists_mellin_smooth1_boundA.choose
    + 2 * exists_mellin_smooth1_boundB.choose / Real.log 2

/-- The implied constant of Theorem 26.6, assembled from `Real.exp 1 / (2π)` (the `y^σ ≤ e`
prefactor), the large-sieve constant `C_LS`, and the `J`-integral constant `C_J`. -/
noncomputable def C_LSC [Bump] : ℝ := Real.exp 1 / (2 * π) * C_LS * C_J

/-- The large-sieve constant is nonnegative: apply the large sieve with a single nonzero
coefficient, whose left-hand side is a nonnegative sum. -/
lemma C_LS_nonneg : 0 ≤ C_LS := by
  have h := large_sieve 1 le_rfl 0 1 one_pos (fun n => if n = 1 then 1 else 0)
  have hnonneg : (0 : ℝ) ≤ C_LS * ((1 : ℕ) + (1 : ℝ) ^ 2) *
      ∑ n ∈ Finset.Ioc (0 : ℤ) (0 + (1 : ℕ)), ‖(if n = 1 then (1 : ℂ) else 0)‖ ^ 2 := by
    refine le_trans ?_ h
    positivity
  rw [show Finset.Ioc (0 : ℤ) (0 + (1 : ℕ)) = {1} by decide] at hnonneg
  norm_num at hnonneg
  linarith

lemma C_J_nonneg [Bump] : 0 ≤ C_J := by
  have := exists_mellin_smooth1_boundA.choose_spec.1
  have := exists_mellin_smooth1_boundB.choose_spec.1
  unfold C_J
  positivity

lemma C_LSC_nonneg [Bump] : 0 ≤ C_LSC := by
  have := C_LS_nonneg
  have := C_J_nonneg
  unfold C_LSC
  positivity

end Flat

namespace Mathlib.Meta.Positivity
open Qq Lean Meta

/-- Positivity of the constants used in the Perron and large-sieve estimates. -/
@[positivity Flat.FG.M, Flat.FG.N, C_LS, Flat.C_J, Flat.C_LSC]
def evalPerronConstant : PositivityExt where eval {u α} zα pα? e :=
  match pα? with | none => pure .none | some pα => do
  match u, α, e with
  | 0, ~q(ℝ), ~q(@Flat.FG.M $inst) =>
    assertInstancesCommute
    return .positive q(@Flat.FG.hM_pos $inst)
  | 0, ~q(ℝ), ~q(@Flat.FG.N $inst) =>
    assertInstancesCommute
    return .positive q(@Flat.FG.hN_pos $inst)
  | 0, ~q(ℝ), ~q(C_LS) =>
    assertInstancesCommute
    return .nonnegative q(Flat.C_LS_nonneg)
  | 0, ~q(ℝ), ~q(@Flat.C_J $inst) =>
    assertInstancesCommute
    return .nonnegative q(@Flat.C_J_nonneg $inst)
  | 0, ~q(ℝ), ~q(@Flat.C_LSC $inst) =>
    assertInstancesCommute
    return .nonnegative q(@Flat.C_LSC_nonneg $inst)
  | _, _, _ => throwError "not a Perron constant"

end Mathlib.Meta.Positivity

namespace Flat
open Complex

/-- Reindex a sum over the integer interval `(0, k]` as a sum over the natural-number
interval `(0, k]` via the cast `ℕ → ℤ`. -/
lemma sum_Ioc_natCast {R : Type*} [AddCommMonoid R] (k : ℕ) (G : ℤ → R) :
    ∑ n ∈ Finset.Ioc (0 : ℤ) (k : ℤ), G n = ∑ m ∈ Finset.Ioc (0 : ℕ) k, G (m : ℤ) := by
  apply Finset.sum_nbij' (i := fun n : ℤ ↦ n.toNat) (j := fun m : ℕ ↦ (m : ℤ)) <;> grind

/-- One application of the large sieve to a single Dirichlet polynomial:
`∑_{q≤Q} ∑*_χ (q/φq) ‖∑_{m≤P} h(m) χ(m) m^{-(σ+it)}‖² ≤ C_LS (P+Q²) ∑_{m≤P} ‖h(m)‖²`,
where the `m^{-σ}` factors with `σ > 0`, `m ≥ 1` only shrink the coefficients. -/
lemma largeSieve_factor {Q : ℝ} (hQ : 1 ≤ Q) {σ : ℝ} (hσ_pos : 0 < σ) (t : ℝ)
    (h : ℕ → ℂ) (P : ℝ) :
    open Classical in
    ∑ q ∈ Finset.Ioc 0 ⌊Q⌋₊, ∑ χ : DirichletCharacter ℂ q with χ.IsPrimitive,
      (q : ℝ) * (q.totient : ℝ)⁻¹ *
      ‖summatory (fun m ↦ h m * χ m * (m : ℂ) ^ (-(σ + t * I))) P‖ ^ 2
    ≤ C_LS * (P + Q ^ 2) * summatory (fun m ↦ ‖h m‖ ^ 2) P := by
  classical
  have hSnn : (0 : ℝ) ≤ summatory (fun m ↦ ‖h m‖ ^ 2) P :=
    summatory_nonneg _ _ (fun n _ => by positivity)
  rcases Nat.eq_zero_or_pos ⌊P⌋₊ with hP0 | hPpos
  · simp [summatory_apply, hP0]
  -- `⌊P⌋₊ > 0`: apply the large sieve.
  have hP1 : (1 : ℝ) ≤ P := Nat.floor_pos.mp hPpos
  have hPnn : (0 : ℝ) ≤ P := by positivity
  set c : ℤ → ℂ := fun n => h n.toNat * ((n.toNat : ℂ)) ^ (-(σ + t * I)) with hc
  have hLS := large_sieve Q hQ 0 ⌊P⌋₊ hPpos c
  simp only [div_eq_mul_inv, zero_add] at hLS
  -- (a) rewrite each inner large-sieve sum as our `summatory`.
  have ha : ∀ (q : ℕ) (χ : DirichletCharacter ℂ q),
      (∑ n ∈ Finset.Ioc (0 : ℤ) (⌊P⌋₊ : ℤ), c n * χ n)
        = summatory (fun m ↦ h m * χ m * (m : ℂ) ^ (-(σ + t * I))) P := by
    intro q χ
    rw [sum_Ioc_natCast, summatory_apply]
    apply Finset.sum_congr rfl
    intro m hm
    simp only [hc, Int.toNat_natCast]
    rw [show ((m : ℤ) : ZMod q) = ((m : ℕ) : ZMod q) from by push_cast; ring]
    ring
  -- (b) the coefficient ℓ²-sum is bounded by `∑ ‖h m‖²`.
  have hb : (∑ n ∈ Finset.Ioc (0 : ℤ) (⌊P⌋₊ : ℤ), ‖c n‖ ^ 2)
      ≤ summatory (fun m ↦ ‖h m‖ ^ 2) P := by
    rw [sum_Ioc_natCast, summatory_apply]
    apply Finset.sum_le_sum
    intro m hm
    simp only [Finset.mem_Ioc] at hm
    have hm1 : 1 ≤ m := hm.1
    simp only [hc, Int.toNat_natCast, norm_mul, mul_pow]
    rw [Complex.norm_natCast_cpow_of_pos (by positivity)]
    have hre : (-(σ + t * I)).re = -σ := by simp
    rw [hre]
    have hle1 : (m : ℝ) ^ (-σ) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hm1) (by linarith)
    calc ‖h m‖ ^ 2 * ((m : ℝ) ^ (-σ)) ^ 2
        ≤ ‖h m‖ ^ 2 * 1 ^ 2 := by gcongr
      _ = ‖h m‖ ^ 2 := by ring
  -- assemble
  have hCLS := C_LS_nonneg
  calc ∑ q ∈ Finset.Ioc 0 ⌊Q⌋₊, ∑ χ : DirichletCharacter ℂ q with χ.IsPrimitive,
        (q : ℝ) * (q.totient : ℝ)⁻¹ *
        ‖summatory (fun m ↦ h m * χ m * (m : ℂ) ^ (-(σ + t * I))) P‖ ^ 2
      = ∑ q ∈ Finset.Ioc 0 ⌊Q⌋₊, ∑ χ : DirichletCharacter ℂ q with χ.IsPrimitive,
        (q : ℝ) * (q.totient : ℝ)⁻¹ *
        ‖∑ n ∈ Finset.Ioc (0 : ℤ) (⌊P⌋₊ : ℤ), c n * χ n‖ ^ 2 := by
          simp_rw [ha]
    _ ≤ C_LS * ((⌊P⌋₊ : ℝ) + Q ^ 2) * ∑ n ∈ Finset.Ioc (0 : ℤ) (⌊P⌋₊ : ℤ), ‖c n‖ ^ 2 := hLS
    _ ≤ C_LS * ((⌊P⌋₊ : ℝ) + Q ^ 2) * summatory (fun m ↦ ‖h m‖ ^ 2) P := by
          apply mul_le_mul_of_nonneg_left hb
          positivity
    _ ≤ C_LS * (P + Q ^ 2) * summatory (fun m ↦ ‖h m‖ ^ 2) P := by
          apply mul_le_mul_of_nonneg_right _ hSnn
          have : (⌊P⌋₊ : ℝ) ≤ P := Nat.floor_le hPnn
          gcongr

/-- Weighted Cauchy–Schwarz, with the weights kept outside the squares. -/
lemma sum_weight_mul_le_sqrt {ι : Type*} (s : Finset ι) (w a b : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) :
    ∑ i ∈ s, w i * (a i * b i) ≤
      √(∑ i ∈ s, w i * a i ^ 2) * √(∑ i ∈ s, w i * b i ^ 2) := by
  have hprod : ∀ i, (√(w i) * a i) * (√(w i) * b i) = w i * (a i * b i) := by
    intro i
    rw [mul_mul_mul_comm, Real.mul_self_sqrt (hw i)]
  simpa only [hprod, mul_pow, Real.sq_sqrt (hw _)] using
    Real.sum_mul_le_sqrt_mul_sqrt s (fun i ↦ √(w i) * a i) (fun i ↦ √(w i) * b i)

lemma sqrt_add_sq_mul_le {M N Q : ℝ} (hM : 0 ≤ M) (hN : 0 ≤ N) (hQ : 0 ≤ Q) :
    √(M + Q ^ 2) * √(N + Q ^ 2) ≤ √(N * M) + √M * Q + √N * Q + Q ^ 2 := by
  have hbound (x : ℝ) (hx : 0 ≤ x) : √(x + Q ^ 2) ≤ √x + Q := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity, ?_⟩
    nlinarith [Real.sq_sqrt hx, mul_nonneg (Real.sqrt_nonneg x) hQ]
  calc
    _ ≤ (√M + Q) * (√N + Q) := by gcongr <;> apply hbound <;> assumption
    _ = _ := by rw [Real.sqrt_mul hN]; ring

/-- Step 4 of `notes/theorem26_6_smooth.md`: summing the pointwise products
`‖F_{σ+tI}(χ)‖·‖G_{σ+tI}(χ)‖` over `q ≤ Q` and primitive `χ (mod q)` (weighted by `q/φ(q)`),
Cauchy–Schwarz and two applications of the large sieve give a bound in terms of the `ℓ²` norms
of `f` and `g`, uniformly in `t`. -/
theorem largeSieve_char_bound [FG] {Q : ℝ} (hQ : 1 ≤ Q) {σ : ℝ} (hσ_pos : 0 < σ) (t : ℝ) :
    open Classical in
    summatory (fun q ↦ ∑ χ : DirichletCharacter ℂ q with χ.IsPrimitive,
      (q : ℝ) * (q.totient : ℝ)⁻¹ *
      (‖summatory (fun m ↦ f m * χ m * (m : ℂ) ^ (-(σ + t * I))) M‖ *
       ‖summatory (fun n ↦ g n * χ n * (n : ℂ) ^ (-(σ + t * I))) N‖)) Q
    ≤ C_LS * (√(N * M) + √M * Q + √N * Q + Q ^ 2) *
      √(summatory (fun m ↦ ‖f m‖ ^ 2) M) * √(summatory (fun n ↦ ‖g n‖ ^ 2) N) := by
  classical
  let s := (Finset.Ioc 0 ⌊Q⌋₊).sigma
    (fun q ↦ Finset.univ.filter (fun χ : DirichletCharacter ℂ q ↦ χ.IsPrimitive))
  have hCS := sum_weight_mul_le_sqrt s (fun p ↦ (p.1 : ℝ) * (p.1.totient : ℝ)⁻¹)
    (fun p ↦ ‖summatory (fun m ↦ f m * p.2 m * (m : ℂ) ^ (-(σ + t * I))) M‖)
    (fun p ↦ ‖summatory (fun n ↦ g n * p.2 n * (n : ℂ) ^ (-(σ + t * I))) N‖)
    (fun _ ↦ by positivity)
  simp only [s, Finset.sum_sigma] at hCS
  refine hCS.trans ?_
  calc
    _ ≤ √(C_LS * (M + Q ^ 2) * summatory (fun m ↦ ‖f m‖ ^ 2) M) *
        √(C_LS * (N + Q ^ 2) * summatory (fun n ↦ ‖g n‖ ^ 2) N) := by
      gcongr <;> exact largeSieve_factor hQ hσ_pos t _ _
    _ = C_LS * (√(M + Q ^ 2) * √(N + Q ^ 2)) *
        √(summatory (fun m ↦ ‖f m‖ ^ 2) M) * √(summatory (fun n ↦ ‖g n‖ ^ 2) N) := by
      simp only [Real.sqrt_mul (by positivity : 0 ≤ C_LS * (M + Q ^ 2)),
        Real.sqrt_mul (by positivity : 0 ≤ C_LS * (N + Q ^ 2)),
        Real.sqrt_mul C_LS_nonneg]
      nlinarith [Real.sq_sqrt C_LS_nonneg]
    _ ≤ _ := by
      gcongr
      exact sqrt_add_sq_mul_le (by positivity) (by positivity) (by positivity)

/-- `‖σ + tI‖⁻¹ ≤ √2 · (σ + |t|)⁻¹` for `σ > 0`: the reverse triangle estimate
`σ + |t| ≤ √2 · ‖σ + tI‖`. -/
private lemma normI_inv_le {σ : ℝ} (hσ : 0 < σ) (t : ℝ) :
    ‖(σ : ℂ) + t * I‖⁻¹ ≤ Real.sqrt 2 * (σ + |t|)⁻¹ := by
  have : σ + t * I ≠ 0 := by
    apply_fun Complex.re
    simp [hσ.ne.symm]
  rw [← sq_le_sq₀ (by positivity) (by positivity)]
  simp [field, Complex.norm_eq_sqrt_sq_add_sq]
  rw [Real.sq_sqrt (by positivity)]
  conv_rhs => rw [← abs_of_nonneg (sq_nonneg t), abs_pow]
  have : 0 ≤ (σ - |t|)^2 := by positivity
  linarith

/-- Step 4 of `notes/theorem26_6_smooth.md`: the `J`-integral estimate.  The Mellin kernel
`𝓜(Smooth1 ν ε)` decays like `1/‖s‖` near the real axis and like `1/(ε‖s‖²)` in the tails;
splitting the integral at `|t| = 1/ε` gives `J ≪ log(1/(σε)) ≍ log(x+1)`. -/
theorem mellin_J_bound [Bump] {ε : ℝ} (hε_pos : 0 < ε) (hε_one : ε < 1) {σ : ℝ} (hσ_pos : 0 < σ)
    (hσ : σ ≤ 2) {x : ℝ} (hx : 1 ≤ x) (hσx : σ = (Real.log (x + 1))⁻¹)
    (hε : ε = (6 * Real.log 2)⁻¹ * x⁻¹) :
    ∫ t : ℝ, ‖mellin (fun u ↦ (Smooth1 ν ε u : ℂ)) (σ + t * I)‖ ≤ C_J * Real.log (x + 1) := by
  classical
  set L := Real.log (x + 1) with hL
  have hx1 : (1 : ℝ) < x + 1 := by linarith
  have hL_pos : 0 < L := Real.log_pos hx1
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hL_ge : Real.log 2 ≤ L := by
    rw [hL]; exact Real.log_le_log (by positivity) (by linarith)
  -- the two bump-decay constants
  obtain ⟨hCA_nonneg, hCA⟩ := exists_mellin_smooth1_boundA.choose_spec
  obtain ⟨hCB_pos, hCB⟩ := exists_mellin_smooth1_boundB.choose_spec
  rw [C_J]
  set CA := exists_mellin_smooth1_boundA.choose with hCAdef
  set CB := exists_mellin_smooth1_boundB.choose with hCBdef
  -- the split radius `T = 1/ε`
  set T := ε⁻¹ with hTdef
  have hT_pos : 0 < T := by positivity
  -- the integrand is integrable on `ℝ`
  have hVI : Integrable (fun t : ℝ ↦ mellin (fun u ↦ (Smooth1 ν ε u : ℂ)) (σ + t * I)) :=
    Bump.verticalIntegrable hε_pos hε_one hσ_pos hσ
  have hInt : Integrable (fun t : ℝ ↦ ‖mellin (fun u ↦ (Smooth1 ν ε u : ℂ)) (σ + t * I)‖) :=
    hVI.norm
  -- centre estimate `∫_{|t|≤T} ≤ 2√2 (1+6 log 2) CA · L`
  have hcenter_log : Real.log (σ + T) - Real.log σ ≤ (1 + 6 * Real.log 2) * L := by
    rw [← Real.log_div (by positivity) hσ_pos.ne']
    have hTσ : (σ + T) / σ = 1 + 6 * Real.log 2 * x * L := by
      grind
    rw [hTσ]
    exact log_one_add_le hx hL
  have hcenter : ∫ t in Set.Icc (-T) T, ‖mellin (fun u ↦ (Smooth1 ν ε u : ℂ)) (σ + t * I)‖
      ≤ 2 * Real.sqrt 2 * (1 + 6 * Real.log 2) * CA * L := by
    have hmaj_cont : Continuous (fun t : ℝ => (Real.sqrt 2 * CA) * (σ + |t|)⁻¹) := by
      apply Continuous.mul continuous_const
      apply Continuous.inv₀
      · fun_prop
      · grind
    calc ∫ t in Set.Icc (-T) T, ‖mellin (fun u ↦ (Smooth1 ν ε u : ℂ)) (σ + t * I)‖
        ≤ ∫ t in Set.Icc (-T) T, (Real.sqrt 2 * CA) * (σ + |t|)⁻¹ := by
          apply setIntegral_mono_on hInt.integrableOn
            (hmaj_cont.continuousOn.integrableOn_compact isCompact_Icc) measurableSet_Icc
          intro t _
          calc ‖mellin (fun u ↦ (Smooth1 ν ε u : ℂ)) (σ + t * I)‖
              ≤ CA * ‖(σ : ℂ) + t * I‖⁻¹ := hCA ε σ t hε_pos hε_one hσ_pos hσ
            _ ≤ CA * (Real.sqrt 2 * (σ + |t|)⁻¹) :=
                mul_le_mul_of_nonneg_left (normI_inv_le hσ_pos t) hCA_nonneg
            _ = (Real.sqrt 2 * CA) * (σ + |t|)⁻¹ := by ring
      _ = (Real.sqrt 2 * CA) * ∫ t in Set.Icc (-T) T, (σ + |t|)⁻¹ :=
          MeasureTheory.integral_const_mul _ _
      _ = (Real.sqrt 2 * CA) * (2 * (Real.log (σ + T) - Real.log σ)) := by
          rw [integral_Icc_inv_abs hσ_pos hT_pos.le]
      _ ≤ (Real.sqrt 2 * CA) * (2 * ((1 + 6 * Real.log 2) * L)) := by
          apply mul_le_mul_of_nonneg_left _ (mul_nonneg (Real.sqrt_nonneg 2) hCA_nonneg)
          grind
      _ = 2 * Real.sqrt 2 * (1 + 6 * Real.log 2) * CA * L := by ring
  -- tail estimate `∫_{|t|>T} ≤ 2 CB ≤ (2 CB / log 2) · L`
  have htail : ∫ t in (Set.Icc (-T) T)ᶜ, ‖mellin (fun u ↦ (Smooth1 ν ε u : ℂ)) (σ + t * I)‖
      ≤ 2 * CB / Real.log 2 * L := by
    have hmaj_compl : MeasureTheory.IntegrableOn (fun t : ℝ => (t ^ 2)⁻¹) (Set.Icc (-T) T)ᶜ := by
      have hcompl : (Set.Icc (-T) T)ᶜ = Set.Iio (-T) ∪ Set.Ioi T := by
        grind
      rw [hcompl]
      exact (integrableOn_Iio_inv_sq hT_pos).union (integrableOn_Ioi_inv_sq hT_pos)
    calc ∫ t in (Set.Icc (-T) T)ᶜ, ‖mellin (fun u ↦ (Smooth1 ν ε u : ℂ)) (σ + t * I)‖
        ≤ ∫ t in (Set.Icc (-T) T)ᶜ, (CB / ε) * (t ^ 2)⁻¹ := by
          apply setIntegral_mono_on hInt.integrableOn (hmaj_compl.const_mul (CB / ε))
            measurableSet_Icc.compl
          intro t ht
          have htabs : T < |t| := by
            grind
          have htne : t ≠ 0 := by
            grind
          have ht2 : 0 < t ^ 2 := by positivity
          have hzsq : ‖(σ : ℂ) + t * I‖ ^ 2 = σ ^ 2 + t ^ 2 := by
            rw [Complex.sq_norm, Complex.normSq_add_mul_I]
          have ht2le : t ^ 2 ≤ ‖(σ : ℂ) + t * I‖ ^ 2 := by rw [hzsq]; nlinarith [sq_nonneg σ]
          calc ‖mellin (fun u ↦ (Smooth1 ν ε u : ℂ)) (σ + t * I)‖
              ≤ CB * (ε * ‖(σ : ℂ) + t * I‖ ^ 2)⁻¹ := hCB σ hσ_pos hσ ε t hε_pos hε_one
            _ ≤ CB * (ε * t ^ 2)⁻¹ := by
                have hle : ε * t ^ 2 ≤ ε * ‖(σ : ℂ) + t * I‖ ^ 2 :=
                  mul_le_mul_of_nonneg_left ht2le hε_pos.le
                have hinv : (ε * ‖(σ : ℂ) + t * I‖ ^ 2)⁻¹ ≤ (ε * t ^ 2)⁻¹ := by
                  simpa only [one_div] using one_div_le_one_div_of_le (mul_pos hε_pos ht2) hle
                exact mul_le_mul_of_nonneg_left hinv hCB_pos.le
            _ = (CB / ε) * (t ^ 2)⁻¹ := by grind
      _ = (CB / ε) * ∫ t in (Set.Icc (-T) T)ᶜ, (t ^ 2)⁻¹ := MeasureTheory.integral_const_mul _ _
      _ = (CB / ε) * (2 * T⁻¹) := by rw [integral_compl_Icc_inv_sq hT_pos]
      _ = 2 * CB := by grind
      _ ≤ 2 * CB / Real.log 2 * L := by
          have hLratio : 1 ≤ L / Real.log 2 := by
            rw [le_div_iff₀ hlog2]; linarith
          calc 2 * CB = 2 * CB * 1 := by ring
            _ ≤ 2 * CB * (L / Real.log 2) :=
                mul_le_mul_of_nonneg_left hLratio (mul_nonneg (by positivity) hCB_pos.le)
            _ = 2 * CB / Real.log 2 * L := by ring
  -- assemble
  rw [← MeasureTheory.integral_add_compl (measurableSet_Icc (a := -T) (b := T)) hInt]
  grind

/-- For each `q`, `χ` and each `t`, the integrand
`t ↦ ‖F_{σ+tI}(χ)‖·‖G_{σ+tI}(χ)‖·‖𝓜(σ+tI)‖` is integrable: the two partial-sum norms are
continuous and bounded (constant `r^{-σ}` factors), and the Mellin factor is vertically
integrable. -/
theorem integrable_norm_FG_mellin [Bump] [FG] {q : ℕ} {ε : ℝ} (hε_pos : 0 < ε) (hε_one : ε < 1)
    {χ : DirichletCharacter ℂ q} {σ : ℝ} (hσ_pos : 0 < σ) (hσ : σ ≤ 2) :
    Integrable (fun t : ℝ =>
      ‖summatory (fun m ↦ f m * χ m * (m : ℂ) ^ (-(σ + t * I))) M‖ *
        ‖summatory (fun n ↦ g n * χ n * (n : ℂ) ^ (-(σ + t * I))) N‖ *
        ‖mellin (fun u ↦ (Smooth1 ν ε u : ℂ)) (σ + t * I)‖) := by
  have hcont : Continuous (fun t : ℝ ↦
      ‖summatory (fun m ↦ f m * χ m * (m : ℂ) ^ (-(σ + t * I))) M‖ *
        ‖summatory (fun n ↦ g n * χ n * (n : ℂ) ^ (-(σ + t * I))) N‖) := by
    fun_prop
  refine (Bump.verticalIntegrable hε_pos hε_one hσ_pos hσ).norm.bdd_mul
    hcont.aestronglyMeasurable (c :=
      summatory (fun m ↦ ‖f m * χ m‖ * (m : ℝ) ^ (-σ)) M *
      summatory (fun n ↦ ‖g n * χ n‖ * (n : ℝ) ^ (-σ)) N) ?_
  filter_upwards with t
  rw [Real.norm_of_nonneg (by positivity)]
  exact mul_le_mul (norm_dirichletSum_le _ _ _ _) (norm_dirichletSum_le _ _ _ _)
    (norm_nonneg _) (by positivity)

open _root_.Classical in
theorem summatory_T_ll [Bump] [FG] {ε Q : ℝ} (hε_pos : 0 < ε) (hQ : 1 ≤ Q)
    {x : ℝ} (hx : 1 ≤ x) (hε : ε = (6 * Real.log 2)⁻¹ * x⁻¹)  :
    summatory (fun q => ∑ χ : DirichletCharacter ℂ q with χ.IsPrimitive, ↑q * (↑q.totient)⁻¹ * ⨆ y ∈ Icc 1 (x+1), ‖T ε y χ‖) Q ≤ C_LSC *
    (√(N * M) + √M * Q + √N * Q + Q ^ 2) * √(summatory (fun m => ‖f m‖ ^ 2) M) * √(summatory (fun n => ‖g n‖ ^ 2) N) * Real.log (x + 1) := by
  classical
  have hlog2 := Real.log_two_gt_d9
  -- `ε < 1` is automatic: `ε = (6 log 2)⁻¹ x⁻¹ ≤ (6 log 2)⁻¹ < 1`.
  have hε_one : ε < 1 := by
    have hx' : x⁻¹ ≤ 1 := by rw [inv_le_one₀ (by positivity)]; exact hx
    calc ε ≤ (6 * Real.log 2)⁻¹ * x⁻¹ := hε.le
      _ ≤ (6 * Real.log 2)⁻¹ * 1 := by gcongr
      _ < 1 := by rw [mul_one, inv_lt_one₀ (by positivity)]; nlinarith
  -- Set `σ = 1/log(x+1)`, so `0 < σ ≤ 2` and `y^σ ≤ (x+1)^σ = e` for `y ≤ x+1`.
  set L := Real.log (x + 1) with hL
  have hx1 : (1 : ℝ) < x + 1 := by linarith
  have hL_pos : 0 < L := Real.log_pos hx1
  set σ : ℝ := L⁻¹ with hσdef
  have hσ_pos : 0 < σ := by positivity
  have hL_ge : Real.log 2 ≤ L := Real.log_le_log (by positivity) (by linarith)
  have hσ_le : σ ≤ 2 := by
    rw [hσdef, inv_le_comm₀ hL_pos (by positivity)]
    linarith
  -- `(x+1)^σ = e`, hence `y^σ ≤ e` for `1 ≤ y ≤ x+1`.
  have hxσ : (x + 1) ^ σ = Real.exp 1 := by
    rw [Real.rpow_def_of_pos (by positivity), hσdef, ← hL, mul_inv_cancel₀ hL_pos.ne']
  -- Abbreviation for the (nonnegative) integrand.
  let B : ∀ (q : ℕ), DirichletCharacter ℂ q → ℝ → ℝ := fun q χ t =>
    ‖summatory (fun m ↦ f m * χ m * (m : ℂ) ^ (-(σ + t * I))) M‖ *
      ‖summatory (fun n ↦ g n * χ n * (n : ℂ) ^ (-(σ + t * I))) N‖ *
      ‖mellin (fun u ↦ (Smooth1 ν ε u : ℂ)) (σ + t * I)‖
  have hB_int : ∀ (q : ℕ) (χ : DirichletCharacter ℂ q), Integrable (B q χ) :=
    fun q χ => integrable_norm_FG_mellin hε_pos hε_one hσ_pos hσ_le
  -- Step 1 & 3: per-character bound, using `T_norm_le_integral` and `y^σ ≤ e`.
  have hsup : ∀ (q : ℕ) (χ : DirichletCharacter ℂ q),
      (⨆ y ∈ Icc 1 (x + 1), ‖T ε y χ‖) ≤ (Real.exp 1 / (2 * π)) * ∫ t : ℝ, B q χ t := by
    intro q χ
    have hI_nonneg : 0 ≤ ∫ t : ℝ, B q χ t := by positivity
    apply Real.iSup_le _ (by positivity)
    intro y
    apply Real.iSup_le _ (by positivity)
    intro hy
    simp only [mem_Icc] at hy
    calc ‖T ε y χ‖
        ≤ (y ^ σ / (2 * π)) * ∫ t : ℝ, B q χ t :=
          T_norm_le_integral hε_pos hε_one hσ_pos hσ_le hy.1
      _ ≤ (Real.exp 1 / (2 * π)) * ∫ t : ℝ, B q χ t := by
          apply mul_le_mul_of_nonneg_right _ hI_nonneg
          gcongr
          rw [← hxσ]
          exact Real.rpow_le_rpow (by linarith [hy.1]) hy.2 hσ_pos.le
  -- `D t` is the large-sieve double sum at parameter `t` (without the Mellin factor).
  set D : ℝ → ℝ := fun t => summatory (fun q =>
    ∑ χ : DirichletCharacter ℂ q with χ.IsPrimitive,
      (q : ℝ) * (q.totient : ℝ)⁻¹ *
      (‖summatory (fun m ↦ f m * χ m * (m : ℂ) ^ (-(σ + t * I))) M‖ *
       ‖summatory (fun n ↦ g n * χ n * (n : ℂ) ^ (-(σ + t * I))) N‖)) Q with hDdef
  set Cb : ℝ := C_LS * (√(N * M) + √M * Q + √N * Q + Q ^ 2) *
    √(summatory (fun m ↦ ‖f m‖ ^ 2) M) * √(summatory (fun n ↦ ‖g n‖ ^ 2) N) with hCbdef
  have hD_le : ∀ t, D t ≤ Cb := fun t => largeSieve_char_bound hQ hσ_pos t
  have hmnorm_int : Integrable (fun t : ℝ =>
      ‖mellin (fun u ↦ (Smooth1 ν ε u : ℂ)) (σ + t * I)‖) :=
    (Bump.verticalIntegrable hε_pos hε_one hσ_pos hσ_le).norm
  -- The product `q/φ(q) · B q χ` is integrable (constant times `B q χ`).
  have hcB_int : ∀ (q : ℕ) (χ : DirichletCharacter ℂ q),
      Integrable (fun t => (q : ℝ) * (q.totient : ℝ)⁻¹ * B q χ t) :=
    fun q χ => (hB_int q χ).const_mul _
  have hsum_int : ∀ (q : ℕ), Integrable (fun t =>
      ∑ χ : DirichletCharacter ℂ q with χ.IsPrimitive, (q : ℝ) * (q.totient : ℝ)⁻¹ * B q χ t) :=
    fun q => integrable_finsetSum _ (fun χ _ => hcB_int q χ)
  -- The Mellin integrand factors out of the double sum:  `G t = D t · ‖𝓜(σ+tI)‖`.
  have hG_eq : ∀ t, summatory (fun q =>
      ∑ χ : DirichletCharacter ℂ q with χ.IsPrimitive,
        (q : ℝ) * (q.totient : ℝ)⁻¹ * B q χ t) Q
      = D t * ‖mellin (fun u ↦ (Smooth1 ν ε u : ℂ)) (σ + t * I)‖ := by
    intro t
    rw [hDdef]
    simp only [B, ← mul_assoc, ← Finset.sum_mul, summatory_mul]
  -- The key swap: finite double sum of integrals = integral of finite double sum.
  have hmain_eq : summatory (fun q =>
      ∑ χ : DirichletCharacter ℂ q with χ.IsPrimitive,
        (q : ℝ) * (q.totient : ℝ)⁻¹ * (Real.exp 1 / (2 * π) * ∫ t : ℝ, B q χ t)) Q
      = (Real.exp 1 / (2 * π)) *
        ∫ t : ℝ, D t * ‖mellin (fun u ↦ (Smooth1 ν ε u : ℂ)) (σ + t * I)‖ := by
    have e1 : ∀ (q : ℕ) (χ : DirichletCharacter ℂ q),
        (q : ℝ) * (q.totient : ℝ)⁻¹ * (Real.exp 1 / (2 * π) * ∫ t : ℝ, B q χ t)
        = (Real.exp 1 / (2 * π)) * ∫ t : ℝ, (q : ℝ) * (q.totient : ℝ)⁻¹ * B q χ t := by
      intro q χ
      rw [MeasureTheory.integral_const_mul]; ring
    simp_rw [e1, ← Finset.mul_sum]
    rw [mul_summatory]
    congr 1
    -- goal: summatory (fun q ↦ ∑*_χ ∫ (q/φq B)) Q = ∫ t, D t · ‖𝓜‖
    simp_rw [← MeasureTheory.integral_finsetSum _ (fun χ _ => hcB_int _ χ)]
    rw [← integral_summatory (fun q _ ↦ hsum_int q)]
    exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hG_eq)
  -- Assemble the chain.
  calc summatory (fun q => ∑ χ : DirichletCharacter ℂ q with χ.IsPrimitive,
          (q : ℝ) * (q.totient : ℝ)⁻¹ * ⨆ y ∈ Icc 1 (x + 1), ‖T ε y χ‖) Q
      ≤ summatory (fun q => ∑ χ : DirichletCharacter ℂ q with χ.IsPrimitive,
          (q : ℝ) * (q.totient : ℝ)⁻¹ * (Real.exp 1 / (2 * π) * ∫ t : ℝ, B q χ t)) Q := by
        apply Finset.sum_le_sum
        intro q hq
        apply Finset.sum_le_sum
        intro χ hχ
        apply mul_le_mul_of_nonneg_left (hsup q χ) (by positivity)
    _ = (Real.exp 1 / (2 * π)) *
          ∫ t : ℝ, D t * ‖mellin (fun u ↦ (Smooth1 ν ε u : ℂ)) (σ + t * I)‖ := hmain_eq
    _ ≤ (Real.exp 1 / (2 * π)) *
          ∫ t : ℝ, Cb * ‖mellin (fun u ↦ (Smooth1 ν ε u : ℂ)) (σ + t * I)‖ := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply MeasureTheory.integral_mono_of_nonneg
        · filter_upwards with t; positivity
        · exact hmnorm_int.const_mul Cb
        · filter_upwards with t
          exact mul_le_mul_of_nonneg_right (hD_le t) (norm_nonneg _)
    _ = (Real.exp 1 / (2 * π)) * Cb *
          ∫ t : ℝ, ‖mellin (fun u ↦ (Smooth1 ν ε u : ℂ)) (σ + t * I)‖ := by
        rw [MeasureTheory.integral_const_mul]; ring
    _ ≤ (Real.exp 1 / (2 * π)) * Cb * (C_J * L) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact mellin_J_bound hε_pos hε_one hσ_pos hσ_le hx rfl hε
    _ = C_LSC * (√(N * M) + √M * Q + √N * Q + Q ^ 2) *
          √(summatory (fun m => ‖f m‖ ^ 2) M) * √(summatory (fun n => ‖g n‖ ^ 2) N) * L := by
        rw [hCbdef]; unfold C_LSC; ring

open _root_.Classical in
theorem summatory_T_ll_nat [Bump] [FG] {ε Q : ℝ} (hε_pos : 0 < ε)(hQ : 1 ≤ Q) {x : ℝ} (hx : 1 ≤ x) (hε : ε = (6 * Real.log 2)⁻¹ * x⁻¹)  :
    summatory (fun q => ∑ χ : DirichletCharacter ℂ q with χ.IsPrimitive, ↑q * (↑q.totient)⁻¹ * ⨆ K ∈ Icc 1 ⌊x⌋₊, ‖T ε (↑K + 2⁻¹) χ‖) Q ≤ C_LSC *
    (√(N * M) + √M * Q + √N * Q + Q ^ 2) * √(summatory (fun m => ‖f m‖ ^ 2) M) * √(summatory (fun n => ‖g n‖ ^ 2) N) * Real.log (x + 1) := by
  trans summatory (fun q => ∑ χ : DirichletCharacter ℂ q with χ.IsPrimitive, ↑q * (↑q.totient)⁻¹ * ⨆ y ∈ Icc 1 (x+1), ‖T ε y χ‖) Q
  · gcongr with q hq hqQ χ hχ
    apply Real.iSup_le _ (by positivity)
    intro K
    apply le_ciSup_of_le (c := K + (2⁻¹ : ℝ))
    · refine bddAbove_range_biSup
        (B := ∑ m ∈ Finset.Ioc 0 ⌊M⌋₊, ∑ n ∈ Finset.Ioc 0 ⌊N⌋₊,
          ‖f m‖ * ‖χ (m : ZMod q)‖ * ‖g n‖ * ‖χ (n : ZMod q)‖)
        (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity) ?_
      intro y hy
      simp only [mem_Icc] at hy
      exact norm_T_le hε_pos hy.1
    by_cases h : K ∈ Icc 1 ⌊x⌋₊
    · have h' : K + (2 : ℝ)⁻¹ ∈ Icc 1 (x+1) := by
        simp only [mem_Icc] at h ⊢
        have : (1 : ℝ) ≤ K := by
          exact_mod_cast h.1
        have : (K : ℝ) ≤ x := by
          grw [h.2]
          apply Nat.floor_le
          positivity
        grind
      simp only [h, h', ciSup_unique]
      rfl
    · simp only [h, iSup_of_isEmpty, mem_Icc]
      positivity
  apply summatory_T_ll hε_pos hQ hx hε

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
    · positivity
  apply_fun Nat.ceil (α := ℝ) at h
  · simp only [Nat.ceil_natCast] at h
    rw [add_comm, Nat.ceil_add_natCast] at h
    · grind
    · positivity
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
        apply Nat.le_of_le_add_real (by positivity) (by norm_num) h
      grw [hε, this]
      have : 0 < x + 1 := by positivity
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
        apply Nat.le_of_add_real_le (by positivity) (by norm_num) h.le
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
        grind
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
  have h := FG.summatory_mul (fg := inst) (y := y)
  unfold inst at h
  simpa only [← ArithmeticFunction.mul_twist, twist_apply, Algebra.algebraMap_self,
    RingHom.id_apply, mul_assoc] using h


theorem LargeSieve_convolution_aux [Bump] [fg : FG]
    {x Q : ℝ} (hx : 1 ≤ x) (hQ : 1 ≤ Q) :
  open Classical in
    summatory (fun q ↦ ∑ χ : DirichletCharacter ℂ q with χ.IsPrimitive,
      q * (q.totient : ℝ)⁻¹ * ⨆ y ∈ Set.Icc 1 x, ‖summatory (fun n ↦ (f * g) n * χ n) y‖) Q
      ≤ C_LSC * (√(N * M) + √M * Q + √N * Q + Q^2) *
      √(summatory (fun m ↦ ‖f m‖^2) M) * √(summatory (fun n ↦ ‖g n‖ ^ 2) N) * Real.log (x + 1) := by
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
      · positivity
      · exact_mod_cast hK.1
      · positivity
    _ ≤ _ := by
      grw [summatory_T_ll_nat _ (by grind) hx]
      simp [ε]
      positivity

end Flat
