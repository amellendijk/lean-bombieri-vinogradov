import Mathlib

import PrimeNumberTheoremAnd.SmoothExistence

import BV.Mellin
import BV.Delta


/-
Some token numbers from Opus:
 Session
 Total cost:            $35.38
 Total duration (API):  1h 17m 2s
 Total duration (wall): 1d 5h 4m
 Total code changes:    987 lines added, 149 lines removed
 Usage by model:
     claude-haiku-4-5:  1.6k input, 57 output, 0 cache read, 0 cache write ($0.0019)
      claude-opus-4-8:  17.0k input, 379.3k output, 30.2m cache read, 1.1m cache write ($35.38)

Note: There is a sloppish sorry-free version of this file on the branch claude-fable.
-/

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
  have hy0 : (0 : ℝ) < y := by linarith
  rw [T, summatory_apply]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun m hm => ?_)
  simp only [Finset.mem_Ioc] at hm
  rw [summatory_apply]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun n hn => ?_)
  simp only [Finset.mem_Ioc] at hn
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm.1
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn.1
  have hpos : 0 < (m : ℝ) * n / y := by positivity
  have hs1 : ‖(↑(Smooth1 ν ε ((m : ℝ) * n / y)) : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Smooth1Nonneg (fun x _ => νpos x) hpos hε_pos)]
    exact Smooth1LeOne (fun x _ => νpos x)
      (by rw [← MeasureTheory.integral_Ici_eq_integral_Ioi]; exact mass_one) hε_pos hpos
  rw [norm_mul, norm_mul, norm_mul, norm_mul]
  exact mul_le_of_le_one_right (by positivity) hs1

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
    · refine bddAbove_range_biSup (B := summatory (fun m => ‖f m‖) x)
        (by positivity) ?_
      intro K hK
      simp only [Finset.coe_Icc, mem_Icc] at hK
      exact norm_summatory_le (by rw [hfloor_add_half]; exact hK.2)
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
  have hy0 : (0 : ℝ) < y := by linarith
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
        have hcpow : ‖(1 / (y : ℂ)) ^ (-(σ + t * I))‖ = y ^ σ := by
          rw [show (1 / (y : ℂ)) = ((1 / y : ℝ) : ℂ) by push_cast; ring,
            Complex.norm_cpow_eq_rpow_re_of_pos (by positivity)]
          simp only [neg_re, add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one,
            sub_zero, add_zero]
          rw [one_div, Real.inv_rpow hy0.le, ← Real.rpow_neg hy0.le, neg_neg]
        rw [hcpow]; ring
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
    ext x; simp [Set.mem_Ioi]
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
    ext t
    simp only [Set.mem_compl_iff, Set.mem_Icc, not_and_or, not_le, Set.mem_union, Set.mem_Iio,
      Set.mem_Ioi]
  rw [hcompl, setIntegral_union ?_ measurableSet_Ioi (integrableOn_Iio_inv_sq hT)
      (integrableOn_Ioi_inv_sq hT), integral_Iio_inv_sq hT, integral_Ioi_inv_sq hT]
  · ring
  · rw [Set.disjoint_left]
    intro a ha hb
    simp only [Set.mem_Iio, Set.mem_Ioi] at ha hb
    linarith

/-- `∫_{0}^{T} (σ+t)⁻¹ = log(σ+T) - log σ` for `σ > 0`, `T ≥ 0`. -/
private lemma integral_inv_shift {σ T : ℝ} (hσ : 0 < σ) (hT : 0 ≤ T) :
    ∫ t in (0 : ℝ)..T, (σ + t)⁻¹ = Real.log (σ + T) - Real.log σ := by
  have hderiv : ∀ t ∈ Set.uIcc (0 : ℝ) T, HasDerivAt (fun s => Real.log (σ + s)) (σ + t)⁻¹ t := by
    intro t ht
    rw [Set.uIcc_of_le hT, Set.mem_Icc] at ht
    have hpos : 0 < σ + t := by linarith [ht.1]
    have := (Real.hasDerivAt_log hpos.ne').comp t
      ((hasDerivAt_const t σ).add (hasDerivAt_id t))
    convert! this using 1 <;> ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv ?_]
  · simp
  · apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.inv₀
    · fun_prop
    · intro t ht
      rw [Set.uIcc_of_le hT, Set.mem_Icc] at ht
      have : 0 < σ + t := by linarith [ht.1]
      exact this.ne'

/-- `∫_{[-T,T]} (σ+|t|)⁻¹ = 2(log(σ+T) - log σ)` for `σ > 0`, `T ≥ 0`. -/
private lemma integral_Icc_inv_abs {σ T : ℝ} (hσ : 0 < σ) (hT : 0 ≤ T) :
    ∫ t in Set.Icc (-T) T, (σ + |t|)⁻¹ = 2 * (Real.log (σ + T) - Real.log σ) := by
  have hcont : Continuous (fun t : ℝ => (σ + |t|)⁻¹) := by
    apply Continuous.inv₀
    · fun_prop
    · intro t; exact (by positivity : (0 : ℝ) < σ + |t|).ne'
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
    have hcongr : ∫ t in (-T : ℝ)..0, (σ + |t|)⁻¹ = ∫ t in (-T : ℝ)..0, (σ - t)⁻¹ := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [Set.uIcc_of_le (by linarith : -T ≤ (0 : ℝ)), Set.mem_Icc] at ht
      show (σ + |t|)⁻¹ = (σ - t)⁻¹
      rw [abs_of_nonpos ht.2, ← sub_eq_add_neg]
    rw [hcongr]
    have hderiv : ∀ t ∈ Set.uIcc (-T : ℝ) 0,
        HasDerivAt (fun s => -Real.log (σ - s)) (σ - t)⁻¹ t := by
      intro t ht
      rw [Set.uIcc_of_le (by linarith : -T ≤ (0 : ℝ)), Set.mem_Icc] at ht
      have hpos : 0 < σ - t := by linarith [ht.2]
      have := ((Real.hasDerivAt_log hpos.ne').comp t
        ((hasDerivAt_const t σ).sub (hasDerivAt_id t))).neg
      convert! this using 1 <;> ring
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv ?_]
    · simp only [sub_zero, sub_neg_eq_add]; ring
    · apply ContinuousOn.intervalIntegrable
      apply ContinuousOn.inv₀
      · fun_prop
      · intro t ht
        rw [Set.uIcc_of_le (by linarith : -T ≤ (0 : ℝ)), Set.mem_Icc] at ht
        exact (by linarith [ht.2] : (0 : ℝ) < σ - t).ne'
  rw [hleft, hright]; ring

/-- Bound A of Step 4: on the vertical line `Re s = σ` with `0 < σ ≤ 2` and `0 < ε < 1`, the
Mellin transform of `Smooth1 ν ε` decays like `1/‖s‖`, with a constant depending only on `ν`.
Combines `MellinOfSmooth1a` with the strip bound `mellin_bump_bounded`. -/
lemma exists_mellin_smooth1_boundA [Bump] :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (ε σ t : ℝ), 0 < ε → ε < 1 → 0 < σ → σ ≤ 2 →
      ‖mellin (fun u ↦ (Smooth1 ν ε u : ℂ)) ((σ : ℂ) + t * I)‖
        ≤ C * ‖(σ : ℂ) + t * I‖⁻¹ := by
  obtain ⟨C, hC⟩ := (mellin_bump_bounded (σ₁ := 0) (σ₂ := 2) (by norm_num)
    (diffν.of_le (by simp)) suppν).bound
  rw [Filter.eventually_principal] at hC
  simp only [mem_setOf_eq, norm_one, mul_one] at hC
  have hCnonneg : 0 ≤ C := le_trans (norm_nonneg _) (hC (1 : ℂ) (by simp))
  refine ⟨C, hCnonneg, fun ε σ t hε hε1 hσ hσ2 ↦ ?_⟩
  have hsre : ((σ : ℂ) + t * I).re = σ := by simp
  rw [MellinOfSmooth1a (diffν.of_le (by simp)) suppν hε (by rw [hsre]; exact hσ),
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
  have hxpos : 0 < x := by linarith
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
  calc Real.log (1 + 6 * Real.log 2 * x * L)
      ≤ Real.log (1 + x) + Real.log (1 + 6 * Real.log 2 * L) := h1
    _ ≤ L + 6 * Real.log 2 * L := by rw [h2]; linarith
    _ = (1 + 6 * Real.log 2) * L := by ring

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
  -- The left-hand side of the large sieve is a sum of nonnegative terms.
  have key : (0 : ℝ) ≤ C_LS * ((1 : ℕ) + (1 : ℝ) ^ 2) *
      ∑ n ∈ Finset.Ioc (0 : ℤ) (0 + (1 : ℕ)), ‖(if n = 1 then (1 : ℂ) else 0)‖ ^ 2 := by
    refine le_trans ?_ h
    apply Finset.sum_nonneg; intro q _
    apply Finset.sum_nonneg; intro χ _
    positivity
  have hS : (∑ n ∈ Finset.Ioc (0 : ℤ) (0 + (1 : ℕ)), ‖(if n = 1 then (1 : ℂ) else 0)‖ ^ 2) = 1 := by
    rw [show Finset.Ioc (0 : ℤ) (0 + (1 : ℕ)) = {1} from by decide, Finset.sum_singleton]
    norm_num
  rw [hS] at key
  nlinarith [key]

/-- Reindex a sum over the integer interval `(0, k]` as a sum over the natural-number
interval `(0, k]` via the cast `ℕ → ℤ`. -/
lemma sum_Ioc_natCast {R : Type*} [AddCommMonoid R] (k : ℕ) (G : ℤ → R) :
    ∑ n ∈ Finset.Ioc (0 : ℤ) (k : ℤ), G n = ∑ m ∈ Finset.Ioc (0 : ℕ) k, G (m : ℤ) := by
  apply Finset.sum_nbij' (i := fun n : ℤ => n.toNat) (j := fun m : ℕ => (m : ℤ))
  · intro a ha; simp only [Finset.mem_Ioc] at ha ⊢; omega
  · intro a ha; simp only [Finset.mem_Ioc] at ha ⊢; omega
  · intro a ha; simp only [Finset.mem_Ioc] at ha; omega
  · intro a ha; simp only [Finset.mem_Ioc] at ha; omega
  · intro a ha; simp only [Finset.mem_Ioc] at ha; congr 1; omega

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
  · -- `⌊P⌋₊ = 0`: every inner sum is empty, both sides are zero.
    have hS0 : summatory (fun m ↦ ‖h m‖ ^ 2) P = 0 := by rw [summatory_apply, hP0]; simp
    have hT0 : ∀ (q : ℕ) (χ : DirichletCharacter ℂ q),
        summatory (fun m ↦ h m * χ m * (m : ℂ) ^ (-(σ + t * I))) P = 0 := by
      intro q χ; rw [summatory_apply, hP0]; simp
    simp only [hT0, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_pow, mul_zero, Finset.sum_const_zero]
    rw [hS0]; simp
  -- `⌊P⌋₊ > 0`: apply the large sieve.
  have hP1 : (1 : ℝ) ≤ P := Nat.floor_pos.mp hPpos
  have hPnn : (0 : ℝ) ≤ P := by linarith
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
    rw [Complex.norm_natCast_cpow_of_pos (by omega)]
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
          apply Finset.sum_congr rfl
          intro q hq
          apply Finset.sum_congr rfl
          intro χ hχ
          rw [ha q χ]
    _ ≤ C_LS * ((⌊P⌋₊ : ℝ) + Q ^ 2) * ∑ n ∈ Finset.Ioc (0 : ℤ) (⌊P⌋₊ : ℤ), ‖c n‖ ^ 2 := hLS
    _ ≤ C_LS * ((⌊P⌋₊ : ℝ) + Q ^ 2) * summatory (fun m ↦ ‖h m‖ ^ 2) P := by
          apply mul_le_mul_of_nonneg_left hb
          have : (0 : ℝ) ≤ (⌊P⌋₊ : ℝ) + Q ^ 2 := by positivity
          positivity
    _ ≤ C_LS * (P + Q ^ 2) * summatory (fun m ↦ ‖h m‖ ^ 2) P := by
          apply mul_le_mul_of_nonneg_right _ hSnn
          have : (⌊P⌋₊ : ℝ) ≤ P := Nat.floor_le hPnn
          gcongr

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
  rw [summatory_apply]
  set Sf : ℝ := summatory (fun m ↦ ‖f m‖ ^ 2) M with hSf
  set Sg : ℝ := summatory (fun n ↦ ‖g n‖ ^ 2) N with hSg
  have hSfnn : 0 ≤ Sf := summatory_nonneg _ _ (fun n _ => by positivity)
  have hSgnn : 0 ≤ Sg := summatory_nonneg _ _ (fun n _ => by positivity)
  -- the sigma index set of pairs `(q, χ)` with `χ` primitive
  set s : Finset (Σ q : ℕ, DirichletCharacter ℂ q) :=
    (Finset.Ioc 0 ⌊Q⌋₊).sigma
      (fun q => Finset.univ.filter (fun χ : DirichletCharacter ℂ q => χ.IsPrimitive)) with hs
  -- the Cauchy–Schwarz vectors `√(q/φq)·‖F‖` and `√(q/φq)·‖G‖`
  set aF : (Σ q : ℕ, DirichletCharacter ℂ q) → ℝ := fun p =>
    Real.sqrt ((p.1 : ℝ) * (p.1.totient : ℝ)⁻¹) *
      ‖summatory (fun m ↦ f m * p.2 m * (m : ℂ) ^ (-(σ + t * I))) M‖ with haF
  set aG : (Σ q : ℕ, DirichletCharacter ℂ q) → ℝ := fun p =>
    Real.sqrt ((p.1 : ℝ) * (p.1.totient : ℝ)⁻¹) *
      ‖summatory (fun n ↦ g n * p.2 n * (n : ℂ) ^ (-(σ + t * I))) N‖ with haG
  -- LHS as a single sum over `s`
  have eLHS : (∑ q ∈ Finset.Ioc 0 ⌊Q⌋₊, ∑ χ : DirichletCharacter ℂ q with χ.IsPrimitive,
      (q : ℝ) * (q.totient : ℝ)⁻¹ *
      (‖summatory (fun m ↦ f m * χ m * (m : ℂ) ^ (-(σ + t * I))) M‖ *
       ‖summatory (fun n ↦ g n * χ n * (n : ℂ) ^ (-(σ + t * I))) N‖))
      = ∑ p ∈ s, aF p * aG p := by
    rw [Finset.sum_sigma', hs]
    apply Finset.sum_congr rfl; intro p _
    simp only [haF, haG]
    symm
    rw [mul_mul_mul_comm, Real.mul_self_sqrt (by positivity)]
  have eF : (∑ q ∈ Finset.Ioc 0 ⌊Q⌋₊, ∑ χ : DirichletCharacter ℂ q with χ.IsPrimitive,
      (q : ℝ) * (q.totient : ℝ)⁻¹ *
        ‖summatory (fun m ↦ f m * χ m * (m : ℂ) ^ (-(σ + t * I))) M‖ ^ 2)
      = ∑ p ∈ s, aF p ^ 2 := by
    rw [Finset.sum_sigma', hs]
    apply Finset.sum_congr rfl; intro p _
    simp only [haF]
    rw [mul_pow, Real.sq_sqrt (by positivity)]
  have eG : (∑ q ∈ Finset.Ioc 0 ⌊Q⌋₊, ∑ χ : DirichletCharacter ℂ q with χ.IsPrimitive,
      (q : ℝ) * (q.totient : ℝ)⁻¹ *
        ‖summatory (fun n ↦ g n * χ n * (n : ℂ) ^ (-(σ + t * I))) N‖ ^ 2)
      = ∑ p ∈ s, aG p ^ 2 := by
    rw [Finset.sum_sigma', hs]
    apply Finset.sum_congr rfl; intro p _
    simp only [haG]
    rw [mul_pow, Real.sq_sqrt (by positivity)]
  rw [eLHS]
  -- nonnegativity of the CS sum
  have hLHSnn : 0 ≤ ∑ p ∈ s, aF p * aG p :=
    Finset.sum_nonneg (fun p _ => by simp only [haF, haG]; positivity)
  -- the two large-sieve bounds
  have hSFle : ∑ p ∈ s, aF p ^ 2 ≤ C_LS * (M + Q ^ 2) * Sf := by
    rw [← eF, hSf]; exact largeSieve_factor hQ hσ_pos t (⇑f) M
  have hSGle : ∑ p ∈ s, aG p ^ 2 ≤ C_LS * (N + Q ^ 2) * Sg := by
    rw [← eG, hSg]; exact largeSieve_factor hQ hσ_pos t (⇑g) N
  have hAFnn : 0 ≤ C_LS * (M + Q ^ 2) * Sf :=
    le_trans (Finset.sum_nonneg (fun p _ => sq_nonneg _)) hSFle
  -- Cauchy–Schwarz, then the large sieve bounds
  have hsq : (∑ p ∈ s, aF p * aG p) ^ 2 ≤
      (C_LS * (M + Q ^ 2) * Sf) * (C_LS * (N + Q ^ 2) * Sg) :=
    (Finset.sum_mul_sq_le_sq_mul_sq s aF aG).trans
      (mul_le_mul hSFle hSGle (Finset.sum_nonneg (fun p _ => sq_nonneg _)) hAFnn)
  -- the constant comparison `√((M+Q²)(N+Q²)) ≤ √(NM)+√M Q+√N Q+Q²`
  have hQ0 : (0 : ℝ) ≤ Q := by linarith
  have hM := hM_pos.le
  have hN := hN_pos.le
  have hκ : (M + Q ^ 2) * (N + Q ^ 2)
      ≤ (√(N * M) + √M * Q + √N * Q + Q ^ 2) ^ 2 := by
    have ha := Real.sqrt_nonneg M
    have hb := Real.sqrt_nonneg N
    have e1 : √M ^ 2 = M := Real.sq_sqrt hM
    have e2 : √N ^ 2 = N := Real.sq_sqrt hN
    have e3 : √(N * M) = √N * √M := Real.sqrt_mul hN M
    rw [e3]
    nlinarith [e1, e2, ha, hb, hQ0, mul_nonneg ha hQ0, mul_nonneg hb hQ0,
      mul_nonneg ha hb, mul_nonneg (mul_nonneg ha hb) hQ0, sq_nonneg Q]
  -- the RHS is nonnegative and its square dominates `AF·AG`
  have hκnn : 0 ≤ √(N * M) + √M * Q + √N * Q + Q ^ 2 :=
    add_nonneg (add_nonneg (add_nonneg (Real.sqrt_nonneg _)
      (mul_nonneg (Real.sqrt_nonneg _) hQ0)) (mul_nonneg (Real.sqrt_nonneg _) hQ0)) (sq_nonneg _)
  have hRHSnn : 0 ≤ C_LS * (√(N * M) + √M * Q + √N * Q + Q ^ 2) * √Sf * √Sg :=
    mul_nonneg (mul_nonneg (mul_nonneg C_LS_nonneg hκnn) (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)
  have hfin : (C_LS * (M + Q ^ 2) * Sf) * (C_LS * (N + Q ^ 2) * Sg)
      ≤ (C_LS * (√(N * M) + √M * Q + √N * Q + Q ^ 2) * √Sf * √Sg) ^ 2 := by
    have hRHS2 : (C_LS * (√(N * M) + √M * Q + √N * Q + Q ^ 2) * √Sf * √Sg) ^ 2
        = C_LS ^ 2 * (√(N * M) + √M * Q + √N * Q + Q ^ 2) ^ 2 * Sf * Sg := by
      rw [mul_pow, mul_pow, mul_pow, Real.sq_sqrt hSfnn, Real.sq_sqrt hSgnn]
    rw [hRHS2]
    nlinarith [hκ, sq_nonneg C_LS, hSfnn, hSgnn, mul_nonneg hSfnn hSgnn,
      mul_nonneg (mul_nonneg (sq_nonneg C_LS) hSfnn) hSgnn]
  -- conclude
  have key : (∑ p ∈ s, aF p * aG p) ^ 2
      ≤ (C_LS * (√(N * M) + √M * Q + √N * Q + Q ^ 2) * √Sf * √Sg) ^ 2 := hsq.trans hfin
  have := Real.sqrt_le_sqrt key
  rwa [Real.sqrt_sq hLHSnn, Real.sqrt_sq hRHSnn] at this

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
    rw [hL]; exact Real.log_le_log (by norm_num) (by linarith)
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
    Smooth1_verticalIntegrable (diffν.of_le (by simp)) (fun x _ => νpos x) suppν
      (by rw [← MeasureTheory.integral_Ici_eq_integral_Ioi]; exact mass_one)
      hε_pos hε_one hσ_pos hσ
  have hInt : Integrable (fun t : ℝ ↦ ‖mellin (fun u ↦ (Smooth1 ν ε u : ℂ)) (σ + t * I)‖) :=
    hVI.norm
  -- centre estimate `∫_{|t|≤T} ≤ 2√2 (1+6 log 2) CA · L`
  have hcenter_log : Real.log (σ + T) - Real.log σ ≤ (1 + 6 * Real.log 2) * L := by
    rw [← Real.log_div (by positivity) hσ_pos.ne']
    have hTσ : (σ + T) / σ = 1 + 6 * Real.log 2 * x * L := by
      have hx0 : x ≠ 0 := by linarith
      have hl2 : Real.log 2 ≠ 0 := hlog2.ne'
      have hL0 : L ≠ 0 := hL_pos.ne'
      rw [hTdef, hσx, hε]
      field_simp
    rw [hTσ]
    exact log_one_add_le hx hL
  have hcenter : ∫ t in Set.Icc (-T) T, ‖mellin (fun u ↦ (Smooth1 ν ε u : ℂ)) (σ + t * I)‖
      ≤ 2 * Real.sqrt 2 * (1 + 6 * Real.log 2) * CA * L := by
    have hmaj_cont : Continuous (fun t : ℝ => (Real.sqrt 2 * CA) * (σ + |t|)⁻¹) := by
      apply Continuous.mul continuous_const
      apply Continuous.inv₀
      · fun_prop
      · intro t; exact (by positivity : (0 : ℝ) < σ + |t|).ne'
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
          exact mul_le_mul_of_nonneg_left hcenter_log (by norm_num)
      _ = 2 * Real.sqrt 2 * (1 + 6 * Real.log 2) * CA * L := by ring
  -- tail estimate `∫_{|t|>T} ≤ 2 CB ≤ (2 CB / log 2) · L`
  have htail : ∫ t in (Set.Icc (-T) T)ᶜ, ‖mellin (fun u ↦ (Smooth1 ν ε u : ℂ)) (σ + t * I)‖
      ≤ 2 * CB / Real.log 2 * L := by
    have hmaj_compl : MeasureTheory.IntegrableOn (fun t : ℝ => (t ^ 2)⁻¹) (Set.Icc (-T) T)ᶜ := by
      have hcompl : (Set.Icc (-T) T)ᶜ = Set.Iio (-T) ∪ Set.Ioi T := by
        ext t; simp only [Set.mem_compl_iff, Set.mem_Icc, not_and_or, not_le, Set.mem_union,
          Set.mem_Iio, Set.mem_Ioi]
      rw [hcompl]
      exact (integrableOn_Iio_inv_sq hT_pos).union (integrableOn_Ioi_inv_sq hT_pos)
    calc ∫ t in (Set.Icc (-T) T)ᶜ, ‖mellin (fun u ↦ (Smooth1 ν ε u : ℂ)) (σ + t * I)‖
        ≤ ∫ t in (Set.Icc (-T) T)ᶜ, (CB / ε) * (t ^ 2)⁻¹ := by
          apply setIntegral_mono_on hInt.integrableOn (hmaj_compl.const_mul (CB / ε))
            measurableSet_Icc.compl
          intro t ht
          have htabs : T < |t| := by
            simp only [Set.mem_compl_iff, Set.mem_Icc, not_and_or, not_le] at ht
            rcases ht with h | h
            · rw [abs_of_neg (by linarith)]; linarith
            · rw [abs_of_pos (by linarith)]; linarith
          have htne : t ≠ 0 := by
            intro h; rw [h, abs_zero] at htabs; linarith
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
            _ = (CB / ε) * (t ^ 2)⁻¹ := by rw [mul_inv]; ring
      _ = (CB / ε) * ∫ t in (Set.Icc (-T) T)ᶜ, (t ^ 2)⁻¹ := MeasureTheory.integral_const_mul _ _
      _ = (CB / ε) * (2 * T⁻¹) := by rw [integral_compl_Icc_inv_sq hT_pos]
      _ = 2 * CB := by rw [hTdef, inv_inv]; field_simp
      _ ≤ 2 * CB / Real.log 2 * L := by
          have hLratio : 1 ≤ L / Real.log 2 := by
            rw [le_div_iff₀ hlog2]; linarith
          calc 2 * CB = 2 * CB * 1 := by ring
            _ ≤ 2 * CB * (L / Real.log 2) :=
                mul_le_mul_of_nonneg_left hLratio (mul_nonneg (by norm_num) hCB_pos.le)
            _ = 2 * CB / Real.log 2 * L := by ring
  -- assemble
  rw [← MeasureTheory.integral_add_compl (measurableSet_Icc (a := -T) (b := T)) hInt]
  refine le_trans (add_le_add hcenter htail) (le_of_eq ?_)
  ring

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
  classical
  -- The Mellin factor is vertically integrable.
  have hVI : Integrable (fun t : ℝ ↦ mellin (fun u ↦ (Smooth1 ν ε u : ℂ)) (σ + t * I)) :=
    Smooth1_verticalIntegrable (diffν.of_le (by simp)) (fun x _ => νpos x) suppν
      (by rw [← MeasureTheory.integral_Ici_eq_integral_Ioi]; exact mass_one)
      hε_pos hε_one hσ_pos hσ
  -- Each partial Dirichlet sum is continuous and bounded in `t`.
  have key : ∀ (c : ℕ → ℂ) (P : ℝ),
      Continuous (fun t : ℝ ↦ summatory (fun m ↦ c m * χ m * (m : ℂ) ^ (-(σ + t * I))) P) ∧
      ∃ C : ℝ, ∀ t : ℝ,
        ‖summatory (fun m ↦ c m * χ m * (m : ℂ) ^ (-(σ + t * I))) P‖ ≤ C := by
    intro c P
    have hexp : Continuous (fun t : ℝ ↦ (-(↑σ + ↑t * I) : ℂ)) := by fun_prop
    have hcont : Continuous
        (fun t : ℝ ↦ summatory (fun m ↦ c m * χ m * (m : ℂ) ^ (-(σ + t * I))) P) := by
      simp_rw [summatory_apply]
      apply continuous_finset_sum
      intro m hm
      simp only [Finset.mem_Ioc] at hm
      exact continuous_const.mul
        (hexp.const_cpow (Or.inl (by exact_mod_cast (show (0 : ℕ) < m by omega).ne')))
    refine ⟨hcont, summatory (fun m ↦ ‖c m‖ * ‖χ (m : ZMod q)‖ * (m : ℝ) ^ (-σ)) P, fun t ↦ ?_⟩
    rw [summatory_apply, summatory_apply]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun m hm ↦ le_of_eq ?_)
    simp only [Finset.mem_Ioc] at hm
    rw [norm_mul, norm_mul, Complex.norm_natCast_cpow_of_pos (by omega)]
    simp only [neg_re, add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one,
      sub_zero, add_zero]
  obtain ⟨hFcont, C_F, hF_bound⟩ := key (fun m ↦ f m) M
  obtain ⟨hGcont, C_G, hG_bound⟩ := key (fun n ↦ g n) N
  -- `‖F_t‖·‖G_t‖` is continuous and bounded; multiply by the integrable Mellin norm.
  have hbound : ∀ t : ℝ, ‖(fun t ↦ ‖summatory (fun m ↦ (f m) * χ m * (m : ℂ) ^ (-(σ + t * I))) M‖ *
        ‖summatory (fun n ↦ (g n) * χ n * (n : ℂ) ^ (-(σ + t * I))) N‖) t‖ ≤ C_F * C_G := by
    intro t
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact mul_le_mul (hF_bound t) (hG_bound t) (norm_nonneg _)
      (le_trans (norm_nonneg _) (hF_bound 0))
  exact hVI.norm.bdd_mul (hFcont.norm.mul hGcont.norm).aestronglyMeasurable
    (Filter.Eventually.of_forall hbound)

open _root_.Classical in
theorem summatory_T_ll [Bump] [FG] {ε Q : ℝ} (hε_pos : 0 < ε) (hQ : 1 ≤ Q)
    {x : ℝ} (hx : 1 ≤ x) (hε : ε = (6 * Real.log 2)⁻¹ * x⁻¹)  :
    summatory (fun q => ∑ χ : DirichletCharacter ℂ q with χ.IsPrimitive, ↑q * (↑q.totient)⁻¹ * ⨆ y ∈ Icc 1 (x+1), ‖T ε y χ‖) Q ≤ C_LSC *
    (√(N * M) + √M * Q + √N * Q + Q ^ 2) * √(summatory (fun m => ‖f m‖ ^ 2) M) * √(summatory (fun n => ‖g n‖ ^ 2) N) * Real.log (x + 1) := by
  classical
  have hlog2 := Real.log_two_gt_d9
  -- `ε < 1` is automatic: `ε = (6 log 2)⁻¹ x⁻¹ ≤ (6 log 2)⁻¹ < 1`.
  have hε_one : ε < 1 := by
    have hx' : x⁻¹ ≤ 1 := by rw [inv_le_one₀ (by linarith)]; exact hx
    calc ε ≤ (6 * Real.log 2)⁻¹ * x⁻¹ := hε.le
      _ ≤ (6 * Real.log 2)⁻¹ * 1 := by gcongr
      _ < 1 := by rw [mul_one, inv_lt_one₀ (by positivity)]; nlinarith
  -- Set `σ = 1/log(x+1)`, so `0 < σ ≤ 2` and `y^σ ≤ (x+1)^σ = e` for `y ≤ x+1`.
  set L := Real.log (x + 1) with hL
  have hx1 : (1 : ℝ) < x + 1 := by linarith
  have hL_pos : 0 < L := Real.log_pos hx1
  set σ : ℝ := L⁻¹ with hσdef
  have hσ_pos : 0 < σ := by positivity
  have hL_ge : Real.log 2 ≤ L := Real.log_le_log (by norm_num) (by linarith)
  have hσ_le : σ ≤ 2 := by
    rw [hσdef, inv_le_comm₀ hL_pos (by norm_num)]
    linarith
  -- `(x+1)^σ = e`, hence `y^σ ≤ e` for `1 ≤ y ≤ x+1`.
  have hxσ : (x + 1) ^ σ = Real.exp 1 := by
    rw [Real.rpow_def_of_pos (by linarith), hσdef, ← hL, mul_inv_cancel₀ hL_pos.ne']
  -- Abbreviation for the (nonnegative) integrand.
  let B : ∀ (q : ℕ), DirichletCharacter ℂ q → ℝ → ℝ := fun q χ t =>
    ‖summatory (fun m ↦ f m * χ m * (m : ℂ) ^ (-(σ + t * I))) M‖ *
      ‖summatory (fun n ↦ g n * χ n * (n : ℂ) ^ (-(σ + t * I))) N‖ *
      ‖mellin (fun u ↦ (Smooth1 ν ε u : ℂ)) (σ + t * I)‖
  have hB_nonneg : ∀ (q : ℕ) (χ : DirichletCharacter ℂ q) (t : ℝ), 0 ≤ B q χ t := by
    intro q χ t
    show 0 ≤ ‖_‖ * ‖_‖ * ‖_‖
    positivity
  have hB_int : ∀ (q : ℕ) (χ : DirichletCharacter ℂ q), Integrable (B q χ) :=
    fun q χ => integrable_norm_FG_mellin hε_pos hε_one hσ_pos hσ_le
  -- Step 1 & 3: per-character bound, using `T_norm_le_integral` and `y^σ ≤ e`.
  have hsup : ∀ (q : ℕ) (χ : DirichletCharacter ℂ q),
      (⨆ y ∈ Icc 1 (x + 1), ‖T ε y χ‖) ≤ (Real.exp 1 / (2 * π)) * ∫ t : ℝ, B q χ t := by
    intro q χ
    have hI_nonneg : 0 ≤ ∫ t : ℝ, B q χ t :=
      MeasureTheory.integral_nonneg (fun t => hB_nonneg q χ t)
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
  have hBeq : ∀ (q : ℕ) (χ : DirichletCharacter ℂ q) (t : ℝ), B q χ t =
      (‖summatory (fun m ↦ f m * χ m * (m : ℂ) ^ (-(σ + t * I))) M‖ *
       ‖summatory (fun n ↦ g n * χ n * (n : ℂ) ^ (-(σ + t * I))) N‖) *
      ‖mellin (fun u ↦ (Smooth1 ν ε u : ℂ)) (σ + t * I)‖ := fun q χ t => by
    show _ * _ * _ = _ * _ * _; ring
  -- `D t` is the large-sieve double sum at parameter `t` (without the Mellin factor).
  set D : ℝ → ℝ := fun t => summatory (fun q =>
    ∑ χ : DirichletCharacter ℂ q with χ.IsPrimitive,
      (q : ℝ) * (q.totient : ℝ)⁻¹ *
      (‖summatory (fun m ↦ f m * χ m * (m : ℂ) ^ (-(σ + t * I))) M‖ *
       ‖summatory (fun n ↦ g n * χ n * (n : ℂ) ^ (-(σ + t * I))) N‖)) Q with hDdef
  set Cb : ℝ := C_LS * (√(N * M) + √M * Q + √N * Q + Q ^ 2) *
    √(summatory (fun m ↦ ‖f m‖ ^ 2) M) * √(summatory (fun n ↦ ‖g n‖ ^ 2) N) with hCbdef
  have hD_le : ∀ t, D t ≤ Cb := fun t => largeSieve_char_bound hQ hσ_pos t
  have hD_nonneg : ∀ t, 0 ≤ D t := by
    intro t
    apply summatory_nonneg
    intro q hq
    apply Finset.sum_nonneg
    intro χ hχ
    positivity
  have hCb_nonneg : 0 ≤ Cb := le_trans (hD_nonneg 0) (hD_le 0)
  have hmnorm_int : Integrable (fun t : ℝ =>
      ‖mellin (fun u ↦ (Smooth1 ν ε u : ℂ)) (σ + t * I)‖) := by
    have hVI : Integrable (fun t : ℝ =>
        mellin (fun u ↦ (Smooth1 ν ε u : ℂ)) (σ + t * I)) :=
      Smooth1_verticalIntegrable (diffν.of_le (by simp)) (fun x _ => νpos x) suppν
        (by rw [← MeasureTheory.integral_Ici_eq_integral_Ioi]; exact mass_one)
        hε_pos hε_one hσ_pos hσ_le
    exact hVI.norm
  -- The product `q/φ(q) · B q χ` is integrable (constant times `B q χ`).
  have hcB_int : ∀ (q : ℕ) (χ : DirichletCharacter ℂ q),
      Integrable (fun t => (q : ℝ) * (q.totient : ℝ)⁻¹ * B q χ t) :=
    fun q χ => (hB_int q χ).const_mul _
  have hsum_int : ∀ (q : ℕ), Integrable (fun t =>
      ∑ χ : DirichletCharacter ℂ q with χ.IsPrimitive, (q : ℝ) * (q.totient : ℝ)⁻¹ * B q χ t) :=
    fun q => integrable_finset_sum _ (fun χ _ => hcB_int q χ)
  -- The Mellin integrand factors out of the double sum:  `G t = D t · ‖𝓜(σ+tI)‖`.
  have hG_eq : ∀ t, summatory (fun q =>
      ∑ χ : DirichletCharacter ℂ q with χ.IsPrimitive,
        (q : ℝ) * (q.totient : ℝ)⁻¹ * B q χ t) Q
      = D t * ‖mellin (fun u ↦ (Smooth1 ν ε u : ℂ)) (σ + t * I)‖ := by
    intro t
    rw [hDdef]
    simp only [hBeq, ← mul_assoc, ← Finset.sum_mul, summatory_mul]
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
    simp_rw [← MeasureTheory.integral_finset_sum _ (fun χ _ => hcB_int _ χ)]
    rw [show summatory (fun q => ∫ t : ℝ, ∑ χ : DirichletCharacter ℂ q with χ.IsPrimitive,
            (q : ℝ) * (q.totient : ℝ)⁻¹ * B q χ t) Q
          = ∫ t : ℝ, summatory (fun q => ∑ χ : DirichletCharacter ℂ q with χ.IsPrimitive,
            (q : ℝ) * (q.totient : ℝ)⁻¹ * B q χ t) Q from
        (MeasureTheory.integral_finset_sum (Nat.Icc 1 Q) (fun q _ => hsum_int q)).symm]
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
          grind
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
  have := FG.summatory_mul (fg := inst) (y := y)
  unfold inst at this
  simp only [twist_apply, Algebra.algebraMap_self, RingHom.id_apply, ← mul_assoc] at this
  calc
    summatory (fun n ↦ (@FG.f fg * @FG.g fg) n * χ n) y =
        summatory (fun n ↦ ((@FG.f fg).twist χ * (@FG.g fg).twist χ) n) y := by
      simp [Finset.sum_mul]
      congr! 2 with n hn_pos hny ⟨a, b⟩ hab
      simp only [Nat.mem_divisorsAntidiagonal, ne_eq] at hab
      simp [← hab.1]
      ring
    _ = _ := this

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
      · linarith
      · exact_mod_cast hK.1
      · positivity
    _ ≤ _ := by
      grw [summatory_T_ll_nat _ (by grind) hx]
      simp [ε]
      positivity

end Flat
