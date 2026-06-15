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
    · sorry
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
    · sorry


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

/-- The constant in the `J`-integral estimate `∫ ‖𝓜(σ+tI)‖ dt ≤ C_J · log(x+1)`
(Step 4 of `notes/theorem26_6_smooth.md`).  Its precise value comes from the split-at-`1/ε`
estimate; it is not needed downstream, only its existence. -/
noncomputable def C_J : ℝ := 1

/-- The implied constant of Theorem 26.6, assembled from `Real.exp 1 / (2π)` (the `y^σ ≤ e`
prefactor), the large-sieve constant `C_LS`, and the `J`-integral constant `C_J`. -/
noncomputable def C_LSC : ℝ := Real.exp 1 / (2 * π) * C_LS * C_J

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
  sorry

/-- Step 4 of `notes/theorem26_6_smooth.md`: the `J`-integral estimate.  The Mellin kernel
`𝓜(Smooth1 ν ε)` decays like `1/‖s‖` near the real axis and like `1/(ε‖s‖²)` in the tails;
splitting the integral at `|t| = 1/ε` gives `J ≪ log(1/(σε)) ≍ log(x+1)`. -/
theorem mellin_J_bound [Bump] {ε : ℝ} (hε_pos : 0 < ε) (hε_one : ε < 1) {σ : ℝ} (hσ_pos : 0 < σ)
    (hσ : σ ≤ 2) {x : ℝ} (hx : 1 ≤ x) (hσx : σ = (Real.log (x + 1))⁻¹)
    (hε : ε = (6 * Real.log 2)⁻¹ * x⁻¹) :
    ∫ t : ℝ, ‖mellin (fun u ↦ (Smooth1 ν ε u : ℂ)) (σ + t * I)‖ ≤ C_J * Real.log (x + 1) := by
  -- Proof outline (Step 4 of `notes/theorem26_6_smooth.md`):
  --   • Bound A (small `t`):  `‖𝓜(σ+tI)‖ ≤ C₁/‖σ+tI‖`  from `MellinOfSmooth1a` + `mellin_bump_bounded`.
  --   • Bound B (large `t`):  `‖𝓜(σ+tI)‖ ≤ C₂/(ε‖σ+tI‖²)`  from `MellinOfSmooth1b`.
  -- Split `∫` at `|t| = 1/ε`; bound A gives `∫_{|t|≤1/ε} ≪ log(1/(σε))`, bound B gives `∫_{|t|>1/ε} ≪ 1`.
  -- Since `ε = (6 log 2)⁻¹ x⁻¹` and `σ = 1/log(x+1)`, `log(1/(σε)) ≍ log(x+1)`.
  sorry

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
    · sorry
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
      ≤ C_LSC * (√(N * M) + √M * Q + √N * Q + Q^2) *
      √(summatory (fun m ↦ ‖f m‖^2) M) * √(summatory (fun n ↦ ‖g n‖ ^ 2) N) * Real.log (x + 1) := by
  classical
  let ε := (6 * Real.log 2)⁻¹ * x⁻¹
  simp_rw [temp hx, FG.summatory_mul_char]
  obtain ⟨ν, diffν, νpos, suppν, mass_one⟩ := SmoothExistence
  let inst : Bump := {ν, diffν, νpos, suppν, mass_one}
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
