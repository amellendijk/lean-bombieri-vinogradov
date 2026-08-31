import Mathlib

import PrimeNumberTheoremAnd.SmoothExistence

import BV.Mellin
import BV.Delta


/-
Note: There is a sloppish sorry-free version of this file on the branch claude-fable.
-/


namespace Mathlib.Meta.Positivity
open Qq Lean Meta

/-- The `positivity` extension which proves that `⨆ i, f i` is nonnegative for a real-valued
function `f`, provided each `f i` is nonnegative. This also handles the bounded supremum
`⨆ i ∈ s, f i`, which unfolds to a nested `iSup`. -/
@[positivity ⨆ _, _]
def tmp : PositivityExt where eval {u α} zα pα? e :=
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


open ArithmeticFunction Set ENNReal

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

-- TODO: consider, do we want Q? Should this be a propositional typeclass `TwoLe x`? This avoids other issues.
class Flat.ProofData where
  x : ℝ
  hx : 2 ≤ x
  Q : ℝ
  hQ_pos : 0 < Q

namespace Flat.ProofData

variable [Flat.ProofData]

lemma hx_pos : 0 < x := by linarith only [hx]

lemma hlogx_succ_pos : 0 < Real.log (x + 1) := by
  apply Real.log_pos
  grind [hx]

@[reducible]
noncomputable def ε : ℝ := (6 * Real.log 2)⁻¹ * x⁻¹

lemma hε_pos : 0 < ε := by
  sorry

lemma hε_lt_one : ε < 1 := by
  grw [ε, ← hx]
  -- TODO: Replace with future interval arithmetic tactic.
  field_simp
  have := Real.log_two_gt_d9
  grind

noncomputable def σ : ℝ := 1 / Real.log (x + 1)

lemma hσ_pos : 0 < σ := by
  rw [σ]
  apply div_pos
  · simp
  apply hlogx_succ_pos

lemma hσ_le_two : σ ≤ 2 := by
  sorry

end Flat.ProofData

open Flat.FG Flat.Bump Flat.ProofData

noncomputable def Flat.T [Bump] [FG] {q : ℕ} (ε y : ℝ) (χ : DirichletCharacter ℂ q) : ℂ :=
  summatory (fun m ↦ summatory (fun n ↦ f m * χ m * g n * χ n * Smooth1 ν ε (m*n/y)) N) M

namespace Flat

open Complex

theorem T_eq_sum_integral
    [Bump] [FG] [ProofData] {q : ℕ} {χ : DirichletCharacter ℂ q} (y : ℝ) (hy : 1 ≤ y) :
  T ε y χ =
    summatory (fun m ↦ summatory (fun n ↦
      f m * χ m * g n * χ n *
     (1 / (2 * π)) • ∫ t : ℝ, (m*n/y : ℂ) ^ (-(σ + t * I)) •
     mellin (fun x ↦ (Smooth1 ν ε x : ℂ)) (σ + t * I)) N ) M := by
  rw [T]
  congr! 2 with m hm_pos hm n hn_pos hn
  rw [← Smooth1_mellinInv_mellin_eq (σ := σ) (ε := ε) _ (fun x _ ↦ νpos x) suppν _ hε_pos hε_lt_one hσ_pos hσ_le_two]
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
theorem integrable_term
    [Bump] [FG] [ProofData] {q : ℕ}
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
      (by rw [← MeasureTheory.integral_Ici_eq_integral_Ioi]; exact mass_one) hε_pos hε_lt_one hσ_pos hσ_le_two
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

theorem T_eq_integral_sum
    [Bump] [FG] [ProofData] {q : ℕ} {χ : DirichletCharacter ℂ q} (y : ℝ) (hy : 1 ≤ y) :
  T ε y χ =
     (1 / (2 * π)) • ∫ t : ℝ,
    summatory (fun m ↦ f m * χ m * m ^ (-(σ + t * I))) M *
    summatory (fun n ↦ g n * χ n * n ^ (-(σ + t * I))) N *
     (1/y : ℂ) ^ (-(σ + t * I)) •
     mellin (fun x ↦ (Smooth1 ν ε x : ℂ)) (σ + t * I) := by
  rw [T_eq_sum_integral y hy]
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
    exact integrable_term hy m n
      (Finset.mem_Ioc.mp hm).1 (Finset.mem_Ioc.mp hn).1
  · -- Outer sum (over `n ≤ N`): a finite sum of `integrable_term` terms.
    intro i hi
    refine integrable_finsetSum _ fun m hm => ?_
    exact integrable_term hy m i
      (Finset.mem_Ioc.mp hm).1 (Finset.mem_Ioc.mp hi).1

noncomputable def B [Bump] [FG] {q : ℕ} (σ ε t : ℝ) (χ : DirichletCharacter ℂ q) : ℝ≥0∞ :=
    ‖summatory (fun m ↦ f m * χ m * m ^ (-(σ + t * I))) M‖ₑ *
    ‖summatory (fun n ↦ g n * χ n * n ^ (-(σ + t * I))) N‖ₑ *
    ‖mellin (fun x ↦ (Smooth1 ν ε x : ℂ)) (σ + t * I)‖ₑ

@[fun_prop]
lemma Measurable_B [Bump] [FG] {q : ℕ} (σ ε : ℝ) (χ : DirichletCharacter ℂ q) : Measurable (fun t ↦ B σ ε t χ) := by
  dsimp [B]
  fun_prop

open NNReal

noncomputable def C_TB : ℝ≥0 := ⟨Real.exp 1 * π⁻¹ * 2⁻¹, by positivity⟩

lemma C_TB_def : C_TB = ‖Real.exp 1 * π⁻¹ * 2⁻¹‖ₑ:= by
  simp [C_TB]
  sorry

attribute [push] MeasureTheory.lintegral_const_mul

open MeasureTheory

@[simp]
lemma Complex.enorm_ofReal (r : ℝ) :
    ‖(r : ℂ)‖ₑ = ‖r‖ₑ := by
  simp [enorm_eq_nnnorm]

@[simp]
theorem Complex.arg_ofReal_eq_pi_iff (x : ℝ) :
    (x : ℂ).arg = π ↔ x < 0 := by
  simp [Complex.arg_eq_pi_iff]

theorem sup_T_le_lintegral_B [Bump] [FG] [ProofData] {q : ℕ} (χ : DirichletCharacter ℂ q) : ⨆ y ∈ Icc 1 (x+1), ‖T ε y χ‖ₑ ≤ C_TB * ∫⁻ t : ℝ, B σ ε t χ := by
  refine iSup_le fun y ↦ iSup_le fun hy ↦ ?_
  simp only [mem_Icc] at hy
  rw [T_eq_integral_sum y hy.1]
  simp only [one_div, mul_inv_rev, neg_add_rev, smul_eq_mul, real_smul, Complex.ofReal_mul,
    ofReal_inv, Complex.ofReal_ofNat, enorm_mul, ne_eq, Complex.ofReal_eq_zero, Real.pi_ne_zero,
    not_false_eq_true, enorm_inv, OfNat.ofNat_ne_zero]
  grw [enorm_integral_le_lintegral_enorm]
  simp
  pull (disch := fun_prop) lintegral
  gcongr 1
  have {t : ℝ} : ‖(y⁻¹ : ℂ) ^ (- (t * I) + -σ)‖ₑ ≤ ‖Real.exp 1‖ₑ := by
    rw [Complex.cpow_def_of_ne_zero (by sorry), Complex.log_inv _ (by simp; grind)]
    simp [← ofReal_norm, Complex.norm_exp, Complex.log_im, Complex.arg_ofReal_of_nonneg (show 0 ≤ y by grind), Complex.log_ofReal_re]
    gcongr 2
    grw [hy.2, σ]
    · -- Paper cut: This should be trivial.
      have : 0 < Real.log (x + 1) := hlogx_succ_pos
      field_simp
      rfl
    · grind
    -- TODO: tag with positivity
    · exact hσ_pos.le

  grw [B, C_TB_def, this]
  -- lemma enorm_eq_nnnorm let us side-step some issues with casts and enorms. Look into this.
  simp [ne_eq, Real.pi_ne_zero, not_false_eq_true, OfNat.ofNat_ne_zero,
    neg_add_rev, enorm_eq_nnnorm]
  apply le_of_eq
  ring

def C_LSC : ℝ := sorry

open _root_.Classical in
theorem summatory_T_ll [Bump] [FG] [ProofData] :
    summatory (fun q => ∑ χ : DirichletCharacter ℂ q with χ.IsPrimitive, ↑q * (↑q.totient)⁻¹ * ⨆ y ∈ Icc 1 (x+1), ‖T ε y χ‖ₑ) Q ≤ .ofReal (C_LSC *
    (√(N * M) + √M * Q + √N * Q + Q ^ 2) * √(summatory (fun m => ‖f m‖ ^ 2) M) * √(summatory (fun n => ‖g n‖^2) N)) := by
  sorry

theorem sup_summatory_eq_sup_nat {f : ℕ → ℂ}
    {x : ℝ} (hx : 2 ≤ x) :
  open Classical in
      ⨆ y ∈ Set.Icc 1 x, ‖summatory f y‖ₑ =
      ⨆ K ∈ Set.Icc 1 ⌊x⌋₊, ‖summatory f (K + 2⁻¹)‖ₑ := by
  have hfloor_add_half {n : ℕ} : ⌊(n + 2⁻¹: ℝ)⌋₊ = n := by
    rw [add_comm, Nat.floor_add_natCast (show 0 ≤ (2⁻¹ : ℝ) by norm_num)]
    norm_num
  apply le_antisymm
  · apply iSup_le
    intro y
    apply iSup_le
    intro h
    have : Finset.Icc 1 ⌊x⌋₊ = Icc 1 ⌊x⌋₊ := by simp
    rw [← this]
    grw [← le_iSup (i := ⌊y⌋₊)]
    · have : ⌊y⌋₊ ∈ Icc 1 (⌊x⌋₊) := by
        simp only [mem_Icc, Nat.one_le_floor_iff]
        simp only [mem_Icc] at h
        refine ⟨h.1, ?_⟩
        gcongr
        exact h.2
      simp only [Finset.coe_Icc, this, ciSup_unique, ge_iff_le]
      apply le_of_eq
      simp_rw [summatory_apply, hfloor_add_half]
  · apply iSup_le
    intro K
    apply iSup_le
    intro h
    grw [← le_iSup (i := (K : ℝ))]
    · have : ↑K ∈ Icc 1 x := by
        simp only [mem_Icc, Nat.one_le_cast] at h ⊢
        refine ⟨h.1, ?_⟩
        rw [Nat.le_floor_iff] at h
        · exact h.2
        · grind
      simp [this, summatory_apply, hfloor_add_half]

open ENNReal

theorem temp [fg : FG]
    {x Q : ℝ} (hx : 2 ≤ x) :
  open Classical in
    summatory (fun q ↦ ∑ χ : DirichletCharacter ℂ q with χ.IsPrimitive,
      q * (q.totient : ℝ≥0∞)⁻¹ * ⨆ y ∈ Set.Icc 1 x, ‖summatory (fun n ↦ (f * g) n * χ n) y‖ₑ) Q =
    summatory (fun q ↦ ∑ χ : DirichletCharacter ℂ q with χ.IsPrimitive,
      q * (q.totient : ℝ≥0∞)⁻¹ * ⨆ K ∈ Set.Icc 1 ⌊x⌋₊, ‖summatory (fun n ↦ (f * g) n * χ n) (K + 2⁻¹)‖ₑ) Q := by
  simp_rw [sup_summatory_eq_sup_nat hx]

open _root_.Classical in
theorem summatory_T_ll_nat [Bump] [FG] [data : ProofData] :
    (summatory (fun q => ∑ χ : DirichletCharacter ℂ q with χ.IsPrimitive, ↑q * (↑q.totient)⁻¹ * ⨆ K ∈ Icc 1 ⌊x⌋₊, ‖T ε (↑K + 2⁻¹) χ‖ₑ) Q) ≤ .ofReal (C_LSC *
    (√(N * M) + √M * Q + √N * Q + Q ^ 2) * √(summatory (fun m => ‖f m‖ ^ 2) M) * √(summatory (fun n => ‖g n‖^2) N)) := by
  trans (summatory (fun q => ∑ χ : DirichletCharacter ℂ q with χ.IsPrimitive, ↑q * (↑q.totient)⁻¹ * ⨆ y ∈ Icc 1 (x+1), ‖T ε y χ‖ₑ) Q)
  · gcongr with q hq hqQ χ hχ
    apply iSup_le
    intro K
    apply le_iSup_of_le (i := K + (2⁻¹ : ℝ))
    by_cases h : K ∈ Icc 1 ⌊x⌋₊
    · have h' : K + (2 : ℝ)⁻¹ ∈ Icc 1 (x+1) := by
        simp only [mem_Icc] at h ⊢
        have : (1 : ℝ) ≤ K := by
          exact_mod_cast h.1
        have : (K : ℝ) ≤ x := by
          grw [h.2]
          apply Nat.floor_le
          apply hx_pos.le
        grind
      simp only [h, h', ciSup_unique]
      rfl
    · simp [h, mem_Icc]
  apply summatory_T_ll

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
  have : summatory (fun n => (f.twist χ * g.twist χ) n) y = summatory (fun m => summatory (fun n => if ↑m * ↑n ≤ y then f.twist χ m * g.twist χ n else 0) N) M := summatory_mul (fg := {
      M, hM_pos, N, hN_pos,
      f := f.twist χ,
      g := g.twist χ
      hf := by simp +contextual [hf]
      hg := by simp +contextual [hg]
    }) (y := y)
  simp +instances only [twist_apply, Algebra.algebraMap_self, RingHom.id_apply, ← mul_assoc] at this
  rw [← this]
  simp [Finset.sum_mul]
  congr! 2 with n hn_pos hny ⟨a, b⟩ hab
  simp only [Nat.mem_divisorsAntidiagonal, ne_eq] at hab
  simp [← hab.1]
  ring

theorem LargeSieve_convolution [fg : FG]
    {x Q : ℝ} (hx : 2 ≤ x) (hQ : 1 ≤ Q) :
  open Classical in
    (summatory (fun q ↦ ∑ χ : DirichletCharacter ℂ q with χ.IsPrimitive,
      q * (q.totient : ℝ≥0∞)⁻¹ * ⨆ y ∈ Set.Icc 1 x, ‖summatory (fun n ↦ (f * g) n * χ n) y‖ₑ) Q)
      ≤ .ofReal (C_LSC * (√(N * M) + √M * Q + √N * Q + Q^2) *
      √(summatory (fun m ↦ ‖f m‖^2) M) * √(summatory (fun n ↦ ‖g n‖^2) N)) := by
  classical
  let ε := (6 * Real.log 2)⁻¹ * x⁻¹
  simp_rw [temp hx, FG.summatory_mul_char]
  obtain ⟨ν, diffν, νpos, suppν, mass_one⟩ := SmoothExistence
  let inst : Bump := {ν, diffν, νpos, suppν, mass_one}
  calc
    _ = (summatory (fun q ↦ ∑ χ : DirichletCharacter ℂ q with χ.IsPrimitive,
        q * (q.totient : ℝ≥0∞)⁻¹ * ⨆ K ∈ Set.Icc 1 ⌊x⌋₊, ‖T ε (K + 2⁻¹) χ‖ₑ) Q) := by
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
      apply (summatory_T_ll_nat
        (data := {x := x, Q := Q, hx := hx, hQ_pos := (zero_lt_one.trans_le hQ)})).trans
      simp

end Flat
