import Mathlib
import Architect

import BV.Defs
import BV.LambdaLE
import BV.LambdaSharp
import BV.LambdaFlat

open ArithmeticFunction

open scoped BV

open ProofData
open BV

noncomputable section

/-! ## Bombieri-Vinogradov Theorem

This module contains the formalization of the Bombieri-Vinogradov theorem,
a fundamental result in analytic number theory.
-/


/-! Wrapping up -/

/-- `maxy f ≥ 0` unconditionally: the family defining `maxy` ranges over all reals `y`,
and for `y ∉ [√x, x]` the inner supremum (over the empty proposition `y ∈ [√x,x]`) is `0`. -/
theorem maxy_nonneg' [ProofData] (f : ℝ → ℝ) : 0 ≤ maxy f := by
  rw [maxy]
  by_cases h : BddAbove (Set.range fun y => ⨆ (_ : y ∈ Set.Icc (√x) x), f y)
  · have hmem : (√x - 1) ∉ Set.Icc (√x) x := by
      simp only [Set.mem_Icc, not_and, not_le]; intro _; linarith
    refine le_ciSup_of_le h (√x - 1) ?_
    rw [ciSup_neg hmem]
    exact le_of_eq Real.sSup_empty.symm
  · rw [Real.iSup_of_not_bddAbove h]

/-- `maxya q F ≥ 0` unconditionally. -/
theorem maxya_nonneg [ProofData] {q : ℕ} (F : ℝ → ZMod q → ℝ) : 0 ≤ maxya q F := by
  rw [maxya]
  exact Real.iSup_nonneg (fun a ↦ maxy_nonneg' _)

/-- If `F z a` is bounded above by a nonnegative `B` on `[√x, x]` for a *unit* `a`,
then `F y a ≤ maxya q F` for `y ∈ [√x, x]`. -/
theorem le_maxya [ProofData] {q : ℕ} (F : ℝ → ZMod q → ℝ) {y : ℝ} {a : ZMod q}
    (ha : IsUnit a) (hy1 : √x ≤ y) (hy2 : y ≤ x) {B : ℝ} (hB : 0 ≤ B)
    (hbound : ∀ z, √x ≤ z → z ≤ x → F z a ≤ B) :
    F y a ≤ maxya q F := by
  obtain ⟨u, rfl⟩ := ha
  refine le_trans (le_maxy (f := fun y ↦ F y u) hy1 hy2 hB hbound) ?_
  rw [maxya]
  exact le_ciSup (f := fun a : (ZMod q)ˣ ↦ maxy (fun y ↦ F y ↑a))
    (Finite.bddAbove_range _) u

/-- For a unit `a` and `y ∈ [√x,x]`, `Δ_[f](y;q,a) ≤ maxya q (Δ_[f])`. -/
theorem Delta_le_maxya [ProofData] (f : ℕ → ℝ) {q : ℕ} {y : ℝ} {a : ZMod q}
    (ha : IsUnit a) (hy1 : √x ≤ y) (hy2 : y ≤ x) :
    Δ_[f](y; q, a) ≤ maxya q (fun y a ↦ Δ_[f](y; q, a)) := by
  refine le_maxya (fun y a ↦ Δ_[f](y; q, a)) ha hy1 hy2
    (B := 2 * summatory (fun n ↦ |f n|) x)
    (by have := summatory_nonneg (fun n ↦ |f n|) x (fun n _ ↦ abs_nonneg _); linarith)
    (fun z hz1 hz2 ↦ ?_)
  refine (le_abs_self _).trans ((abs_Delta_le_two_summatory_abs f z q a).trans ?_)
  gcongr

/-- For a unit `a` and `y ∈ [√x,x]`, `|Δ_[f](y;q,a)| ≤ maxya q (|Δ_[f]|)`. -/
theorem abs_Delta_le_maxya [ProofData] (f : ℕ → ℝ) {q : ℕ} {y : ℝ} {a : ZMod q}
    (ha : IsUnit a) (hy1 : √x ≤ y) (hy2 : y ≤ x) :
    |Δ_[f](y; q, a)| ≤ maxya q (fun y a ↦ |Δ_[f](y; q, a)|) := by
  refine le_maxya (fun y a ↦ |Δ_[f](y; q, a)|) ha hy1 hy2
    (B := 2 * summatory (fun n ↦ |f n|) x)
    (by have := summatory_nonneg (fun n ↦ |f n|) x (fun n _ ↦ abs_nonneg _); linarith)
    (fun z hz1 hz2 ↦ ?_)
  refine (abs_Delta_le_two_summatory_abs f z q a).trans ?_
  gcongr

/-- Per-conductor triangle inequality from the `Λ = Λ♯ + Λ♭ + Λ_{≤U}` decomposition. -/
theorem maxya_Delta_Lambda_le [ProofData] (q : ℕ) :
    maxya q (fun y a ↦ |Δ_[Λ](y; q, a)|) ≤
      maxya q (fun y a ↦ |Δ_[Λ♯](y; q, a)|) + maxya q (fun y a ↦ |Δ_[Λ♭](y; q, a)|)
      + maxya q (fun y a ↦ |Δ_[Λ≤U](y; q, a)|) := by
  have hdecomp : (⇑Λ : ℕ → ℝ) = ⇑Λ♯ + ⇑Λ♭ + ⇑Λ≤U := by
    funext n; simpa using Lambda_decomp n
  refine maxya_le_unit (fun y hy1 hy2 a ha ↦ ?_) ?_
  · have heq : Δ_[Λ](y; q, a)
        = Δ_[Λ♯](y; q, a) + Δ_[Λ♭](y; q, a) + Δ_[Λ≤U](y; q, a) := by
      rw [show (⇑Λ : ℕ → ℝ) = _ from hdecomp, Delta_add, Delta_add]
    rw [heq]
    calc |Δ_[Λ♯](y; q, a) + Δ_[Λ♭](y; q, a) + Δ_[Λ≤U](y; q, a)|
        ≤ |Δ_[Λ♯](y; q, a)| + |Δ_[Λ♭](y; q, a)| + |Δ_[Λ≤U](y; q, a)| := by
          refine (abs_add_le _ _).trans ?_; gcongr; exact abs_add_le _ _
      _ ≤ _ := add_le_add (add_le_add (abs_Delta_le_maxya _ ha hy1 hy2)
          (abs_Delta_le_maxya _ ha hy1 hy2)) (abs_Delta_le_maxya _ ha hy1 hy2)
  · have h1 := maxya_nonneg (fun y a ↦ |Δ_[Λ♯](y; q, a)|)
    have h2 := maxya_nonneg (fun y a ↦ |Δ_[Λ♭](y; q, a)|)
    have h3 := maxya_nonneg (fun y a ↦ |Δ_[Λ≤U](y; q, a)|)
    linarith

/-- At conductor `q = 0`, a unit `a : ZMod 0 = ℤ` equals `±1`, and `Δ_[Λ≤U](y;0,a) = 0`. -/
theorem Delta_LambdaLEU_conductor_zero [ProofData] (y : ℝ) {a : ZMod 0} (ha : IsUnit a) :
    Δ_[Λ≤U](y; 0, a) = 0 := by
  classical
  have hind : (Nat.modEqs a).indicator (⇑Λ≤U) = fun _ ↦ (0 : ℝ) := by
    funext n
    rw [Set.indicator_apply]
    split_ifs with hn
    · rw [Nat.mem_modEqs] at hn
      -- `(n : ZMod 0) = a`, i.e. `(n : ℤ) = a`
      rcases Int.isUnit_iff.mp ha with h | h
      · -- a = 1, forcing n = 1
        have : (n : ℤ) = 1 := h ▸ hn
        have hn1 : n = 1 := by exact_mod_cast this
        rw [hn1]
        by_cases hU : (1 : ℝ) ≤ U
        · rw [LambdaLEU_apply_of_le (by exact_mod_cast hU)]
          exact ArithmeticFunction.vonMangoldt_apply_one
        · rw [LambdaLEU_apply_of_gt (by push_cast; linarith)]
      · -- a = -1, impossible for a cast of a natural
        exfalso
        have : (n : ℤ) = -1 := h ▸ hn
        omega
    · rfl
  simp only [Delta, hind, summatory, Finset.sum_const_zero, Nat.totient_zero, Nat.cast_zero,
    inv_zero, zero_mul, sub_zero]

def C_BV_L (A : ℕ) : ℝ := C_BVLS + C_BV_LF A + 2

open ProofData in
@[blueprint (statement :=
/--
For each fixed $A \ge 0$ we have
$$\sum_{q\le Q} \max_{\sqrt x \le y \le x} \max_{a \in (\mathbb{Z}/q\mathbb{Z})^*} \left| \Delta_{\Lambda}(y; q,a) \right| \ll_A \frac{x}{(\log x)^{A}}$$
uniformly for $x \ge 2$ and $1 \le Q \le \sqrt{x}/(\log (x))^{A+3}$
-/
) (proof := /--
Follows from \ref{Lambda_decomp} and the triangle inequality, combining the bounds
\ref{BV_LambdaLE}, \ref{BV_LambdaSharp}, and \ref{BV_LambdaFlat}.
-/) (uses := [BV_LambdaLE, BV_LambdaSharp, BV_LambdaFlat, Lambda_decomp])]
theorem BV_Delta_Lambda [ProofData] (A : ℕ) (Q : ℝ) (h1Q : 1 ≤ Q) (hQ : Q ≤ √x / (Real.log x)^(A+3)) :
    ∑ q ∈ Nat.Icc 0 Q, maxya q (fun y a ↦ |Δ_[Λ](y; q, a)|) ≤
      C_BV_L A * x / (Real.log x)^A := by
  have hL1 : (1 : ℝ) ≤ Real.log x := one_le_log_x
  have hLpos : (0 : ℝ) < Real.log x := log_x_pos
  have hx0 : (0 : ℝ) ≤ x := ProofData.x_nonneg
  have hQ0 : (0 : ℝ) ≤ Q := by linarith
  -- Per-conductor triangle bound, then split the sum into the three pieces.
  have hstep : ∑ q ∈ Nat.Icc 0 Q, maxya q (fun y a ↦ |Δ_[Λ](y; q, a)|) ≤
      (∑ q ∈ Nat.Icc 0 Q, maxya q (fun y a ↦ |Δ_[Λ♯](y; q, a)|))
        + (∑ q ∈ Nat.Icc 0 Q, maxya q (fun y a ↦ |Δ_[Λ♭](y; q, a)|))
        + (∑ q ∈ Nat.Icc 0 Q, maxya q (fun y a ↦ |Δ_[Λ≤U](y; q, a)|)) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum (fun q _ ↦ maxya_Delta_Lambda_le q)
  -- Bound each of the three pieces.
  have hsharp : ∑ q ∈ Nat.Icc 0 Q, maxya q (fun y a ↦ |Δ_[Λ♯](y; q, a)|)
      ≤ C_BVLS * (x / (Real.log x)^A) := BV_LambdaSharp Q h1Q hQ
  have hflat : ∑ q ∈ Nat.Icc 0 Q, maxya q (fun y a ↦ |Δ_[Λ♭](y; q, a)|)
      ≤ C_BV_LF A * x / (Real.log x)^A := BV_LambdaFlat A Q h1Q hQ
  -- The `q = 0` term of the `Λ_{≤U}` piece vanishes, reducing to `BV_LambdaLE`.
  have hLE : ∑ q ∈ Nat.Icc 0 Q, maxya q (fun y a ↦ |Δ_[Λ≤U](y; q, a)|)
      ≤ 2 * x / (Real.log x)^(A+2) := by
    have hsplit : Nat.Icc (0 : ℝ) Q = insert 0 (Nat.Icc 1 Q) := by
      ext n
      simp only [Finset.mem_insert, Nat.mem_Icc]
      constructor
      · rintro ⟨-, h2⟩
        rcases Nat.eq_zero_or_pos n with hn | hn
        · exact Or.inl hn
        · exact Or.inr ⟨Nat.one_le_cast.mpr hn, h2⟩
      · rintro (rfl | ⟨-, h2⟩)
        · exact ⟨by positivity, by exact_mod_cast hQ0⟩
        · exact ⟨by positivity, h2⟩
    have h0notmem : (0 : ℕ) ∉ Nat.Icc (1 : ℝ) Q := by
      simp only [Nat.mem_Icc, Nat.cast_zero]; intro h; linarith
    rw [hsplit, Finset.sum_insert h0notmem]
    have hzero : maxya 0 (fun y a ↦ |Δ_[Λ≤U](y; (0 : ℕ), a)|) ≤ 0 := by
      refine maxya_le_unit (fun y _ _ a ha ↦ ?_) le_rfl
      rw [Delta_LambdaLEU_conductor_zero y ha, abs_zero]
    have hle := BV_LambdaLE (A := A) Q hQ0 hQ
    linarith
  -- Combine: `2x/L^(A+2) ≤ 2x/L^A`, then collect the constant.
  have hpow : (2 : ℝ) * x / (Real.log x)^(A+2) ≤ 2 * x / (Real.log x)^A := by
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    exact pow_le_pow_right₀ hL1 (by omega)
  have hcollect : C_BVLS * (x / (Real.log x)^A) + C_BV_LF A * x / (Real.log x)^A
      + 2 * x / (Real.log x)^A = C_BV_L A * x / (Real.log x)^A := by
    rw [C_BV_L]; ring
  calc ∑ q ∈ Nat.Icc 0 Q, maxya q (fun y a ↦ |Δ_[Λ](y; q, a)|)
      ≤ _ := hstep
    _ ≤ C_BVLS * (x / (Real.log x)^A) + C_BV_LF A * x / (Real.log x)^A
          + 2 * x / (Real.log x)^(A+2) := add_le_add (add_le_add hsharp hflat) hLE
    _ ≤ C_BVLS * (x / (Real.log x)^A) + C_BV_LF A * x / (Real.log x)^A
          + 2 * x / (Real.log x)^A := by gcongr
    _ = C_BV_L A * x / (Real.log x)^A := hcollect

/-
The proofs that follow were written by GPT-5.6-sol xhigh
-/

/-- An elementary uniform bound for a single progression Chebyshev function. -/
lemma psi_le_chebyshev {q : ℕ} (z : ℝ) (a : ZMod q) :
    ψ z a ≤ Chebyshev.psi z := by
  rw [chebyPsi_eq_summatory, ← summatory_vonMangoldt]
  refine summatory_mono_fun _ _ z fun n _ ↦ ?_
  rw [Set.indicator]
  split_ifs
  · exact le_rfl
  · exact ArithmeticFunction.vonMangoldt_nonneg

/-- A crude bound used only to dispose of bounded ranges of `x`. -/
lemma abs_psi_sub_div_le {q : ℕ} (hq : 0 < q) {z : ℝ} (hz1 : 1 ≤ z)
    (a : ZMod q) :
    |ψ z a - z / q.totient| ≤ (Real.log 4 + 5) * z := by
  have hψ0 : 0 ≤ ψ z a := by
    rw [chebyPsi_eq_summatory, summatory]
    exact Finset.sum_nonneg fun n _ ↦ by
      rw [Set.indicator]
      split_ifs
      · exact ArithmeticFunction.vonMangoldt_nonneg
      · exact le_rfl
  have hψ : ψ z a ≤ (Real.log 4 + 4) * z :=
    (psi_le_chebyshev z a).trans (Chebyshev.psi_le_const_mul_self (by positivity))
  have hφ : (1 : ℝ) ≤ q.totient := by exact_mod_cast Nat.totient_pos.mpr hq
  have hφ0 : (0 : ℝ) ≤ q.totient := hφ.trans' (by norm_num)
  have hzφ0 : 0 ≤ z / q.totient := div_nonneg (by positivity) hφ0
  have hzφ : z / q.totient ≤ z := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  rw [abs_sub_le_iff]
  constructor <;> nlinarith [Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 4)]

/-- The elementary contribution of prime powers dividing the modulus, in a form
that does not require a `ProofData` instance for the endpoint. -/
private lemma sum_vonMangoldt_not_coprime_generic {z : ℝ} (hz : 2 ≤ z)
    {q : ℕ} (hq : 0 < q) :
    |summatory (fun n ↦ if ¬q.Coprime n then Λ n else 0) z| ≤
      (Real.log 2)⁻¹ * (Real.log q * Real.log z) := by
  have hpow {k : ℕ} (hk : 0 < k) :
      |∑ p ∈ Finset.Ioc 0 ⌊z ^ ((1 : ℝ) / k)⌋₊ with Nat.Prime p,
          if ¬q.Coprime (p ^ k) then Λ p else 0| ≤ Real.log q := by
    have {p : ℕ} (hp : p.Prime) : ¬ q.Coprime (p ^ k) ↔ p ∣ q := by
      rw [Nat.coprime_comm]
      simp only [Nat.coprime_pow_left_iff, hk, Nat.Prime.coprime_iff_not_dvd hp,
        Decidable.not_not]
    rw [abs_of_nonneg ?A]
    case A =>
      apply Finset.sum_nonneg fun _ _ ↦ by split_ifs <;> simp
    simp +contextual (disch := grind) only [this]
    simp_rw [← Finset.sum_filter]
    trans ∑ d ∈ q.divisors, Λ d
    · apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro d hd
        simp only [Finset.mem_filter] at hd
        exact Nat.mem_divisors.mpr ⟨hd.2, hq.ne'⟩
      · intro d _ _
        exact ArithmeticFunction.vonMangoldt_nonneg
    · apply le_of_eq
      exact ArithmeticFunction.vonMangoldt_sum
  simp_rw [summatory_apply]
  rw [sum_PrimePow_eq_sum_sum_of_eq_zero]
  · grw [Finset.abs_sum_le_sum_abs]
    simp +contextual (disch := grind) only [ArithmeticFunction.vonMangoldt_apply_pow]
    trans ∑ k ∈ Finset.Icc 1 ⌊Real.log z / Real.log 2⌋₊, Real.log q
    · gcongr with k hk
      exact hpow (Finset.mem_Icc.mp hk).1
    simp only [Finset.sum_const, Nat.card_Icc, add_tsub_cancel_right, nsmul_eq_mul]
    grw [Nat.floor_le (div_nonneg (Real.log_nonneg (by linarith))
      (Real.log_nonneg (by norm_num)))]
    apply le_of_eq
    ring
  · linarith
  · simp +contextual [vonMangoldt_eq_zero_iff]

private lemma coprime_vonMangoldt_error_generic (B : ℕ) {z : ℝ} (hz : 2 ≤ z)
    {q : ℕ} (hq : 0 < q) :
    |summatory (fun n ↦ if q.Coprime n then Λ n else 0) z - z| ≤
      C_SW B 0 * (z / (Real.log z) ^ B) +
        (Real.log 2)⁻¹ * (Real.log q * Real.log z) := by
  have hPNT := siegel_walfisz B 0 hz (q := 1) (by norm_num) (by simp)
    (a := (1 : ZMod 1)) (by simp)
  simp only [ψ_one_one] at hPNT
  rw [← summatory_vonMangoldt] at hPNT
  norm_num at hPNT
  have hsplit :
      summatory (fun n ↦ if q.Coprime n then Λ n else 0) z - z =
        (summatory (fun n ↦ Λ n) z - z) -
          summatory (fun n ↦ if ¬q.Coprime n then Λ n else 0) z := by
    rw [← summatory_sub_ite]
    ring
  rw [hsplit]
  exact (abs_sub _ _).trans (add_le_add hPNT
    (sum_vonMangoldt_not_coprime_generic hz hq))

private lemma pnt_ratio_bound [ProofData] (B : ℕ) {z : ℝ}
    (hz1 : √x ≤ z) (hz2 : z ≤ x) :
    z / (Real.log z) ^ B ≤ 2 ^ B * x / (Real.log x) ^ B := by
  have hx0 : 0 ≤ x := ProofData.x_nonneg
  have hsx : 0 < √x := Real.sqrt_pos.2 ProofData.x_pos
  have hz0 : 0 < z := hsx.trans_le hz1
  have hlogz : 0 < Real.log z := by
    apply Real.log_pos
    have hlog16 := sixteen_le_log_x
    have hxexp : Real.exp 16 ≤ x := by
      rw [← Real.exp_log ProofData.x_pos]
      exact Real.exp_le_exp.mpr hlog16
    have hs4 : Real.exp 8 ≤ √x := by
      rw [Real.le_sqrt (by positivity) hx0, pow_two, ← Real.exp_add]
      norm_num
      exact hxexp
    have : 2 < Real.exp 8 := by
      calc (2 : ℝ) < Real.exp 1 := by
            simpa only [one_add_one_eq_two] using
              Real.add_one_lt_exp (show (1 : ℝ) ≠ 0 by norm_num)
        _ ≤ Real.exp 8 := Real.exp_le_exp.mpr (by norm_num)
    linarith
  have hlogsqrt : Real.log x / 2 ≤ Real.log z := by
    rw [← Real.log_sqrt hx0]
    exact Real.log_le_log hsx hz1
  have hlog : Real.log x ≤ 2 * Real.log z := by linarith
  have hp : (Real.log x) ^ B ≤ 2 ^ B * (Real.log z) ^ B := by
    calc
      (Real.log x) ^ B ≤ (2 * Real.log z) ^ B := by gcongr
      _ = 2 ^ B * (Real.log z) ^ B := mul_pow _ _ _
  have hL : 0 < (Real.log x) ^ B := pow_pos log_x_pos _
  have hZ : 0 < (Real.log z) ^ B := pow_pos hlogz _
  rw [div_le_div_iff₀ hZ hL]
  nlinarith

/-- Implied constant for Bombieri-Vinogradov theorem.  The first summand is the
analytic constant; the second deliberately coarse summand absorbs the compact
range in which no `ProofData` instance exists. -/
noncomputable def C_BV (A : ℕ) : ℝ :=
  |C_BV_L A| + (Real.log 4 + 5) +
    |C_SW (A + 2) 0| * 2 ^ (A + 2) * |C_tot| +
    (Real.log 2)⁻¹ * |C_tot| * (A + 3).factorial +
    (Real.log 4 + 5) * Real.exp 16 * 32 ^ A / (Real.log 2) ^ (A + 3)

private lemma BV_compact (A : ℕ) {x Q : ℝ} (hx : 2 ≤ x)
    (hxE : x ≤ Real.exp 32) (hQ0 : 1 ≤ Q)
    (hQ : Q ≤ √x / (Real.log x) ^ (A + 3)) :
    ∑ q ∈ Nat.Icc 1 Q, ⨆ z ∈ Set.Icc 1 x, ⨆ a : (ZMod q)ˣ,
        |ψ (q := q) z a - z / q.totient| ≤
      ((Real.log 4 + 5) * Real.exp 16 * 32 ^ A / (Real.log 2) ^ (A + 3))
        * x / (Real.log x) ^ A := by
  let K : ℝ := Real.log 4 + 5
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hx0 : 0 ≤ x := by linarith
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogx : 0 < Real.log x := Real.log_pos (by linarith)
  have hloglo : Real.log 2 ≤ Real.log x := Real.log_le_log (by norm_num) hx
  have hloghi : Real.log x ≤ 32 := by
    rw [← Real.log_exp 32]
    exact Real.log_le_log (by positivity) hxE
  have hsqrt : √x ≤ Real.exp 16 := by
    rw [Real.sqrt_le_iff]
    constructor
    · positivity
    · calc x ≤ Real.exp 32 := hxE
        _ = (Real.exp 16) ^ 2 := by rw [pow_two, ← Real.exp_add]; norm_num
  have hQ' : Q ≤ Real.exp 16 / (Real.log 2) ^ (A + 3) := by
    calc Q ≤ √x / (Real.log x) ^ (A + 3) := hQ
      _ ≤ Real.exp 16 / (Real.log 2) ^ (A + 3) := by
        gcongr
  have hterm (q : ℕ) (hq : q ∈ Nat.Icc 1 Q) :
      (⨆ z ∈ Set.Icc 1 x, ⨆ a : (ZMod q)ˣ, |ψ (q := q) z a - z / q.totient|) ≤ K * x := by
    rw [Nat.mem_Icc] at hq
    refine Real.iSup_le (fun z ↦ ?_) (mul_nonneg hK hx0)
    refine Real.iSup_le (fun hz ↦ ?_) (mul_nonneg hK hx0)
    refine Real.iSup_le (fun a ↦ ?_) (mul_nonneg hK hx0)
    exact (abs_psi_sub_div_le (by exact_mod_cast hq.1) hz.1 a).trans
      (mul_le_mul_of_nonneg_left hz.2 hK)
  calc
    ∑ q ∈ Nat.Icc 1 Q, ⨆ z ∈ Set.Icc 1 x, ⨆ a : (ZMod q)ˣ,
          |ψ (q := q) z a - z / q.totient|
        ≤ (Nat.Icc 1 Q).card * (K * x) := by
          calc
            _ ≤ ∑ _q ∈ Nat.Icc 1 Q, K * x :=
              Finset.sum_le_sum fun q hq ↦ hterm q hq
            _ = _ := by simp
    _ ≤ Q * (K * x) := by
      have hc : ((Nat.Icc 1 Q).card : ℝ) ≤ Q := by
        rw [card_natIcc 1 (by linarith : 0 ≤ Q)]
        norm_num
        exact_mod_cast Nat.floor_le (by linarith : 0 ≤ Q)
      exact mul_le_mul_of_nonneg_right hc (mul_nonneg hK hx0)
    _ ≤ (Real.exp 16 / (Real.log 2) ^ (A + 3)) * (K * x) :=
      mul_le_mul_of_nonneg_right hQ' (mul_nonneg hK hx0)
    _ ≤ (K * Real.exp 16 * 32 ^ A / (Real.log 2) ^ (A + 3)) * x /
          (Real.log x) ^ A := by
      have hp : (Real.log x) ^ A ≤ (32 : ℝ) ^ A := by gcongr
      have hden : 0 < (Real.log 2) ^ (A + 3) := pow_pos hlog2 _
      have hlogpow : 0 < (Real.log x) ^ A := pow_pos hlogx _
      rw [le_div_iff₀ hlogpow]
      field_simp [ne_of_gt hden]
      nlinarith

private lemma BV_large [ProofData] (A : ℕ) {Q : ℝ} (hQ0 : 1 ≤ Q)
    (hQ : Q ≤ √x / (Real.log x) ^ (A + 3)) :
    ∑ q ∈ Nat.Icc 1 Q, ⨆ z ∈ Set.Icc 1 x, ⨆ a : (ZMod q)ˣ,
        |ψ (q := q) z a - z / q.totient| ≤
      (|C_BV_L A| + (Real.log 4 + 5) +
        |C_SW (A + 2) 0| * 2 ^ (A + 2) * |C_tot| +
        (Real.log 2)⁻¹ * |C_tot| * (A + 3).factorial) *
          x / (Real.log x) ^ A := by
  let L : ℝ := Real.log x
  let K : ℝ := Real.log 4 + 5
  let R : ℝ := |C_SW (A + 2) 0| * 2 ^ (A + 2) * x / L ^ (A + 2) +
    (Real.log 2)⁻¹ * L ^ 2
  have hL : 1 ≤ L := by simpa [L] using one_le_log_x
  have hL0 : 0 < L := lt_of_lt_of_le (by norm_num) hL
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hx0 : 0 ≤ x := ProofData.x_nonneg
  have hR : 0 ≤ R := by
    dsimp [R]
    exact add_nonneg
      (div_nonneg (mul_nonneg (mul_nonneg (abs_nonneg _) (by positivity)) hx0)
        (pow_nonneg (le_of_lt hL0) _))
      (mul_nonneg (by positivity) (sq_nonneg _))
  have hsqrt_le_x : √x ≤ x := by
    rw [Real.sqrt_le_iff]
    constructor
    · exact hx0
    · nlinarith [ProofData.le_x]
  have hQx : Q ≤ x := by
    calc Q ≤ √x / L ^ (A + 3) := by simpa [L] using hQ
      _ ≤ √x := div_le_self (Real.sqrt_nonneg _) (one_le_pow₀ hL)
      _ ≤ x := hsqrt_le_x
  have hsumφ : ∑ q ∈ Nat.Icc 1 Q, (q.totient : ℝ)⁻¹ ≤ |C_tot| * L := by
    have h := summatory_totient_inv_le Q hQx
    rw [summatory] at h
    exact h.trans (mul_le_mul_of_nonneg_right (le_abs_self C_tot) (by positivity))
  have hsqrt_two : 2 ≤ √x := by
    have h16 := sixteen_le_log_x
    have hx16 : Real.exp 16 ≤ x := by
      rw [← Real.exp_log ProofData.x_pos]
      exact Real.exp_le_exp.mpr h16
    rw [Real.le_sqrt (by norm_num) hx0]
    calc (2 : ℝ) ^ 2 ≤ Real.exp 16 := by
          have he := Real.add_one_le_exp (16 : ℝ)
          norm_num at he ⊢
          linarith
      _ ≤ x := hx16
  have hqterm (q : ℕ) (hqmem : q ∈ Nat.Icc 1 Q) :
      (⨆ z ∈ Set.Icc 1 x, ⨆ a : (ZMod q)ˣ, |ψ (q := q) z a - z / q.totient|) ≤
        maxya q (fun z a ↦ |Δ_[Λ](z; q, a)|) + (q.totient : ℝ)⁻¹ * R + K * √x := by
    rw [Nat.mem_Icc] at hqmem
    have hqpos : 0 < q := by exact_mod_cast hqmem.1
    have hphi0 : 0 ≤ (q.totient : ℝ)⁻¹ := by positivity
    have hM0 : 0 ≤ maxya q (fun z a ↦ |Δ_[Λ](z; q, a)|) +
        (q.totient : ℝ)⁻¹ * R + K * √x := by
      exact add_nonneg (add_nonneg (maxya_nonneg _) (mul_nonneg hphi0 hR))
        (mul_nonneg hK (Real.sqrt_nonneg _))
    refine Real.iSup_le (fun z ↦ ?_) hM0
    refine Real.iSup_le (fun hz ↦ ?_) hM0
    refine Real.iSup_le (fun a ↦ ?_) hM0
    by_cases hzs : √x ≤ z
    · have hqcast : (q : ℝ) ≤ x := hqmem.2.trans hQx
      have hlogq : Real.log q ≤ L := by
        dsimp [L]
        exact Real.log_le_log (by exact_mod_cast hqpos) hqcast
      have hz2 : 2 ≤ z := hsqrt_two.trans hzs
      have herr := coprime_vonMangoldt_error_generic (A + 2) hz2 hqpos
      have hratio := pnt_ratio_bound (A + 2) hzs hz.2
      have herrR :
          |summatory (fun n ↦ if q.Coprime n then Λ n else 0) z - z| ≤ R := by
        refine herr.trans ?_
        dsimp [R, L]
        have hC : C_SW (A + 2) 0 ≤ |C_SW (A + 2) 0| := le_abs_self _
        have hfirst : C_SW (A + 2) 0 * (z / Real.log z ^ (A + 2)) ≤
            |C_SW (A + 2) 0| * (2 ^ (A + 2) * x / Real.log x ^ (A + 2)) := by
          exact mul_le_mul hC hratio
            (div_nonneg (by positivity) (pow_nonneg (Real.log_nonneg (by linarith)) _))
            (abs_nonneg _)
        have hlogq0 : 0 ≤ Real.log q := Real.log_nonneg (by exact_mod_cast hqpos)
        have hsecond : (Real.log 2)⁻¹ * (Real.log q * Real.log z) ≤
            (Real.log 2)⁻¹ * Real.log x ^ 2 := by
          have hlogz : Real.log z ≤ Real.log x :=
            Real.log_le_log (by linarith) hz.2
          gcongr
          nlinarith
        calc
          C_SW (A + 2) 0 * (z / Real.log z ^ (A + 2)) +
              (Real.log 2)⁻¹ * (Real.log q * Real.log z)
              ≤ |C_SW (A + 2) 0| *
                  (2 ^ (A + 2) * x / Real.log x ^ (A + 2)) +
                    (Real.log 2)⁻¹ * Real.log x ^ 2 := add_le_add hfirst hsecond
          _ = |C_SW (A + 2) 0| * 2 ^ (A + 2) * x /
                Real.log x ^ (A + 2) + (Real.log 2)⁻¹ * Real.log x ^ 2 := by ring
      have hid : ψ (q := q) z a - z / q.totient = Δ_[Λ](z; q, a) +
          (q.totient : ℝ)⁻¹ *
            (summatory (fun n ↦ if q.Coprime n then Λ n else 0) z - z) := by
        rw [Delta_Lambda_eq, summatory, Finset.sum_filter]
        ring
      rw [hid]
      calc
        |Δ_[Λ](z; q, a) + (q.totient : ℝ)⁻¹ *
            (summatory (fun n ↦ if q.Coprime n then Λ n else 0) z - z)|
            ≤ |Δ_[Λ](z; q, a)| + (q.totient : ℝ)⁻¹ * R := by
              refine (abs_add_le _ _).trans ?_
              rw [abs_mul, abs_of_nonneg hphi0]
              gcongr
        _ ≤ maxya q (fun z a ↦ |Δ_[Λ](z; q, a)|) +
              (q.totient : ℝ)⁻¹ * R := by
                gcongr
                exact abs_Delta_le_maxya _ a.isUnit hzs hz.2
        _ ≤ _ := le_add_of_nonneg_right (mul_nonneg hK (Real.sqrt_nonneg _))
    · have hzsqrt : z ≤ √x := le_of_not_ge hzs
      calc
        |ψ (q := q) z a - z / q.totient| ≤ K * z :=
          abs_psi_sub_div_le hqpos hz.1 a
        _ ≤ K * √x := mul_le_mul_of_nonneg_left hzsqrt hK
        _ ≤ _ := by
          have hm := maxya_nonneg (fun z a ↦ |Δ_[Λ](z; q, a)|)
          have he := mul_nonneg hphi0 hR
          linarith [mul_nonneg hK (Real.sqrt_nonneg x)]
  have hmain := BV_Delta_Lambda A Q hQ0 hQ
  have hsum :
      ∑ q ∈ Nat.Icc 1 Q, ⨆ z ∈ Set.Icc 1 x, ⨆ a : (ZMod q)ˣ,
          |ψ (q := q) z a - z / q.totient| ≤
        |C_BV_L A| * x / L ^ A + R * (|C_tot| * L) + K * x / L ^ (A + 3) := by
    have hdelta :
        ∑ q ∈ Nat.Icc 1 Q, maxya q (fun z a ↦ |Δ_[Λ](z; q, a)|) ≤
          |C_BV_L A| * x / L ^ A := by
      have hsub : Nat.Icc 1 Q ⊆ Nat.Icc 0 Q := by
        intro q hq
        rw [Nat.mem_Icc] at hq ⊢
        exact ⟨by positivity, hq.2⟩
      have hle : ∑ q ∈ Nat.Icc 1 Q, maxya q (fun z a ↦ |Δ_[Λ](z; q, a)|) ≤
          ∑ q ∈ Nat.Icc 0 Q, maxya q (fun z a ↦ |Δ_[Λ](z; q, a)|) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub
          (fun q _ _ ↦ maxya_nonneg (fun z a ↦ |Δ_[Λ](z; q, a)|))
      have hm : ∑ q ∈ Nat.Icc 0 Q, maxya q (fun z a ↦ |Δ_[Λ](z; q, a)|) ≤
          C_BV_L A * x / L ^ A := by simpa [L] using hmain
      refine hle.trans (hm.trans ?_)
      calc
        C_BV_L A * x / L ^ A = C_BV_L A * (x / L ^ A) := by ring
        _ ≤ |C_BV_L A| * (x / L ^ A) :=
          mul_le_mul_of_nonneg_right (le_abs_self (C_BV_L A))
            (div_nonneg hx0 (pow_nonneg (le_of_lt hL0) _))
        _ = |C_BV_L A| * x / L ^ A := by ring
    have hphi : ∑ q ∈ Nat.Icc 1 Q, (q.totient : ℝ)⁻¹ * R ≤
        R * (|C_tot| * L) := by
      rw [← Finset.sum_mul]
      rw [mul_comm]
      exact mul_le_mul_of_nonneg_left hsumφ hR
    have hcard : ((Nat.Icc 1 Q).card : ℝ) ≤ Q := by
      rw [card_natIcc 1 (by linarith : 0 ≤ Q)]
      norm_num
      exact_mod_cast Nat.floor_le (by linarith : 0 ≤ Q)
    have hsmall : ∑ _q ∈ Nat.Icc 1 Q, K * √x ≤ K * x / L ^ (A + 3) := by
      rw [Finset.sum_const, nsmul_eq_mul]
      calc
        ((Nat.Icc 1 Q).card : ℝ) * (K * √x) ≤ Q * (K * √x) :=
          mul_le_mul_of_nonneg_right hcard (mul_nonneg hK (Real.sqrt_nonneg _))
        _ ≤ (√x / L ^ (A + 3)) * (K * √x) :=
          mul_le_mul_of_nonneg_right (by simpa [L] using hQ)
            (mul_nonneg hK (Real.sqrt_nonneg _))
        _ = K * x / L ^ (A + 3) := by
          field_simp
          nlinarith [Real.sq_sqrt hx0]
    calc
      ∑ q ∈ Nat.Icc 1 Q, ⨆ z ∈ Set.Icc 1 x, ⨆ a : (ZMod q)ˣ,
          |ψ (q := q) z a - z / q.totient|
          ≤ ∑ q ∈ Nat.Icc 1 Q,
              (maxya q (fun z a ↦ |Δ_[Λ](z; q, a)|) +
                (q.totient : ℝ)⁻¹ * R + K * √x) :=
            Finset.sum_le_sum fun q hq ↦ hqterm q hq
      _ = (∑ q ∈ Nat.Icc 1 Q, maxya q (fun z a ↦ |Δ_[Λ](z; q, a)|)) +
            (∑ q ∈ Nat.Icc 1 Q, (q.totient : ℝ)⁻¹ * R) +
              (∑ _q ∈ Nat.Icc 1 Q, K * √x) := by
            simp only [Finset.sum_add_distrib]
      _ ≤ _ := add_le_add (add_le_add hdelta hphi) hsmall
  refine hsum.trans ?_
  have hdrop : x / L ^ (A + 1) ≤ x / L ^ A := by
    apply div_le_div_of_nonneg_left hx0 (pow_pos hL0 _)
    rw [pow_succ]
    exact le_mul_of_one_le_right (pow_nonneg (le_of_lt hL0) _) hL
  have hp :
      (|C_SW (A + 2) 0| * 2 ^ (A + 2) * x / L ^ (A + 2)) *
          (|C_tot| * L) ≤
        (|C_SW (A + 2) 0| * 2 ^ (A + 2) * |C_tot|) * x / L ^ A := by
    have heq :
        (|C_SW (A + 2) 0| * 2 ^ (A + 2) * x / L ^ (A + 2)) *
            (|C_tot| * L) =
          (|C_SW (A + 2) 0| * 2 ^ (A + 2) * |C_tot|) *
            (x / L ^ (A + 1)) := by
      rw [pow_succ]
      field_simp [ne_of_gt hL0]
      ring
    rw [heq]
    calc
      (|C_SW (A + 2) 0| * 2 ^ (A + 2) * |C_tot|) * (x / L ^ (A + 1))
          ≤ (|C_SW (A + 2) 0| * 2 ^ (A + 2) * |C_tot|) * (x / L ^ A) :=
            mul_le_mul_of_nonneg_left hdrop (by positivity)
      _ = (|C_SW (A + 2) 0| * 2 ^ (A + 2) * |C_tot|) * x / L ^ A := by ring
  have hfac : L ^ (A + 3) ≤ ((A + 3).factorial : ℝ) * x := by
    have he := Real.pow_div_factorial_le_exp L (le_of_lt hL0) (A + 3)
    rw [Real.exp_log ProofData.x_pos] at he
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < (A + 3).factorial)] at he
    simpa [mul_comm] using he
  have hthree : L ^ 3 ≤ ((A + 3).factorial : ℝ) * x / L ^ A := by
    rw [le_div_iff₀ (pow_pos hL0 _)]
    rw [← pow_add]
    simpa [add_comm] using hfac
  have hn : ((Real.log 2)⁻¹ * L ^ 2) * (|C_tot| * L) ≤
      ((Real.log 2)⁻¹ * |C_tot| * (A + 3).factorial) * x / L ^ A := by
    calc
      ((Real.log 2)⁻¹ * L ^ 2) * (|C_tot| * L) =
          ((Real.log 2)⁻¹ * |C_tot|) * L ^ 3 := by ring
      _ ≤ ((Real.log 2)⁻¹ * |C_tot|) *
          (((A + 3).factorial : ℝ) * x / L ^ A) :=
            mul_le_mul_of_nonneg_left hthree (by positivity)
      _ = _ := by ring
  have hk : K * x / L ^ (A + 3) ≤ K * x / L ^ A := by
    apply div_le_div_of_nonneg_left (mul_nonneg hK hx0) (pow_pos hL0 _)
    exact pow_le_pow_right₀ hL (by omega)
  dsimp [R]
  calc
    |C_BV_L A| * x / L ^ A +
          (|C_SW (A + 2) 0| * 2 ^ (A + 2) * x / L ^ (A + 2) +
            (Real.log 2)⁻¹ * L ^ 2) * (|C_tot| * L) + K * x / L ^ (A + 3)
        ≤ |C_BV_L A| * x / L ^ A +
            ((|C_SW (A + 2) 0| * 2 ^ (A + 2) * |C_tot|) * x / L ^ A +
              ((Real.log 2)⁻¹ * |C_tot| * (A + 3).factorial) * x / L ^ A) +
                K * x / L ^ A := by
          rw [add_mul]
          gcongr
    _ = (|C_BV_L A| + K +
          |C_SW (A + 2) 0| * 2 ^ (A + 2) * |C_tot| +
          (Real.log 2)⁻¹ * |C_tot| * (A + 3).factorial) * x / L ^ A := by ring

open Nat

@[blueprint "Bombieri-Vinogradov" (statement :=
/--
For each fixed $A \geq 0$,
$$\sum_{q \le Q} \max_{y \le x} \max_{a \in (\mathbb{Z}/q\mathbb{Z})^*} \left| \psi(y; q, a) - \frac{y}{\varphi(q)} \right| \ll_A \frac{x}{(\log x)^{A}}$$

uniformly for all $x \ge 2$ and $1 \le Q \le \frac{\sqrt{x}}{(\log x)^{A+3}}$. -/
) (proof := /--
Apply \ref{BV_Delta_Lambda} and absorb the error terms using \ref{sum_primes_not_dvd_log_eq_id}.
-/) (uses := [BV_Delta_Lambda, sum_primes_not_dvd_log_eq_id])]
theorem bombieri_vinogradov (A : ℕ) {x : ℝ} (hx : 2 ≤ x) {Q : ℝ} (hle_Q : 1 ≤ Q)
    (hQ : Q ≤ √x / (Real.log x)^(A+3)) :
    ∑ q ∈ Nat.Icc 1 Q, ⨆ y ∈ Set.Icc 1 x, ⨆ a : (ZMod q)ˣ, |ψ (q := q) y a - y / φ q|
      ≤ C_BV A * x / (Real.log x)^A := by
  have hx0 : 0 ≤ x := by linarith
  have hlogx : 0 < Real.log x := Real.log_pos (by linarith)
  have hscale : 0 ≤ x / (Real.log x) ^ A :=
    div_nonneg hx0 (pow_nonneg (le_of_lt hlogx) _)
  by_cases hxE : x ≤ Real.exp 32
  · have hc := BV_compact A hx hxE hle_Q hQ
    refine hc.trans ?_
    let D : ℝ := (Real.log 4 + 5) * Real.exp 16 * 32 ^ A /
      Real.log 2 ^ (A + 3)
    have hDC : D ≤ C_BV A := by
      rw [C_BV]
      dsimp [D]
      have hK : 0 ≤ Real.log 4 + 5 := by positivity
      have hcompact : 0 ≤ (Real.log 4 + 5) * Real.exp 16 * 32 ^ A /
          Real.log 2 ^ (A + 3) := by positivity
      have hp : 0 ≤ |C_SW (A + 2) 0| * 2 ^ (A + 2) * |C_tot| := by positivity
      have hn : 0 ≤ (Real.log 2)⁻¹ * |C_tot| * ↑(A + 3).factorial := by positivity
      nlinarith [abs_nonneg (C_BV_L A)]
    change D * x / Real.log x ^ A ≤ C_BV A * x / Real.log x ^ A
    calc
      D * x / Real.log x ^ A = D * (x / Real.log x ^ A) := by ring
      _ ≤ C_BV A * (x / Real.log x ^ A) :=
        mul_le_mul_of_nonneg_right hDC hscale
      _ = C_BV A * x / Real.log x ^ A := by ring
  · have hxE' : Real.exp 32 < x := lt_of_not_ge hxE
    have hlog32 : (32 : ℝ) ≤ Real.log x := by
      have := Real.log_le_log (Real.exp_pos 32) hxE'.le
      simpa using this
    let W : ℝ := Real.exp (Real.sqrt (Real.log x))
    letI : ProofData :=
      { U := W
        V := W
        x := x
        le_x := hx
        UV_le := by
          dsimp [W]
          rw [← Real.exp_add]
          have hsx : 0 < √x := Real.sqrt_pos.2 (by linarith)
          rw [← Real.exp_log hsx, Real.log_sqrt hx0]
          apply Real.exp_le_exp.mpr
          have hs : Real.sqrt (Real.log x) ^ 2 = Real.log x :=
            Real.sq_sqrt (le_of_lt hlogx)
          nlinarith [Real.sqrt_nonneg (Real.log x)]
        le_U := le_rfl
        le_V := le_rfl }
    have hlarge := BV_large A hle_Q hQ
    change (∑ q ∈ Nat.Icc 1 Q, ⨆ y ∈ Set.Icc 1 x, ⨆ a : (ZMod q)ˣ,
      |ψ (q := q) y a - y / φ q|) ≤
        (|C_BV_L A| + (Real.log 4 + 5) +
          |C_SW (A + 2) 0| * 2 ^ (A + 2) * |C_tot| +
          (Real.log 2)⁻¹ * |C_tot| * (A + 3).factorial) * x /
            Real.log x ^ A at hlarge
    refine hlarge.trans ?_
    let E : ℝ := |C_BV_L A| + (Real.log 4 + 5) +
      |C_SW (A + 2) 0| * 2 ^ (A + 2) * |C_tot| +
      (Real.log 2)⁻¹ * |C_tot| * (A + 3).factorial
    have hEC : E ≤ C_BV A := by
      rw [C_BV]
      dsimp [E]
      have hcompact : 0 ≤ (Real.log 4 + 5) * Real.exp 16 * 32 ^ A /
          Real.log 2 ^ (A + 3) := by positivity
      linarith
    change E * x / Real.log x ^ A ≤ C_BV A * x / Real.log x ^ A
    calc
      E * x / Real.log x ^ A = E * (x / Real.log x ^ A) := by ring
      _ ≤ C_BV A * (x / Real.log x ^ A) := mul_le_mul_of_nonneg_right hEC hscale
      _ = C_BV A * x / Real.log x ^ A := by ring

end
