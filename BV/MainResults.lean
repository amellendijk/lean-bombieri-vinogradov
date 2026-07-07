import Mathlib
import Architect

import BV.Defs
import BV.LambdaLE
import BV.LambdaSharp
import BV.LambdaFlat

open ArithmeticFunction

open scoped BV

open ProofData

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
        have : (n : ℤ) = 1 := by rw [hn, h]
        have hn1 : n = 1 := by exact_mod_cast this
        rw [hn1]
        by_cases hU : (1 : ℝ) ≤ U
        · rw [LambdaLEU_apply_of_le (by exact_mod_cast hU)]
          exact ArithmeticFunction.vonMangoldt_apply_one
        · rw [LambdaLEU_apply_of_gt (by push_cast; linarith)]
      · -- a = -1, impossible for a cast of a natural
        exfalso
        have : (n : ℤ) = -1 := by rw [hn, h]
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


/-- Implied constant for Bombieri-Vinogradov theorem -/
noncomputable def C_BV (A : ℕ) : ℝ := sorry

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
    ∑ q ∈ Nat.Icc 1 Q, ⨆ y ∈ Set.Icc 1 x, ⨆ a : (ZMod q)ˣ, |ψ (q := q) y a - x / φ q|
      ≤ C_BV A * x / (Real.log x)^A := by
  sorry

end
