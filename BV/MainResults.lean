import Mathlib
import Architect

import BV.Defs
import BV.LambdaLE
import BV.LambdaSharp
import BV.LambdaFlat
import BV.ForMathlib.Log
import BV.SiegelWalfisz

open ArithmeticFunction

open scoped BV ENNReal

open ProofData
open BV

noncomputable section

/-! ## Bombieri-Vinogradov Theorem

This module contains the formalization of the Bombieri-Vinogradov theorem,
a fundamental result in analytic number theory.
-/


/-! Wrapping up -/

/-- Canonical per-conductor triangle inequality from
`Λ = Λ♯ + Λ♭ + Λ≤U`. -/
theorem maxya_Delta_Lambda_enorm_le [ProofData] (q : ℕ) :
    maxya q (fun y a ↦ ‖Δ_[Λ](y; q, a)‖ₑ) ≤
      maxya q (fun y a ↦ ‖Δ_[Λ♯](y; q, a)‖ₑ) +
        maxya q (fun y a ↦ ‖Δ_[Λ♭](y; q, a)‖ₑ) +
          maxya q (fun y a ↦ ‖Δ_[Λ≤U](y; q, a)‖ₑ) := by
  have hdecomp : (⇑Λ : ℕ → ℝ) = ⇑Λ♯ + ⇑Λ♭ + ⇑Λ≤U := by
    funext n; simpa using Lambda_decomp n
  rw [show (⇑Λ : ℕ → ℝ) = _ from hdecomp]
  exact (maxya_Delta_add_le (⇑Λ♯ + ⇑Λ♭) ⇑Λ≤U q).trans
    (add_le_add (maxya_Delta_add_le ⇑Λ♯ ⇑Λ♭ q) le_rfl)

def C_BV_L (A : ℕ) : ℝ := C_BVLS + C_BV_LF A + 2

open ProofData in
@[blueprint (statement :=
/--
For each fixed $A \ge 0$ we have
$$\sum_{q\le Q} \max_{\sqrt x \le y \le x} \max_{a \in (\mathbb{Z}/q\mathbb{Z})^*} \left| \Delta_{\Lambda}(y; q,a) \right| \ll_A \frac{x}{(\log x)^{A}}$$
uniformly for $x \ge 2$ and $1 \le Q \le \sqrt{x}/(\log (x))^{A+3}$
-/
) (proof := /--
Follows from \ref{Lambda_decomp} and the triangle inequality, combining the canonical bounds
\ref{BV_LambdaLE_enorm}, \ref{BV_LambdaSharp_enorm}, and \ref{BV_LambdaFlat_enorm}.
-/) (uses := [BV_LambdaLE_enorm, BV_LambdaSharp_enorm, BV_LambdaFlat_enorm, Lambda_decomp])]
theorem BV_Delta_Lambda_enorm [ProofData] (A : ℕ) (Q : ℝ) (h1Q : 1 ≤ Q)
    (hQ : Q ≤ √x / (Real.log x) ^ (A + 3)) :
    ∑ q ∈ Finset.Ioc 0 ⌊Q⌋₊,
      maxya q (fun y a ↦ ‖Δ_[Λ](y; q, a)‖ₑ) ≤
        ENNReal.ofReal (C_BV_L A * x / (Real.log x) ^ A) := by
  have hL1 : (1 : ℝ) ≤ Real.log x := one_le_log_x
  have hx0 : (0 : ℝ) ≤ x := ProofData.x_nonneg
  have hQ0 : (0 : ℝ) ≤ Q := by linarith
  have hstep : ∑ q ∈ Finset.Ioc 0 ⌊Q⌋₊,
      maxya q (fun y a ↦ ‖Δ_[Λ](y; q, a)‖ₑ) ≤
      (∑ q ∈ Finset.Ioc 0 ⌊Q⌋₊, maxya q (fun y a ↦ ‖Δ_[Λ♯](y; q, a)‖ₑ))
        + (∑ q ∈ Finset.Ioc 0 ⌊Q⌋₊, maxya q (fun y a ↦ ‖Δ_[Λ♭](y; q, a)‖ₑ))
        + (∑ q ∈ Finset.Ioc 0 ⌊Q⌋₊, maxya q (fun y a ↦ ‖Δ_[Λ≤U](y; q, a)‖ₑ)) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum (fun q _ ↦ maxya_Delta_Lambda_enorm_le q)
  have hsharp : ∑ q ∈ Finset.Ioc 0 ⌊Q⌋₊,
      maxya q (fun y a ↦ ‖Δ_[Λ♯](y; q, a)‖ₑ)
      ≤ ENNReal.ofReal (C_BVLS * (x / (Real.log x)^A)) := BV_LambdaSharp_enorm Q h1Q hQ
  have hflat : ∑ q ∈ Finset.Ioc 0 ⌊Q⌋₊,
      maxya q (fun y a ↦ ‖Δ_[Λ♭](y; q, a)‖ₑ)
      ≤ ENNReal.ofReal (C_BV_LF A * x / (Real.log x)^A) := BV_LambdaFlat_enorm A Q h1Q hQ
  have hLE : ∑ q ∈ Finset.Ioc 0 ⌊Q⌋₊,
      maxya q (fun y a ↦ ‖Δ_[Λ≤U](y; q, a)‖ₑ)
      ≤ ENNReal.ofReal (2 * x / (Real.log x)^(A+2)) := BV_LambdaLE_enorm Q hQ0 hQ
  let Bs := C_BVLS * (x / (Real.log x) ^ A)
  let Bf := C_BV_LF A * x / (Real.log x) ^ A
  let Ble := 2 * x / (Real.log x) ^ (A + 2)
  have hBs : 0 ≤ Bs := by dsimp [Bs, C_BVLS, C_DLS, C_tau]; positivity
  have hBf : 0 ≤ Bf := by
    dsimp [Bf]
    exact div_nonneg (mul_nonneg (C_BV_LF_nonneg A) hx0) (pow_nonneg log_x_pos.le _)
  have hBle : 0 ≤ Ble := by dsimp [Ble]; positivity
  have hpow : (2 : ℝ) * x / (Real.log x)^(A+2) ≤ 2 * x / (Real.log x)^A := by
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    exact pow_le_pow_right₀ hL1 (by omega)
  have hcollect : C_BVLS * (x / (Real.log x)^A) + C_BV_LF A * x / (Real.log x)^A
      + 2 * x / (Real.log x)^A = C_BV_L A * x / (Real.log x)^A := by
    rw [C_BV_L]; ring
  have hreal : Bs + Bf + Ble ≤ C_BV_L A * x / (Real.log x) ^ A := by
    grind
  calc ∑ q ∈ Finset.Ioc 0 ⌊Q⌋₊,
      maxya q (fun y a ↦ ‖Δ_[Λ](y; q, a)‖ₑ)
      ≤ _ := hstep
    _ ≤ ENNReal.ofReal Bs + ENNReal.ofReal Bf + ENNReal.ofReal Ble :=
      add_le_add (add_le_add hsharp hflat) hLE
    _ = ENNReal.ofReal (Bs + Bf + Ble) := by
      symm
      rw [ENNReal.ofReal_add (add_nonneg hBs hBf) hBle, ENNReal.ofReal_add hBs hBf]
    _ ≤ ENNReal.ofReal (C_BV_L A * x / (Real.log x) ^ A) :=
      ENNReal.ofReal_le_ofReal hreal

/-- Implied constant for Bombieri-Vinogradov theorem.  The first summand is the
analytic constant; the second deliberately coarse summand absorbs the compact
range in which no `ProofData` instance exists. -/
noncomputable def C_BV (A : ℕ) : ℝ :=
  |C_BV_L A| + (Real.log 4 + 5) +
    |C_SW (A + 2) 0| * 2 ^ (A + 2) * |C_tot| +
    (Real.log 2)⁻¹ * |C_tot| * (A + 3).factorial +
    (Real.log 4 + 5) * Real.exp 16 * 32 ^ A / (Real.log 2) ^ (A + 3)

/-- Canonical maximum of the modular Chebyshev error on `[1,x]`. -/
noncomputable def psiMaxEnorm (x : ℝ) (q : ℕ) : ℝ≥0∞ :=
  ⨆ y : ℝ, ⨆ (_ : y ∈ Set.Icc 1 x), ⨆ a : (ZMod q)ˣ,
    ‖ψ (q := q) y a - y / q.totient‖ₑ

theorem psiMaxEnorm_le_of_pos {x : ℝ} {q : ℕ} (hq : 0 < q) :
    psiMaxEnorm x q ≤ ENNReal.ofReal ((Real.log 4 + 5) * x) := by
  have hK : 0 ≤ Real.log 4 + 5 := by positivity
  refine iSup_le fun y ↦ ?_
  refine iSup_le fun hy ↦ ?_
  refine iSup_le fun a ↦ ?_
  rw [← BV.ofReal_abs_eq_enorm]
  exact ENNReal.ofReal_le_ofReal ((abs_psi_sub_div_le hq hy.1 a).trans
    (mul_le_mul_of_nonneg_left hy.2 hK))

theorem psiMaxEnorm_ne_top {x : ℝ} {q : ℕ} (hq : 0 < q) :
    psiMaxEnorm x q ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.ofReal_ne_top (psiMaxEnorm_le_of_pos hq)

/-- The finite real view of `psiMaxEnorm` is the former absolute-value supremum. -/
theorem psiMaxEnorm_toReal (x : ℝ) (q : ℕ) :
    (psiMaxEnorm x q).toReal =
      ⨆ y ∈ Set.Icc 1 x, ⨆ a : (ZMod q)ˣ, |ψ (q := q) y a - y / q.totient| := by
  rw [psiMaxEnorm, ENNReal.toReal_iSup]
  · congr with y
    rw [ENNReal.toReal_iSup]
    · congr with hy
      rw [ENNReal.toReal_iSup]
      · simp only [BV.toReal_enorm_real]
      · exact fun _ ↦ enorm_ne_top
    · intro _
      exact iSup_ne_top fun _ ↦ enorm_ne_top
  · intro _
    exact iSup_ne_top fun _ ↦ iSup_ne_top fun _ ↦ enorm_ne_top

private lemma BV_compact_enorm (A : ℕ) {x Q : ℝ} (hx : 2 ≤ x)
    (hxE : x ≤ Real.exp 32) (hQ0 : 1 ≤ Q)
    (hQ : Q ≤ √x / (Real.log x) ^ (A + 3)) :
    ∑ q ∈ Finset.Ioc 0 ⌊Q⌋₊, psiMaxEnorm x q ≤
      ENNReal.ofReal (((Real.log 4 + 5) * Real.exp 16 * 32 ^ A /
        (Real.log 2) ^ (A + 3)) * x / (Real.log x) ^ A) := by
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
  have hterm (q : ℕ) (hq : q ∈ Finset.Ioc 0 ⌊Q⌋₊) :
      psiMaxEnorm x q ≤ ENNReal.ofReal (K * x) := by
    rw [Finset.mem_Ioc_zero_floor] at hq
    simpa [K] using psiMaxEnorm_le_of_pos (by exact_mod_cast hq.1)
  have hreal : ∑ _q ∈ Finset.Ioc 0 ⌊Q⌋₊, K * x ≤
      (K * Real.exp 16 * 32 ^ A / (Real.log 2) ^ (A + 3)) * x /
        (Real.log x) ^ A := by
    calc
    ∑ _q ∈ Finset.Ioc 0 ⌊Q⌋₊, K * x
        = (Finset.Ioc 0 ⌊Q⌋₊).card * (K * x) := by simp
    _ ≤ Q * (K * x) := by
      have hc : ((Finset.Ioc 0 ⌊Q⌋₊).card : ℝ) ≤ Q := by
        simpa using Nat.floor_le (by linarith : 0 ≤ Q)
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
  calc
    ∑ q ∈ Finset.Ioc 0 ⌊Q⌋₊, psiMaxEnorm x q
        ≤ ∑ _q ∈ Finset.Ioc 0 ⌊Q⌋₊, ENNReal.ofReal (K * x) :=
          Finset.sum_le_sum fun q hq ↦ hterm q hq
    _ = ENNReal.ofReal (∑ _q ∈ Finset.Ioc 0 ⌊Q⌋₊, K * x) := by
      rw [ENNReal.ofReal_sum_of_nonneg (fun _ _ ↦ mul_nonneg hK hx0)]
    _ ≤ ENNReal.ofReal (((Real.log 4 + 5) * Real.exp 16 * 32 ^ A /
        (Real.log 2) ^ (A + 3)) * x / (Real.log x) ^ A) := by
      dsimp [K] at hreal ⊢
      exact ENNReal.ofReal_le_ofReal hreal

private lemma BV_large_enorm [ProofData] (A : ℕ) {Q : ℝ} (hQ0 : 1 ≤ Q)
    (hQ : Q ≤ √x / (Real.log x) ^ (A + 3)) :
    ∑ q ∈ Finset.Ioc 0 ⌊Q⌋₊, psiMaxEnorm x q ≤
      ENNReal.ofReal ((|C_BV_L A| + (Real.log 4 + 5) +
        |C_SW (A + 2) 0| * 2 ^ (A + 2) * |C_tot| +
        (Real.log 2)⁻¹ * |C_tot| * (A + 3).factorial) *
          x / (Real.log x) ^ A) := by
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
  have hsumφ : ∑ q ∈ Finset.Ioc 0 ⌊Q⌋₊, (q.totient : ℝ)⁻¹ ≤ |C_tot| * L := by
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
          grind
      _ ≤ x := hx16
  have hqterm (q : ℕ) (hqmem : q ∈ Finset.Ioc 0 ⌊Q⌋₊) :
      psiMaxEnorm x q ≤
        maxya q (fun z a ↦ ‖Δ_[Λ](z; q, a)‖ₑ) +
          ENNReal.ofReal ((q.totient : ℝ)⁻¹ * R) + ENNReal.ofReal (K * √x) := by
    rw [Finset.mem_Ioc_zero_floor] at hqmem
    have hqpos : 0 < q := by exact_mod_cast hqmem.1
    have hphi0 : 0 ≤ (q.totient : ℝ)⁻¹ := by positivity
    refine iSup_le fun z ↦ ?_
    refine iSup_le fun hz ↦ ?_
    refine iSup_le fun a ↦ ?_
    by_cases hzs : √x ≤ z
    · have hqcast : (q : ℝ) ≤ x := hqmem.2.trans hQx
      have hlogq : Real.log q ≤ L := by
        dsimp [L]
        exact Real.log_le_log (by exact_mod_cast hqpos) hqcast
      have hz2 : 2 ≤ z := hsqrt_two.trans hzs
      have herr := coprime_vonMangoldt_error (A + 2) hz2 hqpos
      have hratio := pnt_ratio_bound x z (A + 2) (by linarith) hz.2 hzs
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
      have hid := psi_sub_div_eq_Delta_add z q a
      rw [hid]
      calc
        ‖Δ_[Λ](z; q, a) + (q.totient : ℝ)⁻¹ *
            (summatory (fun n ↦ if q.Coprime n then Λ n else 0) z - z)‖ₑ
            ≤ ‖Δ_[Λ](z; q, a)‖ₑ +
              ‖(q.totient : ℝ)⁻¹ *
                (summatory (fun n ↦ if q.Coprime n then Λ n else 0) z - z)‖ₑ :=
              enorm_add_le _ _
        _ ≤ maxya q (fun z a ↦ ‖Δ_[Λ](z; q, a)‖ₑ) +
              ENNReal.ofReal ((q.totient : ℝ)⁻¹ * R) := by
            apply add_le_add (Delta_enorm_le_maxya _ a.isUnit hzs hz.2)
            rw [← BV.ofReal_abs_eq_enorm, abs_mul, abs_of_nonneg hphi0]
            exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left herrR hphi0)
        _ ≤ _ := le_add_right le_rfl
    · have hzsqrt : z ≤ √x := le_of_not_ge hzs
      calc
        ‖ψ (q := q) z a - z / q.totient‖ₑ ≤ ENNReal.ofReal (K * z) := by
          rw [← BV.ofReal_abs_eq_enorm]
          exact ENNReal.ofReal_le_ofReal (abs_psi_sub_div_le hqpos hz.1 a)
        _ ≤ ENNReal.ofReal (K * √x) :=
          ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hzsqrt hK)
        _ ≤ _ := by
          refine (show ENNReal.ofReal (K * √x) ≤
            0 + 0 + ENNReal.ofReal (K * √x) by simp).trans ?_
          exact add_le_add (add_le_add bot_le bot_le) le_rfl
  have hmain := BV_Delta_Lambda_enorm A Q hQ0 hQ
  have hsum :
      ∑ q ∈ Finset.Ioc 0 ⌊Q⌋₊, psiMaxEnorm x q ≤
        ENNReal.ofReal (|C_BV_L A| * x / L ^ A +
          R * (|C_tot| * L) + K * x / L ^ (A + 3)) := by
    have hdelta :
        ∑ q ∈ Finset.Ioc 0 ⌊Q⌋₊,
          maxya q (fun z a ↦ ‖Δ_[Λ](z; q, a)‖ₑ) ≤
          ENNReal.ofReal (|C_BV_L A| * x / L ^ A) := by
      refine hmain.trans (ENNReal.ofReal_le_ofReal ?_)
      calc C_BV_L A * x / L ^ A = C_BV_L A * (x / L ^ A) := by ring
        _ ≤ |C_BV_L A| * (x / L ^ A) :=
          mul_le_mul_of_nonneg_right (le_abs_self (C_BV_L A))
            (div_nonneg hx0 (pow_nonneg (le_of_lt hL0) _))
        _ = |C_BV_L A| * x / L ^ A := by ring
    have hphi : ∑ q ∈ Finset.Ioc 0 ⌊Q⌋₊, (q.totient : ℝ)⁻¹ * R ≤
        R * (|C_tot| * L) := by
      rw [← Finset.sum_mul]
      rw [mul_comm]
      exact mul_le_mul_of_nonneg_left hsumφ hR
    have hcard : ((Finset.Ioc 0 ⌊Q⌋₊).card : ℝ) ≤ Q := by
      simpa using Nat.floor_le (by linarith : 0 ≤ Q)
    have hsmall : ∑ _q ∈ Finset.Ioc 0 ⌊Q⌋₊, K * √x ≤ K * x / L ^ (A + 3) := by
      rw [Finset.sum_const, nsmul_eq_mul]
      calc
        ((Finset.Ioc 0 ⌊Q⌋₊).card : ℝ) * (K * √x) ≤ Q * (K * √x) :=
          mul_le_mul_of_nonneg_right hcard (mul_nonneg hK (Real.sqrt_nonneg _))
        _ ≤ (√x / L ^ (A + 3)) * (K * √x) :=
          mul_le_mul_of_nonneg_right (by simpa [L] using hQ)
            (mul_nonneg hK (Real.sqrt_nonneg _))
        _ = K * x / L ^ (A + 3) := by
          grind
    have hphiE : ∑ q ∈ Finset.Ioc 0 ⌊Q⌋₊,
        ENNReal.ofReal ((q.totient : ℝ)⁻¹ * R) ≤
          ENNReal.ofReal (R * (|C_tot| * L)) := by
      rw [← ENNReal.ofReal_sum_of_nonneg]
      · exact ENNReal.ofReal_le_ofReal hphi
      · intro q _
        exact mul_nonneg (by positivity) hR
    have hsmallE : ∑ _q ∈ Finset.Ioc 0 ⌊Q⌋₊, ENNReal.ofReal (K * √x) ≤
        ENNReal.ofReal (K * x / L ^ (A + 3)) := by
      rw [← ENNReal.ofReal_sum_of_nonneg]
      · exact ENNReal.ofReal_le_ofReal hsmall
      · intro _ _
        exact mul_nonneg hK (Real.sqrt_nonneg _)
    have hBd : 0 ≤ |C_BV_L A| * x / L ^ A := by positivity
    have hBp : 0 ≤ R * (|C_tot| * L) :=
      mul_nonneg hR (mul_nonneg (abs_nonneg _) hL0.le)
    have hBk : 0 ≤ K * x / L ^ (A + 3) := by positivity
    calc
      ∑ q ∈ Finset.Ioc 0 ⌊Q⌋₊, psiMaxEnorm x q
          ≤ ∑ q ∈ Finset.Ioc 0 ⌊Q⌋₊,
              (maxya q (fun z a ↦ ‖Δ_[Λ](z; q, a)‖ₑ) +
                ENNReal.ofReal ((q.totient : ℝ)⁻¹ * R) + ENNReal.ofReal (K * √x)) :=
            Finset.sum_le_sum fun q hq ↦ hqterm q hq
      _ = (∑ q ∈ Finset.Ioc 0 ⌊Q⌋₊,
              maxya q (fun z a ↦ ‖Δ_[Λ](z; q, a)‖ₑ)) +
            (∑ q ∈ Finset.Ioc 0 ⌊Q⌋₊, ENNReal.ofReal ((q.totient : ℝ)⁻¹ * R)) +
              (∑ _q ∈ Finset.Ioc 0 ⌊Q⌋₊, ENNReal.ofReal (K * √x)) := by
            simp only [Finset.sum_add_distrib]
      _ ≤ ENNReal.ofReal (|C_BV_L A| * x / L ^ A) +
          ENNReal.ofReal (R * (|C_tot| * L)) + ENNReal.ofReal (K * x / L ^ (A + 3)) :=
        add_le_add (add_le_add hdelta hphiE) hsmallE
      _ = ENNReal.ofReal (|C_BV_L A| * x / L ^ A +
          R * (|C_tot| * L) + K * x / L ^ (A + 3)) := by
        symm
        rw [ENNReal.ofReal_add (add_nonneg hBd hBp) hBk, ENNReal.ofReal_add hBd hBp]
  refine hsum.trans (ENNReal.ofReal_le_ofReal ?_)
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
      grind
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
    grind
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
  grind

open Nat

@[blueprint "Bombieri-Vinogradov" (statement :=
/--
For each fixed $A \geq 0$,
$$\sum_{q \le Q} \max_{y \le x} \max_{a \in (\mathbb{Z}/q\mathbb{Z})^*} \left| \psi(y; q, a) - \frac{y}{\varphi(q)} \right| \ll_A \frac{x}{(\log x)^{A}}$$

uniformly for all $x \ge 2$ and $1 \le Q \le \frac{\sqrt{x}}{(\log x)^{A+3}}$. -/
) (proof := /--
Apply \ref{BV_Delta_Lambda_enorm} and absorb the explicit coprimality error.
-/) (uses := [BV_Delta_Lambda_enorm, coprime_vonMangoldt_error])]
theorem bombieri_vinogradov_enorm (A : ℕ) {x : ℝ} (hx : 2 ≤ x) {Q : ℝ} (hle_Q : 1 ≤ Q)
    (hQ : Q ≤ √x / (Real.log x)^(A+3)) :
    ∑ q ∈ Finset.Ioc 0 ⌊Q⌋₊, ⨆ y : ℝ, ⨆ (_ : y ∈ Set.Icc 1 x), ⨆ a : (ZMod q)ˣ,
      ‖ψ (q := q) y a - y / φ q‖ₑ ≤
        ENNReal.ofReal (C_BV A * x / (Real.log x)^A) := by
  change ∑ q ∈ Finset.Ioc 0 ⌊Q⌋₊, psiMaxEnorm x q ≤
    ENNReal.ofReal (C_BV A * x / Real.log x ^ A)
  have hx0 : 0 ≤ x := by linarith
  have hlogx : 0 < Real.log x := Real.log_pos (by linarith)
  have hscale : 0 ≤ x / (Real.log x) ^ A :=
    div_nonneg hx0 (pow_nonneg (le_of_lt hlogx) _)
  by_cases hxE : x ≤ Real.exp 32
  · have hc := BV_compact_enorm A hx hxE hle_Q hQ
    refine hc.trans (ENNReal.ofReal_le_ofReal ?_)
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
    have hlarge := BV_large_enorm A hle_Q hQ
    refine hlarge.trans (ENNReal.ofReal_le_ofReal ?_)
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

/-- Finite real view of `bombieri_vinogradov_enorm`. -/
theorem bombieri_vinogradov (A : ℕ) {x : ℝ} (hx : 2 ≤ x) {Q : ℝ}
    (hle_Q : 1 ≤ Q) (hQ : Q ≤ √x / (Real.log x) ^ (A + 3)) :
    ∑ q ∈ Finset.Ioc 0 ⌊Q⌋₊, ⨆ y ∈ Set.Icc 1 x, ⨆ a : (ZMod q)ˣ,
      |ψ (q := q) y a - y / φ q| ≤ C_BV A * x / (Real.log x) ^ A := by
  have hcanon := bombieri_vinogradov_enorm A hx hle_Q hQ
  change ∑ q ∈ Finset.Ioc 0 ⌊Q⌋₊, psiMaxEnorm x q ≤
    ENNReal.ofReal (C_BV A * x / Real.log x ^ A) at hcanon
  have hfin (q : ℕ) (hq : q ∈ Finset.Ioc 0 ⌊Q⌋₊) : psiMaxEnorm x q ≠ ⊤ := by
    rw [Finset.mem_Ioc_zero_floor] at hq
    exact psiMaxEnorm_ne_top (by exact_mod_cast hq.1)
  have hC : 0 ≤ C_BV A := by rw [C_BV]; positivity
  have hRHS : 0 ≤ C_BV A * x / Real.log x ^ A :=
    div_nonneg (mul_nonneg hC (by linarith))
      (pow_nonneg (Real.log_pos (by linarith)).le _)
  have hto := ENNReal.toReal_mono ENNReal.ofReal_ne_top hcanon
  rw [BV.toReal_finset_sum (Finset.Ioc 0 ⌊Q⌋₊) (fun q ↦ psiMaxEnorm x q) hfin,
    ENNReal.toReal_ofReal hRHS] at hto
  simpa only [psiMaxEnorm_toReal] using hto

end
