import Mathlib
import Architect
import BV.Delta
import BV.Dilate

open ArithmeticFunction BV ProofData
open scoped Moebius zeta

def C_DLS : ℝ := sorry

/-! ### Group D: `Δ` is linear in its function argument -/

theorem Delta_sub {R : Type*} [Field R] (f g : ℕ → R) (x : ℝ) (q : ℕ) (a : ZMod q) :
    Δ_[f - g](x; q, a) = Δ_[f](x; q, a) - Δ_[g](x; q, a) := by
  sorry

theorem Delta_smul {R : Type*} [Field R] (c : R) (f : ℕ → R) (x : ℝ) (q : ℕ) (a : ZMod q) :
    Δ_[c • f](x; q, a) = c • Δ_[f](x; q, a) := by
  sorry

theorem Delta_add {R : Type*} [Field R] (f g : ℕ → R) (x : ℝ) (q : ℕ) (a : ZMod q) :
    Δ_[f + g](x; q, a) = Δ_[f](x; q, a) + Δ_[g](x; q, a) := by
  have hind : (Nat.modEqs (a : ZMod q)).indicator (f + g)
      = fun n => (Nat.modEqs (a : ZMod q)).indicator f n
          + (Nat.modEqs (a : ZMod q)).indicator g n := by
    funext n; by_cases h : n ∈ Nat.modEqs (a : ZMod q) <;> simp [h]
  have hcop : onCoprime q (f + g)
      = fun n => onCoprime q f n + onCoprime q g n := by
    funext n; simp only [onCoprime, Pi.add_apply]; split_ifs <;> simp
  simp only [Delta, hind, hcop, summatory_add_distrib]
  ring

theorem Delta_finset_sum {R : Type*} [Field R] {ι : Type*} (s : Finset ι) (F : ι → ℕ → R)
    (x : ℝ) (q : ℕ) (a : ZMod q) :
    Δ_[∑ i ∈ s, F i](x; q, a) = ∑ i ∈ s, Δ_[F i](x; q, a) := by
  sorry

/-! ### Group C: Möbius expansion of the restricted analytic factor

Stated at the coerced `ℕ → ℝ` level (where `ℝ`-scalar multiplication exists, unlike
on `ArithmeticFunction ℝ`). Convolving the coefficient function `H` with the restricted
`ζ`/`log` produces a `∑_{e ∣ r}` of dilations of `H * ζ` / `H * log`, with the real
coefficients `μ(e)` and `log e` sitting outside the arithmetic functions. -/

theorem mul_zeta_on_coprime_coe (r : ℕ) (H : ArithmeticFunction ℝ) :
    (⇑(H * (ζ : ArithmeticFunction ℝ).on {k | r.Coprime k}) : ℕ → ℝ)
      = ∑ e ∈ r.divisors,
          (μ e : ℝ) • (⇑(dilate e H * (ζ : ArithmeticFunction ℝ)) : ℕ → ℝ) := by
  sorry

theorem mul_log_on_coprime_coe (r : ℕ) (H : ArithmeticFunction ℝ) :
    (⇑(H * (log : ArithmeticFunction ℝ).on {k | r.Coprime k}) : ℕ → ℝ)
      = ∑ e ∈ r.divisors,
          (((μ e : ℝ) * Real.log e) • (⇑(dilate e H * (ζ : ArithmeticFunction ℝ)) : ℕ → ℝ)
            + (μ e : ℝ) • (⇑(dilate e H * (log : ArithmeticFunction ℝ)) : ℕ → ℝ)) := by
  sorry

/-! ### `Δ`-bound for a single dilated summand (flog bound + dilation `ℓ¹` preservation) -/

theorem Delta_dilate_flog_bound {v e : ℕ} (he : 0 < e) (h : ArithmeticFunction ℝ)
    {x : ℝ} (hx : 2 ≤ x) {q : ℕ} [NeZero q] (a : ZMod q) (ha : IsUnit a) :
    |Δ_[⇑(dilate e h * ppow log v)](x; q, a)|
      ≤ 2 * (Real.log x) ^ v * summatory (fun k => |h k|) x := by
  rw [← Real.norm_eq_abs]
  refine le_trans (Delta_flog_bound (f := dilate e h) hx a ha) ?_
  have hpow : (0:ℝ) ≤ 2 * (Real.log x) ^ v := by
    have : (0:ℝ) ≤ Real.log x := Real.log_nonneg (by linarith)
    positivity
  exact mul_le_mul_of_nonneg_left (summatory_abs_dilate_le he h) hpow

/-! ### Group E (specialised `ℓ¹` bounds) -/

/-- `‖μ_{≤V}‖₁ ≤ V`: `|μ| ≤ 1` on the `≤ V` supported values. -/
theorem summatory_abs_moebiusLEV_le [ProofData] {x : ℝ} :
    summatory (fun k => |(μ≤V : ArithmeticFunction ℝ) k|) x ≤ V := by
  refine le_trans (le_abs_self _) ?_
  rw [← Real.norm_eq_abs]
  refine le_trans (summatory_le_support_mul_UB x V ProofData.V_nonneg 1 ?_ ?_) (by simp)
  · -- `|μ_{≤V}(n)| ≤ 1` everywhere.
    intro n _
    rw [Real.norm_eq_abs, abs_abs]
    by_cases hn : n ∈ Set.Icc 1 (Nat.floor V)
    · rw [moebiusLEV, on_apply_of_mem _ _ _ hn, ArithmeticFunction.intCoe_apply]
      exact_mod_cast ArithmeticFunction.abs_moebius_le_one
    · rw [moebiusLEV, on_apply_of_not_mem _ _ _ hn, abs_zero]
      exact zero_le_one
  · -- `μ_{≤V}` vanishes beyond `V`.
    intro n hn
    have : (μ≤V : ArithmeticFunction ℝ) n = 0 := by
      rw [moebiusLEV, on_apply_of_not_mem]
      simp only [Set.mem_Icc, not_and, not_le]
      intro _
      rw [Nat.floor_lt V_nonneg]
      exact hn
    simp [this]

/-- `‖Λ_{≤U}‖₁ ≤ U·log x`: `Λ(k) ≤ log k ≤ log x` on the `≤ U` supported values
(`vonMangoldt_le_log`); the extra `log` is absorbed by the target `UV log x`. -/
theorem summatory_abs_LambdaLEU_le [ProofData] {x : ℝ} (hx : 2 ≤ x) :
    summatory (fun k => |(Λ≤U : ArithmeticFunction ℝ) k|) x ≤ U * Real.log x := by
  have hx0 : (0:ℝ) ≤ Real.log x := Real.log_nonneg (by linarith)
  refine le_trans (le_abs_self _) ?_
  rw [← Real.norm_eq_abs]
  rcases le_total U x with hUx | hxU
  · -- `U ≤ x`: the support has `≤ U` points, each of size `≤ log x`.
    refine summatory_le_support_mul_UB x U ProofData.U_nonneg (Real.log x) ?_ ?_
    · intro n hn
      rw [Real.norm_eq_abs, abs_abs, abs_of_nonneg LambdaLEU_nonneg, LambdaLEU_apply_of_le hn]
      calc Λ n ≤ Real.log n := vonMangoldt_le_log
        _ ≤ Real.log x := by
          rcases Nat.eq_zero_or_pos n with hn0 | hn0
          · simpa [hn0] using hx0
          · exact Real.log_le_log (by exact_mod_cast hn0) (le_trans hn hUx)
    · intro n hn
      rw [LambdaLEU_apply_of_gt hn, abs_zero]
  · -- `x ≤ U`: the range has `≤ x` points, each of size `≤ log x`.
    refine le_trans (summatory_le_UB x (by linarith) (Real.log x) ?_) (by gcongr)
    intro n hn
    rw [Real.norm_eq_abs, abs_abs, abs_of_nonneg LambdaLEU_nonneg]
    by_cases hnU : (n : ℝ) ≤ U
    · rw [LambdaLEU_apply_of_le hnU]
      calc Λ n ≤ Real.log n := vonMangoldt_le_log
        _ ≤ Real.log x := by
          rcases Nat.eq_zero_or_pos n with hn0 | hn0
          · simpa [hn0] using hx0
          · exact Real.log_le_log (by exact_mod_cast hn0) hn
    · rw [LambdaLEU_apply_of_gt (lt_of_not_ge hnU)]; exact hx0

/-! ### Group F: the two term bounds -/

/-- Term 1 of `Λ♯`: `μ_{≤V} * log`, restricted to coprimes of `r`. -/
theorem Delta_term1_bound [ProofData] {q r : ℕ} [NeZero q] {a : ZMod q}
    (ha : IsUnit a) (hr : r ≤ x) {y : ℝ} (h2y : 2 ≤ y) (hy : y ≤ x) :
    |Δ_[onCoprime r ⇑(μ≤V * log)](y; q, a)| ≤ 4 * (r.divisors.card : ℝ) * V * Real.log x := by
  have hV : (0:ℝ) ≤ V := ProofData.V_nonneg
  have hsat : ∀ a b : ℕ, a * b ∈ {n | r.Coprime n}
      ↔ a ∈ {n | r.Coprime n} ∧ b ∈ {n | r.Coprime n} := by
    intro a b
    simp only [Set.mem_setOf_eq]
    exact Nat.coprime_mul_iff_right
  -- Möbius-expand the restricted `μ≤V * log` as a divisor sum of dilated `· * ζ` and `· * log`.
  have hfun : onCoprime r ⇑(μ≤V * log)
      = ∑ e ∈ r.divisors,
          ((((μ e : ℝ) * Real.log e) • (⇑(dilate e ((μ≤V).on {n | r.Coprime n})
              * (ζ : ArithmeticFunction ℝ)) : ℕ → ℝ))
            + ((μ e : ℝ) • (⇑(dilate e ((μ≤V).on {n | r.Coprime n})
              * (log : ArithmeticFunction ℝ)) : ℕ → ℝ))) := by
    rw [onCoprime_eq_on_coe, ArithmeticFunction.on_mul_of_saturated _ hsat]
    exact mul_log_on_coprime_coe r _
  rw [hfun, Delta_finset_sum]
  calc |∑ e ∈ r.divisors,
          Δ_[(((μ e : ℝ) * Real.log e) • (⇑(dilate e ((μ≤V).on {n | r.Coprime n})
              * (ζ : ArithmeticFunction ℝ)) : ℕ → ℝ))
            + ((μ e : ℝ) • (⇑(dilate e ((μ≤V).on {n | r.Coprime n})
              * (log : ArithmeticFunction ℝ)) : ℕ → ℝ))](y; q, a)|
      ≤ ∑ e ∈ r.divisors,
          |Δ_[(((μ e : ℝ) * Real.log e) • (⇑(dilate e ((μ≤V).on {n | r.Coprime n})
              * (ζ : ArithmeticFunction ℝ)) : ℕ → ℝ))
            + ((μ e : ℝ) • (⇑(dilate e ((μ≤V).on {n | r.Coprime n})
              * (log : ArithmeticFunction ℝ)) : ℕ → ℝ))](y; q, a)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _e ∈ r.divisors, 4 * V * Real.log x := by
        apply Finset.sum_le_sum
        intro e he
        have he' : 0 < e := Nat.pos_of_mem_divisors he
        obtain ⟨hedvd, hr0⟩ := Nat.mem_divisors.mp he
        have hle_er : e ≤ r := Nat.le_of_dvd (Nat.pos_of_ne_zero hr0) hedvd
        have hex : (e : ℝ) ≤ x := le_trans (by exact_mod_cast hle_er) hr
        have hloge0 : 0 ≤ Real.log e := Real.log_nonneg (by exact_mod_cast he')
        have hloge : Real.log e ≤ Real.log x := Real.log_le_log (by exact_mod_cast he') hex
        have hlogx0 : 0 ≤ Real.log x := le_trans hloge0 hloge
        have hμ : |(μ e : ℝ)| ≤ 1 := by exact_mod_cast ArithmeticFunction.abs_moebius_le_one
        -- `ℓ¹` bound for the restricted coefficient function
        have hHbound : summatory (fun k => |((μ≤V).on {n | r.Coprime n}) k|) y ≤ V := by
          have e1 : summatory (fun k => |((μ≤V).on {n | r.Coprime n}) k|) y
              ≤ summatory (fun k => |(μ≤V) k|) y := summatory_abs_on_le _ _
          have e4 : summatory (fun k => |(μ≤V) k|) y ≤ V := summatory_abs_moebiusLEV_le
          linarith
        have hHnn : (0:ℝ) ≤ summatory (fun k => |((μ≤V).on {n | r.Coprime n}) k|) y := by
          positivity
        -- `ζ`-part bound (`v = 0`)
        have hΔζ : |Δ_[⇑(dilate e ((μ≤V).on {n | r.Coprime n})
            * (ζ : ArithmeticFunction ℝ))](y; q, a)| ≤ 2 * V := by
          rw [show (ζ : ArithmeticFunction ℝ) = log.ppow 0 from ppow_zero.symm]
          have hflog := Delta_dilate_flog_bound (v := 0) he'
            ((μ≤V).on {n | r.Coprime n}) h2y a ha
          rw [pow_zero, mul_one] at hflog
          calc |Δ_[⇑(dilate e ((μ≤V).on {n | r.Coprime n}) * log.ppow 0)](y; q, a)|
              ≤ 2 * summatory (fun k => |((μ≤V).on {n | r.Coprime n}) k|) y := hflog
            _ ≤ 2 * V := by linarith
        -- `log`-part bound (`v = 1`)
        have hΔlog : |Δ_[⇑(dilate e ((μ≤V).on {n | r.Coprime n})
            * (log : ArithmeticFunction ℝ))](y; q, a)| ≤ 2 * Real.log x * V := by
          rw [show (log : ArithmeticFunction ℝ) = log.ppow 1 from ArithmeticFunction.ppow_one.symm]
          have hflog := Delta_dilate_flog_bound (v := 1) he'
            ((μ≤V).on {n | r.Coprime n}) h2y a ha
          rw [pow_one] at hflog
          have hlogy0 : 0 ≤ Real.log y := Real.log_nonneg (by linarith)
          have hlogxy : Real.log y ≤ Real.log x := Real.log_le_log (by linarith) hy
          calc |Δ_[⇑(dilate e ((μ≤V).on {n | r.Coprime n}) * log.ppow 1)](y; q, a)|
              ≤ 2 * Real.log y * summatory (fun k => |((μ≤V).on {n | r.Coprime n}) k|) y := hflog
            _ ≤ 2 * Real.log x * V := by
                have key : Real.log y * summatory (fun k => |((μ≤V).on {n | r.Coprime n}) k|) y
                    ≤ Real.log x * V := mul_le_mul hlogxy hHbound hHnn hlogx0
                linarith
        -- the coefficient `|μ(e) · log e| ≤ log x`
        have hcoeff1 : |(μ e : ℝ) * Real.log e| ≤ Real.log x := by
          rw [abs_mul, abs_of_nonneg hloge0]
          calc |(μ e : ℝ)| * Real.log e ≤ 1 * Real.log e := by gcongr
            _ = Real.log e := one_mul _
            _ ≤ Real.log x := hloge
        -- combine: each summand is bounded by `4 V log x`
        rw [Delta_add, Delta_smul, Delta_smul, smul_eq_mul, smul_eq_mul]
        calc |(μ e : ℝ) * Real.log e * Δ_[⇑(dilate e ((μ≤V).on {n | r.Coprime n})
                * (ζ : ArithmeticFunction ℝ))](y; q, a)
              + (μ e : ℝ) * Δ_[⇑(dilate e ((μ≤V).on {n | r.Coprime n})
                * (log : ArithmeticFunction ℝ))](y; q, a)|
            ≤ |(μ e : ℝ) * Real.log e * Δ_[⇑(dilate e ((μ≤V).on {n | r.Coprime n})
                * (ζ : ArithmeticFunction ℝ))](y; q, a)|
              + |(μ e : ℝ) * Δ_[⇑(dilate e ((μ≤V).on {n | r.Coprime n})
                * (log : ArithmeticFunction ℝ))](y; q, a)| := abs_add_le _ _
          _ ≤ Real.log x * (2 * V) + 1 * (2 * Real.log x * V) := by
                apply add_le_add
                · calc |(μ e : ℝ) * Real.log e * Δ_[⇑(dilate e ((μ≤V).on {n | r.Coprime n})
                          * (ζ : ArithmeticFunction ℝ))](y; q, a)|
                      = |(μ e : ℝ) * Real.log e| * |Δ_[⇑(dilate e ((μ≤V).on {n | r.Coprime n})
                          * (ζ : ArithmeticFunction ℝ))](y; q, a)| := abs_mul _ _
                    _ ≤ Real.log x * (2 * V) := mul_le_mul hcoeff1 hΔζ (abs_nonneg _) hlogx0
                · calc |(μ e : ℝ) * Δ_[⇑(dilate e ((μ≤V).on {n | r.Coprime n})
                          * (log : ArithmeticFunction ℝ))](y; q, a)|
                      = |(μ e : ℝ)| * |Δ_[⇑(dilate e ((μ≤V).on {n | r.Coprime n})
                          * (log : ArithmeticFunction ℝ))](y; q, a)| := abs_mul _ _
                    _ ≤ 1 * (2 * Real.log x * V) := mul_le_mul hμ hΔlog (abs_nonneg _) (by norm_num)
          _ = 4 * V * Real.log x := by ring
    _ = (r.divisors.card : ℝ) * (4 * V * Real.log x) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ = 4 * (r.divisors.card : ℝ) * V * Real.log x := by ring

/-- Term 2 of `Λ♯`: `Λ_{≤U} * μ_{≤V} * ζ`, restricted to coprimes of `r`. -/
theorem Delta_term2_bound [ProofData] {q r : ℕ} [NeZero q] {a : ZMod q}
    (ha : IsUnit a) (hr : r ≤ x) {y : ℝ} (h2y : 2 ≤ y) (hy : y ≤ x) :
    |Δ_[onCoprime r ⇑(Λ≤U * μ≤V * (ζ : ArithmeticFunction ℝ))](y; q, a)|
      ≤ 2 * (r.divisors.card : ℝ) * U * V * Real.log x := by
  have hU : (0:ℝ) ≤ U := ProofData.U_nonneg
  have hV : (0:ℝ) ≤ V := ProofData.V_nonneg
  have hsat : ∀ a b : ℕ, a * b ∈ {n | r.Coprime n}
      ↔ a ∈ {n | r.Coprime n} ∧ b ∈ {n | r.Coprime n} := by
    intro a b
    simp only [Set.mem_setOf_eq]
    exact Nat.coprime_mul_iff_right
  -- rewrite the restricted function as a divisor sum of dilated `· * ζ`
  have hfun : onCoprime r ⇑(Λ≤U * μ≤V * (ζ : ArithmeticFunction ℝ))
      = ∑ e ∈ r.divisors,
          (μ e : ℝ) • (⇑(dilate e ((Λ≤U * μ≤V).on {n | r.Coprime n})
            * (ζ : ArithmeticFunction ℝ)) : ℕ → ℝ) := by
    rw [onCoprime_eq_on_coe, ArithmeticFunction.on_mul_of_saturated _ hsat]
    exact mul_zeta_on_coprime_coe r _
  rw [hfun, Delta_finset_sum]
  calc |∑ e ∈ r.divisors,
          Δ_[(μ e : ℝ) • (⇑(dilate e ((Λ≤U * μ≤V).on {n | r.Coprime n})
            * (ζ : ArithmeticFunction ℝ)) : ℕ → ℝ)](y; q, a)|
      ≤ ∑ e ∈ r.divisors,
          |Δ_[(μ e : ℝ) • (⇑(dilate e ((Λ≤U * μ≤V).on {n | r.Coprime n})
            * (ζ : ArithmeticFunction ℝ)) : ℕ → ℝ)](y; q, a)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _e ∈ r.divisors, 2 * U * V * Real.log x := by
        apply Finset.sum_le_sum
        intro e he
        have he' : 0 < e := Nat.pos_of_mem_divisors he
        have hμ : |(μ e : ℝ)| ≤ 1 := by exact_mod_cast ArithmeticFunction.abs_moebius_le_one
        have hHbound : summatory (fun k => |((Λ≤U * μ≤V).on {n | r.Coprime n}) k|) y
            ≤ U * Real.log y * V := by
          have e1 : summatory (fun k => |((Λ≤U * μ≤V).on {n | r.Coprime n}) k|) y
              ≤ summatory (fun k => |(Λ≤U * μ≤V) k|) y := summatory_abs_on_le _ _
          have e2 : summatory (fun k => |(Λ≤U * μ≤V) k|) y
              ≤ summatory (fun k => |Λ≤U k|) y * summatory (fun k => |μ≤V k|) y :=
            summatory_abs_mul_le _ _ (by linarith)
          have e3 : summatory (fun k => |Λ≤U k|) y ≤ U * Real.log y :=
            summatory_abs_LambdaLEU_le h2y
          have e4 : summatory (fun k => |μ≤V k|) y ≤ V := summatory_abs_moebiusLEV_le
          have hlogy : 0 ≤ Real.log y := Real.log_nonneg (by linarith)
          calc summatory (fun k => |((Λ≤U * μ≤V).on {n | r.Coprime n}) k|) y
              ≤ summatory (fun k => |Λ≤U k|) y * summatory (fun k => |μ≤V k|) y := e1.trans e2
            _ ≤ (U * Real.log y) * V :=
                mul_le_mul e3 e4 (by positivity) (by positivity)
        have hΔ : |Δ_[⇑(dilate e ((Λ≤U * μ≤V).on {n | r.Coprime n})
            * (ζ : ArithmeticFunction ℝ))](y; q, a)| ≤ 2 * U * V * Real.log x := by
          rw [show (ζ : ArithmeticFunction ℝ) = log.ppow 0 from ppow_zero.symm]
          have hflog := Delta_dilate_flog_bound (v := 0) he'
            ((Λ≤U * μ≤V).on {n | r.Coprime n}) h2y a ha
          rw [pow_zero, mul_one] at hflog
          have hlogxy : Real.log y ≤ Real.log x := Real.log_le_log (by linarith) hy
          calc |Δ_[⇑(dilate e ((Λ≤U * μ≤V).on {n | r.Coprime n}) * log.ppow 0)](y; q, a)|
              ≤ 2 * summatory (fun k => |((Λ≤U * μ≤V).on {n | r.Coprime n}) k|) y := hflog
            _ ≤ 2 * (U * Real.log y * V) := by linarith [hHbound]
            _ ≤ 2 * (U * Real.log x * V) := by gcongr
            _ = 2 * U * V * Real.log x := by ring
        rw [Delta_smul, smul_eq_mul, abs_mul]
        have := mul_le_mul hμ hΔ (abs_nonneg _) (by norm_num : (0:ℝ) ≤ 1)
        rwa [one_mul] at this
    _ = (r.divisors.card : ℝ) * (2 * U * V * Real.log x) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ = 2 * (r.divisors.card : ℝ) * U * V * Real.log x := by ring

/-! ### Group G: the main Type I bound -/

-- Note: corrected statement carries a `τ(r) = r.divisors.card` factor (see
-- `notes/delta_lambda_sharp_bound.md`); the original blueprint `≪ UV log x` is unprovable.
@[blueprint (statement := /--
For $U, V \ge 1$, $x \ge 2$, $q \in \N$, $r \le x$ and $a \in (\Z/q\Z)^*$,
$$\max_{y \le x} \max_{a \in (\Z/q\Z)^*} |\Delta_{\Lambda^\sharp_r}(y;\, q,\, a)| \ll \tau(r)\, UV \log x$$
-/) (proof := /--
Restriction `(\cdot)_r` is a Dirichlet-convolution homomorphism, so the analytic
factor becomes $\log_r$ / $\zeta_r$. Möbius-expand it as $\sum_{e \mid r} \mu(e)$
of dilated literal $\log$ / $\zeta$, then apply \ref{Delta_flog_bound} to each
summand. The number of summands contributes the $\tau(r)$ factor.
-/) (uses := [Delta_flog_bound, Delta_convolution_eq])]
theorem Delta_LambdaSharp_bound [ProofData] {q r : ℕ} [NeZero q] {a : ZMod q} (ha : IsUnit a)
    (hr : r ≤ x) {y : ℝ} (h2y : 2 ≤ y) (hy : y ≤ x) :
    |Δ_[onCoprime r ⇑Λ♯](y; q, a)| ≤ C_DLS * (r.divisors.card : ℝ) * U * V * Real.log x := by
  sorry

@[blueprint (statement := /--
For each fixed $A \ge 0$, $x \ge 2$ and $1 \le Q \le \sqrt{x}/(\log x)^{A+3}$,
$$\sum_{q \le Q} \max_{\sqrt{x} \le y \le x} \max_{a \in (\Z/q\Z)^*} |\Delta_{\Lambda^\sharp}(y;\, q,\, a)| \ll_A \frac{x}{(\log x)^A}$$
-/) (uses := [Delta_LambdaSharp_bound])]
theorem BV_LambdaSharp [ProofData] {A : ℕ} (Q : ℝ) (h1Q : 1 ≤ Q) (hQ : Q ≤ √x / (Real.log x)^(A+3)) :
    ∑ q ∈ Nat.Icc 0 Q, maxya q (fun y a ↦ Δ_[Λ♯](y; q, a)) ≤ x / (Real.log x)^A := by
  sorry
