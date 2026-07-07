import Mathlib
import Architect
import BV.Delta
import BV.Dilate

open ArithmeticFunction BV ProofData
open scoped Moebius zeta

def C_DLS : ℝ := 6

/-- Constant in the average-order bound `∑_{q ≤ Q} τ(q) ≤ C_tau · Q log Q` (`sum_divisors_card_le`). -/
def C_tau : ℝ := 3

/-- Constant in the Type I sum bound `BV_LambdaSharp`. -/
def C_BVLS : ℝ := C_DLS * C_tau

/-! ### Group D: `Δ` is linear in its function argument -/

theorem Delta_sub {R : Type*} [Field R] (f g : ℕ → R) (x : ℝ) (q : ℕ) (a : ZMod q) :
    Δ_[f - g](x; q, a) = Δ_[f](x; q, a) - Δ_[g](x; q, a) := by
  have hind : (Nat.modEqs (a : ZMod q)).indicator (f - g)
      = fun n => (Nat.modEqs (a : ZMod q)).indicator f n
          - (Nat.modEqs (a : ZMod q)).indicator g n := by
    funext n; by_cases h : n ∈ Nat.modEqs (a : ZMod q) <;> simp [h]
  have hcop : onCoprime q (f - g)
      = fun n => onCoprime q f n - onCoprime q g n := by
    funext n; simp only [onCoprime, Pi.sub_apply]; split_ifs <;> simp
  simp only [Delta, hind, hcop, summatory_sub_distrib]
  ring

theorem Delta_smul {R : Type*} [Field R] (c : R) (f : ℕ → R) (x : ℝ) (q : ℕ) (a : ZMod q) :
    Δ_[c • f](x; q, a) = c • Δ_[f](x; q, a) := by
  have hind : (Nat.modEqs (a : ZMod q)).indicator (c • f)
      = fun n => c • (Nat.modEqs (a : ZMod q)).indicator f n := by
    funext n; by_cases h : n ∈ Nat.modEqs (a : ZMod q) <;> simp [h]
  have hcop : onCoprime q (c • f)
      = fun n => c • onCoprime q f n := by
    funext n; simp only [onCoprime, Pi.smul_apply]; split_ifs <;> simp
  simp only [Delta, hind, hcop, smul_eq_mul, summatory, ← Finset.mul_sum]
  ring

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
  classical
  induction s using Finset.induction with
  | empty =>
      simp [Delta, summatory, onCoprime]
  | insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi, Delta_add, ih]

/-! ### Group C: Möbius expansion of the restricted analytic factor

Stated at the coerced `ℕ → ℝ` level (where `ℝ`-scalar multiplication exists, unlike
on `ArithmeticFunction ℝ`). Convolving the coefficient function `H` with the restricted
`ζ`/`log` produces a `∑_{e ∣ r}` of dilations of `H * ζ` / `H * log`, with the real
coefficients `μ(e)` and `log e` sitting outside the arithmetic functions.

(`mul_zeta_on_coprime_coe` / `zeta_on_coprime_apply` live further down, after the shared
`dilate_mul_left` and `moebius_coprime_indicator` helpers.) -/

/-- Move a dilation across a convolution onto the whole product: `dilate e H * g = H * dilate e g`.
-/
theorem dilate_mul_left {e : ℕ} (he : 0 < e) (H g : ArithmeticFunction ℝ) :
    dilate e H * g = H * dilate e g := by
  rw [mul_comm (dilate e H) g, mul_dilate he, mul_dilate he, mul_comm g H]

/-- Möbius inversion of the coprimality indicator: `1_{(r,b)=1} = ∑_{e ∣ r} μ(e)·1_{e ∣ b}`.
Needs `r ≠ 0` (for `r = 0` the empty divisor set `Nat.divisors 0 = ∅` breaks the identity). -/
theorem moebius_coprime_indicator {r : ℕ} (hr : r ≠ 0) (b : ℕ) :
    ∑ e ∈ r.divisors, (if e ∣ b then (μ e : ℝ) else 0) = if r.Coprime b then 1 else 0 := by
  rw [← Finset.sum_filter]
  have hset : r.divisors.filter (· ∣ b) = (Nat.gcd r b).divisors := by
    ext e
    simp only [Finset.mem_filter, Nat.mem_divisors, Nat.dvd_gcd_iff]
    have hg : Nat.gcd r b ≠ 0 := by simp [Nat.gcd_eq_zero_iff, hr]
    tauto
  rw [hset]
  have hone : ∑ i ∈ (Nat.gcd r b).divisors, (μ i : ℝ)
      = (1 : ArithmeticFunction ℝ) (Nat.gcd r b) := by
    rw [← ArithmeticFunction.coe_moebius_mul_coe_zeta, ArithmeticFunction.coe_mul_zeta_apply]
    exact Finset.sum_congr rfl (fun i _ => (ArithmeticFunction.intCoe_apply).symm)
  rw [hone, ArithmeticFunction.one_apply]

/-- Pointwise Möbius expansion (B1): the restriction of `log` to integers coprime to `r`
equals a divisor-sum of dilated `ζ`/`log`. -/
theorem log_on_coprime_apply (r b : ℕ) :
    ((log : ArithmeticFunction ℝ).on {k | r.Coprime k}) b
      = ∑ e ∈ r.divisors,
          ((μ e : ℝ) * Real.log e * dilate e (ζ : ArithmeticFunction ℝ) b
            + (μ e : ℝ) * dilate e (log : ArithmeticFunction ℝ) b) := by
  -- Collapse each summand to `(if e ∣ b then μ e else 0) * log b`.
  have hterm : ∀ e ∈ r.divisors,
      (μ e : ℝ) * Real.log e * dilate e (ζ : ArithmeticFunction ℝ) b
        + (μ e : ℝ) * dilate e (log : ArithmeticFunction ℝ) b
        = (if e ∣ b then (μ e : ℝ) else 0) * Real.log b := by
    intro e he
    have he0 : e ≠ 0 := (Nat.pos_of_mem_divisors he).ne'
    simp only [dilate_apply]
    by_cases hb : e ∣ b
    · simp only [hb, if_true]
      by_cases hb0 : b = 0
      · subst hb0; simp
      · have hbe0 : b / e ≠ 0 := by
          rw [Nat.div_ne_zero_iff]
          exact ⟨he0, Nat.le_of_dvd (Nat.pos_of_ne_zero hb0) hb⟩
        rw [ArithmeticFunction.natCoe_apply, ArithmeticFunction.zeta_apply_ne hbe0,
            Nat.cast_one, mul_one, ArithmeticFunction.log_apply, ← mul_add,
            ← Real.log_mul (by exact_mod_cast he0) (by exact_mod_cast hbe0),
            ← Nat.cast_mul, Nat.mul_div_cancel' hb]
    · simp [hb]
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_mul]
  -- Evaluate the restriction on the left via the coprimality indicator.
  rcases Nat.eq_zero_or_pos r with hr | hr
  · -- `r = 0`: the divisor sum is empty and `log b ≠ 0` only at `b = 1`, where `log 1 = 0`.
    subst hr
    by_cases hcop : (0 : ℕ).Coprime b
    · rw [ArithmeticFunction.on_apply_of_mem {k | (0 : ℕ).Coprime k} log b hcop]
      have : b = 1 := by simpa [Nat.Coprime] using hcop
      subst this; simp
    · rw [ArithmeticFunction.on_apply_of_not_mem {k | (0 : ℕ).Coprime k} log b hcop]
      simp
  · rw [moebius_coprime_indicator hr.ne' b]
    by_cases hcop : r.Coprime b
    · rw [ArithmeticFunction.on_apply_of_mem {k | r.Coprime k} log b hcop,
          ArithmeticFunction.log_apply, if_pos hcop, one_mul]
    · rw [ArithmeticFunction.on_apply_of_not_mem {k | r.Coprime k} log b hcop,
          if_neg hcop, zero_mul]

theorem mul_log_on_coprime_coe (r : ℕ) (H : ArithmeticFunction ℝ) :
    (⇑(H * (log : ArithmeticFunction ℝ).on {k | r.Coprime k}) : ℕ → ℝ)
      = ∑ e ∈ r.divisors,
          (((μ e : ℝ) * Real.log e) • (⇑(dilate e H * (ζ : ArithmeticFunction ℝ)) : ℕ → ℝ)
            + (μ e : ℝ) • (⇑(dilate e H * (log : ArithmeticFunction ℝ)) : ℕ → ℝ)) := by
  funext n
  simp only [Finset.sum_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [ArithmeticFunction.mul_apply]
  -- Expand each summand on the right into a sum over `n.divisorsAntidiagonal`.
  have key : ∀ e ∈ r.divisors,
      ((μ e : ℝ) * Real.log e) * (⇑(dilate e H * (ζ : ArithmeticFunction ℝ)) : ℕ → ℝ) n
        + (μ e : ℝ) * (⇑(dilate e H * (log : ArithmeticFunction ℝ)) : ℕ → ℝ) n
        = ∑ x ∈ n.divisorsAntidiagonal,
            H x.1 * ((μ e : ℝ) * Real.log e * dilate e (ζ : ArithmeticFunction ℝ) x.2
              + (μ e : ℝ) * dilate e (log : ArithmeticFunction ℝ) x.2) := by
    intro e he
    have he0 : 0 < e := Nat.pos_of_mem_divisors he
    rw [dilate_mul_left he0 H (ζ : ArithmeticFunction ℝ),
        dilate_mul_left he0 H (log : ArithmeticFunction ℝ),
        ArithmeticFunction.mul_apply, ArithmeticFunction.mul_apply,
        Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun x _ => by ring)
  rw [Finset.sum_congr rfl key, Finset.sum_comm]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [← Finset.mul_sum, ← log_on_coprime_apply r x.2]

/-- Pointwise Möbius expansion (B0): the restriction of `ζ` to integers coprime to `r`
equals a divisor-sum of dilated `ζ`. Requires `r ≠ 0`: for `r = 0` the coprimality set is
`{1}`, so the restriction is the identity arithmetic function `1`, while the divisor sum is
empty (`Nat.divisors 0 = ∅`). -/
theorem zeta_on_coprime_apply {r : ℕ} (hr : r ≠ 0) (b : ℕ) :
    ((ζ : ArithmeticFunction ℝ).on {k | r.Coprime k}) b
      = ∑ e ∈ r.divisors, (μ e : ℝ) * dilate e (ζ : ArithmeticFunction ℝ) b := by
  by_cases hb0 : b = 0
  · subst hb0; simp
  · -- Collapse each summand to `if e ∣ b then μ e else 0`.
    have hterm : ∀ e ∈ r.divisors,
        (μ e : ℝ) * dilate e (ζ : ArithmeticFunction ℝ) b = if e ∣ b then (μ e : ℝ) else 0 := by
      intro e he
      have he0 : e ≠ 0 := (Nat.pos_of_mem_divisors he).ne'
      simp only [dilate_apply]
      by_cases hb : e ∣ b
      · have hbe0 : b / e ≠ 0 := by
          rw [Nat.div_ne_zero_iff]
          exact ⟨he0, Nat.le_of_dvd (Nat.pos_of_ne_zero hb0) hb⟩
        simp [hb, ArithmeticFunction.natCoe_apply, ArithmeticFunction.zeta_apply_ne hbe0]
      · simp [hb]
    rw [Finset.sum_congr rfl hterm, moebius_coprime_indicator hr]
    by_cases hcop : r.Coprime b
    · rw [ArithmeticFunction.on_apply_of_mem {k | r.Coprime k} _ b hcop, if_pos hcop,
          ArithmeticFunction.natCoe_apply, ArithmeticFunction.zeta_apply_ne hb0, Nat.cast_one]
    · rw [ArithmeticFunction.on_apply_of_not_mem {k | r.Coprime k} _ b hcop, if_neg hcop]

theorem mul_zeta_on_coprime_coe {r : ℕ} (hr : r ≠ 0) (H : ArithmeticFunction ℝ) :
    (⇑(H * (ζ : ArithmeticFunction ℝ).on {k | r.Coprime k}) : ℕ → ℝ)
      = ∑ e ∈ r.divisors,
          (μ e : ℝ) • (⇑(dilate e H * (ζ : ArithmeticFunction ℝ)) : ℕ → ℝ) := by
  funext n
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [ArithmeticFunction.mul_apply]
  have key : ∀ e ∈ r.divisors,
      (μ e : ℝ) * (⇑(dilate e H * (ζ : ArithmeticFunction ℝ)) : ℕ → ℝ) n
        = ∑ x ∈ n.divisorsAntidiagonal,
            H x.1 * ((μ e : ℝ) * dilate e (ζ : ArithmeticFunction ℝ) x.2) := by
    intro e he
    have he0 : 0 < e := Nat.pos_of_mem_divisors he
    rw [dilate_mul_left he0 H (ζ : ArithmeticFunction ℝ), ArithmeticFunction.mul_apply,
        Finset.mul_sum]
    exact Finset.sum_congr rfl (fun x _ => by ring)
  rw [Finset.sum_congr rfl key, Finset.sum_comm]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [← Finset.mul_sum, ← zeta_on_coprime_apply hr x.2]

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
              ≤ summatory (fun k => |(μ≤V) k|) y :=
            summatory_le_summatory (fun n _ _ => abs_on_le _ _ n)
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
  rcases eq_or_ne r 0 with rfl | hr0
  · -- `r = 0`: the coprimality set is `{1}`, where `Λ_{≤U} * μ_{≤V} * ζ` vanishes
    -- (`Λ 1 = 0`), so the discrepancy is `0` and the divisor count is `0`.
    have hz : onCoprime 0 (⇑(Λ≤U * μ≤V * (ζ : ArithmeticFunction ℝ))) = fun _ => 0 := by
      funext n
      rw [onCoprime_apply]
      split_ifs with h
      · have hn1 : n = 1 := by simpa [Nat.Coprime] using h
        have hΛ1 : (Λ≤U : ArithmeticFunction ℝ) 1 = 0 := by
          rw [LambdaLEU_apply_of_le (by exact_mod_cast ProofData.one_le_U)]
          exact ArithmeticFunction.vonMangoldt_apply_one
        subst hn1
        simp [ArithmeticFunction.mul_apply, Nat.divisorsAntidiagonal_one, hΛ1]
      · rfl
    rw [hz]
    simp [Delta, summatory, onCoprime_apply]
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
    exact mul_zeta_on_coprime_coe hr0 _
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
              ≤ summatory (fun k => |(Λ≤U * μ≤V) k|) y :=
            summatory_le_summatory (fun n _ _ => abs_on_le _ _ n)
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
  -- Split `Λ♯ = μ≤V * log - Λ≤U * μ≤V * ζ` inside the (coprime-restricted) `Δ`.
  have hsplit : onCoprime r ⇑Λ♯
      = onCoprime r ⇑(μ≤V * log) - onCoprime r ⇑(Λ≤U * μ≤V * (ζ : ArithmeticFunction ℝ)) := by
    funext n
    simp only [LambdaSharp, onCoprime_apply, Pi.sub_apply]
    split_ifs
    · rfl
    · rw [sub_zero]
  rw [hsplit, Delta_sub]
  have hT1 := Delta_term1_bound ha hr h2y hy
  have hT2 := Delta_term2_bound ha hr h2y hy
  have hτ : (0:ℝ) ≤ (r.divisors.card : ℝ) := by positivity
  have hU : (1:ℝ) ≤ U := ProofData.one_le_U
  have hV : (0:ℝ) ≤ V := ProofData.V_nonneg
  have hlogx : (0:ℝ) ≤ Real.log x := Real.log_nonneg (by linarith [ProofData.le_x])
  have habs : |Δ_[onCoprime r ⇑(μ≤V * log)](y; q, a)
        - Δ_[onCoprime r ⇑(Λ≤U * μ≤V * (ζ : ArithmeticFunction ℝ))](y; q, a)|
      ≤ |Δ_[onCoprime r ⇑(μ≤V * log)](y; q, a)|
        + |Δ_[onCoprime r ⇑(Λ≤U * μ≤V * (ζ : ArithmeticFunction ℝ))](y; q, a)| := by
    rw [sub_eq_add_neg]; exact (abs_add_le _ _).trans_eq (by rw [abs_neg])
  refine habs.trans ?_
  refine (add_le_add hT1 hT2).trans ?_
  simp only [C_DLS]
  nlinarith [mul_nonneg (mul_nonneg (mul_nonneg hτ hV) hlogx) (by linarith : (0:ℝ) ≤ U - 1)]

@[blueprint (statement := /--
The divisor function has average order $\log$:
$$\sum_{q \le Q} \tau(q) \ll Q \log Q,$$
uniformly for $Q \ge 2$ (where $\tau(q) = $ `q.divisors.card`).
-/)]
theorem sum_divisors_card_le {Q : ℝ} (hQ : 2 ≤ Q) :
    ∑ q ∈ Nat.Icc 0 Q, (q.divisors.card : ℝ) ≤ C_tau * Q * Real.log Q := by
  set N := ⌊Q⌋₊ with hN
  have hQ0 : (0:ℝ) ≤ Q := by linarith
  have hIcc : Nat.Icc 0 Q = Finset.Icc 0 N := by
    rw [Nat.Icc, if_pos ⟨by linarith, by linarith⟩]; simp [hN]
  rw [hIcc]
  -- Drop the `q = 0` term (its divisor count is `0`).
  have hsub : ∑ q ∈ Finset.Icc 0 N, (q.divisors.card : ℝ)
      = ∑ q ∈ Finset.Ioc 0 N, (q.divisors.card : ℝ) := by
    refine (Finset.sum_subset Finset.Ioc_subset_Icc_self ?_).symm
    intro x hx hxni
    have hx0 : x = 0 := by
      simp only [Finset.mem_Icc] at hx
      simp only [Finset.mem_Ioc] at hxni
      omega
    simp [hx0]
  rw [hsub]
  -- `∑_{q ≤ N} τ(q) = ∑_{q ≤ N} ⌊N/q⌋` (over `ℕ`).
  have hkey : (∑ q ∈ Finset.Ioc 0 N, q.divisors.card : ℕ) = ∑ q ∈ Finset.Ioc 0 N, (N / q) := by
    simp_rw [← sigma_zero_apply]
    exact sum_Ioc_sigma0_eq_sum_div N
  have hcast : ∑ q ∈ Finset.Ioc 0 N, (q.divisors.card : ℝ)
      = ∑ q ∈ Finset.Ioc 0 N, ((N / q : ℕ) : ℝ) := by
    rw [← Nat.cast_sum, ← Nat.cast_sum, hkey]
  rw [hcast]
  -- Bound `∑ ⌊N/q⌋ ≤ N · H_N`.
  have hharm : (harmonic N : ℝ) = ∑ q ∈ Finset.Ioc 0 N, ((q:ℝ))⁻¹ := by
    rw [show Finset.Ioc 0 N = Finset.Icc 1 N from rfl, harmonic_eq_sum_Icc]
    push_cast
    rfl
  have hbound : ∑ q ∈ Finset.Ioc 0 N, ((N / q : ℕ) : ℝ) ≤ (N:ℝ) * (harmonic N : ℝ) := by
    rw [hharm, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    calc ((N / i : ℕ):ℝ) ≤ (N:ℝ)/(i:ℝ) := Nat.cast_div_le
      _ = (N:ℝ) * ((i:ℝ))⁻¹ := div_eq_mul_inv _ _
  refine hbound.trans ?_
  -- `N · H_N ≤ N (1 + log Q) ≤ Q (1 + log Q) ≤ 3 Q log Q`.
  have hHN : (harmonic N : ℝ) ≤ 1 + Real.log Q := by
    have := harmonic_floor_le_one_add_log Q (by linarith)
    rwa [← hN] at this
  have hNQ : (N:ℝ) ≤ Q := Nat.floor_le hQ0
  have hNnn : (0:ℝ) ≤ (N:ℝ) := by positivity
  have hloghalf : (1:ℝ)/2 ≤ Real.log Q := by
    have h2 : Real.log 2 ≤ Real.log Q := Real.log_le_log (by norm_num) (by linarith)
    have := Real.log_two_gt_d9
    linarith
  calc (N:ℝ) * (harmonic N:ℝ)
      ≤ (N:ℝ) * (1 + Real.log Q) := mul_le_mul_of_nonneg_left hHN hNnn
    _ ≤ Q * (1 + Real.log Q) := mul_le_mul_of_nonneg_right hNQ (by linarith)
    _ ≤ C_tau * Q * Real.log Q := by
        rw [C_tau]
        nlinarith [mul_nonneg hQ0 (by linarith : (0:ℝ) ≤ Real.log Q - 1/2)]

@[blueprint (statement := /--
For each fixed $A \ge 0$, $x \ge 2$ and $1 \le Q \le \sqrt{x}/(\log x)^{A+3}$,
$$\sum_{q \le Q} \max_{\sqrt{x} \le y \le x} \max_{a \in (\Z/q\Z)^*} |\Delta_{\Lambda^\sharp}(y;\, q,\, a)| \ll_A \frac{x}{(\log x)^A}$$
-/) (uses := [Delta_LambdaSharp_bound, sum_divisors_card_le])]
theorem BV_LambdaSharp [ProofData] {A : ℕ} (Q : ℝ) (h1Q : 1 ≤ Q) (hQ : Q ≤ √x / (Real.log x)^(A+3)) :
    ∑ q ∈ Nat.Icc 0 Q, maxya q (fun y a ↦ |Δ_[Λ♯](y; q, a)|) ≤ C_BVLS * (x / (Real.log x)^A) := by
  have hL1 : 1 ≤ Real.log x := one_le_log_x
  have hLpos : 0 < Real.log x := log_x_pos
  have hUnonneg : (0:ℝ) ≤ U := ProofData.U_nonneg
  have hVnonneg : (0:ℝ) ≤ V := ProofData.V_nonneg
  have hUVle : U * V ≤ √x := ProofData.UV_le
  have hsqrt_nonneg : (0:ℝ) ≤ √x := Real.sqrt_nonneg x
  have hsqrt_le_x : √x ≤ x := by
    rw [Real.sqrt_le_iff]
    exact ⟨ProofData.x_nonneg, le_self_pow₀ (by linarith [ProofData.le_x]) (by norm_num)⟩
  -- `(log x)^(A+3) ≥ 1`, hence `Q ≤ √x ≤ x`.
  have hpowge : (1:ℝ) ≤ (Real.log x)^(A+3) := one_le_pow₀ hL1
  have hQ_le_sqrt : Q ≤ √x := by
    refine hQ.trans ?_
    rw [div_le_iff₀ (by positivity)]
    nlinarith [hsqrt_nonneg, hpowge]
  have hQ_le_x : Q ≤ x := hQ_le_sqrt.trans hsqrt_le_x
  -- `2 ≤ √x` (so every `y ∈ [√x, x]` satisfies `2 ≤ y`).
  have hsqx2 : 2 ≤ √x := by
    have heU : Real.exp 1 ≤ U := by
      refine le_trans (Real.exp_le_exp.mpr ?_) le_U
      calc (1:ℝ) = Real.sqrt 1 := by simp
        _ ≤ Real.sqrt (Real.log x) := Real.sqrt_le_sqrt hL1
    calc (2:ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
      _ ≤ U := heU
      _ ≤ √x := ProofData.U_le_sqrt_x
  -- Per-term bound: `maxya q (Δ_[Λ♯]) ≤ C_DLS · τ(q) · U · V · log x`.
  have hterm : ∀ q ∈ Nat.Icc (0:ℝ) Q, maxya q (fun y a ↦ |Δ_[Λ♯](y; q, a)|)
      ≤ C_DLS * (q.divisors.card : ℝ) * U * V * Real.log x := by
    intro q hq
    have hqQ : (q:ℝ) ≤ Q := ((Nat.mem_Icc _ _).mp hq).2
    have hqx : (q:ℝ) ≤ x := hqQ.trans hQ_le_x
    rcases Nat.eq_zero_or_pos q with hq0 | hqpos
    · -- `q = 0`: `τ(0) = 0` and `Δ_[Λ♯](y; 0, a) = 0` for unit `a`.
      subst hq0
      apply maxya_le_unit
      · intro y _ _ a ha
        have hz : onCoprime 0 (⇑(Λ♯ : ArithmeticFunction ℝ)) = fun _ => (0:ℝ) := by
          funext n
          rw [onCoprime_apply]
          split_ifs with h
          · rw [Nat.coprime_zero_left] at h
            subst h
            have hsub : (Λ♯ : ArithmeticFunction ℝ) 1
                = (μ≤V * log) 1 - (Λ≤U * μ≤V * (ζ : ArithmeticFunction ℝ)) 1 := rfl
            rw [hsub, ArithmeticFunction.mul_apply_one, ArithmeticFunction.mul_apply_one,
              ArithmeticFunction.mul_apply_one]
            simp [ArithmeticFunction.log_apply, LambdaLEU_apply_of_le, ProofData.one_le_U]
          · rfl
        rw [(Delta_onCoprime_self _ y ha).symm, hz]
        simp [Delta, summatory, onCoprime, abs_zero]
      · simp
    · -- `q ≥ 1`: use `Delta_LambdaSharp_bound` with `r = q`.
      haveI : NeZero q := ⟨hqpos.ne'⟩
      apply maxya_le_unit
      · intro y hy1 hy2 a ha
        have h2y : 2 ≤ y := le_trans hsqx2 hy1
        have hbound := Delta_LambdaSharp_bound (q := q) (r := q) ha hqx h2y hy2
        rw [(Delta_onCoprime_self _ y ha).symm]
        exact hbound
      · have : (0:ℝ) ≤ (q.divisors.card : ℝ) := by positivity
        have : (0:ℝ) ≤ C_DLS := by rw [C_DLS]; norm_num
        positivity
  -- Sum the per-term bounds and factor out the constants.
  have hsum1 := Finset.sum_le_sum hterm
  have hfactor : ∑ q ∈ Nat.Icc (0:ℝ) Q, C_DLS * (q.divisors.card : ℝ) * U * V * Real.log x
      = C_DLS * U * V * Real.log x * ∑ q ∈ Nat.Icc (0:ℝ) Q, (q.divisors.card : ℝ) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun q _ => by ring)
  -- Divisor average: `∑_{q ≤ Q} τ(q) ≤ C_tau · Q · log x`.
  have hS : ∑ q ∈ Nat.Icc (0:ℝ) Q, (q.divisors.card : ℝ) ≤ C_tau * Q * Real.log x := by
    by_cases hQ2 : 2 ≤ Q
    · refine (sum_divisors_card_le hQ2).trans ?_
      have hlogQ : Real.log Q ≤ Real.log x := Real.log_le_log (by linarith) hQ_le_x
      have hCQ : (0:ℝ) ≤ C_tau * Q := by rw [C_tau]; positivity
      nlinarith [hCQ, hlogQ]
    · have hQ2' : Q < 2 := lt_of_not_ge hQ2
      have h0Q : (0:ℝ) ≤ Q := by linarith
      have hfloor : ⌊Q⌋₊ = 1 := by
        rw [Nat.floor_eq_iff h0Q]
        exact ⟨by exact_mod_cast h1Q, by push_cast; linarith⟩
      have hsum_eq : ∑ q ∈ Nat.Icc (0:ℝ) Q, (q.divisors.card : ℝ) = 1 := by
        rw [show Nat.Icc (0:ℝ) Q = Finset.Icc 0 1 by
          rw [Nat.Icc, if_pos ⟨h0Q, h0Q⟩]; simp [hfloor]]
        simp [Finset.sum_Icc_succ_top]
      rw [hsum_eq, C_tau]
      nlinarith [hL1, h1Q]
  -- Final assembly.
  refine (hsum1.trans (le_of_eq hfactor)).trans ?_
  have hcoef : (0:ℝ) ≤ C_DLS * U * V * Real.log x := by
    have : (0:ℝ) ≤ C_DLS := by rw [C_DLS]; norm_num
    positivity
  refine (mul_le_mul_of_nonneg_left hS hcoef).trans ?_
  -- `C_DLS · U · V · L · (C_tau · Q · L) ≤ C_BVLS · x / L^A`.
  have hQ3 : Q * (Real.log x)^(A+3) ≤ √x := (le_div_iff₀ (by positivity)).mp hQ
  have hQpow : (0:ℝ) ≤ Q := by linarith
  -- `Q · L^(A+2) ≤ Q · L^(A+3) ≤ √x`.
  have hQ2pow : Q * (Real.log x)^(A+2) ≤ √x :=
    le_trans (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hL1 (by omega)) hQpow) hQ3
  -- `(U·V) · (Q·L^(A+2)) ≤ √x · √x = x`.
  have hkey : U * V * (Q * (Real.log x)^(A+2)) ≤ x := by
    calc U * V * (Q * (Real.log x)^(A+2))
        ≤ √x * √x := mul_le_mul hUVle hQ2pow (by positivity) hsqrt_nonneg
      _ = x := Real.mul_self_sqrt ProofData.x_nonneg
  rw [C_BVLS, ← mul_div_assoc, le_div_iff₀ (by positivity : (0:ℝ) < (Real.log x)^A)]
  have hLA2 : (Real.log x)^(A+2) = (Real.log x)^A * (Real.log x)^2 := by rw [pow_add]
  calc C_DLS * U * V * Real.log x * (C_tau * Q * Real.log x) * (Real.log x)^A
      = C_DLS * C_tau * (U * V * (Q * (Real.log x)^(A+2))) := by rw [hLA2]; ring
    _ ≤ C_DLS * C_tau * x := by
        apply mul_le_mul_of_nonneg_left hkey
        rw [C_DLS, C_tau]; norm_num
