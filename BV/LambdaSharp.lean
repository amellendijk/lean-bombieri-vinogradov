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
  sorry

/-! ### Group E (specialised `ℓ¹` bounds) -/

/-- `‖μ_{≤V}‖₁ ≤ V`: `|μ| ≤ 1` on the `≤ V` supported values. -/
theorem summatory_abs_moebiusLEV_le [ProofData] {x : ℝ} :
    summatory (fun k => |(μ≤V : ArithmeticFunction ℝ) k|) x ≤ V := by
  sorry

/-- `‖Λ_{≤U}‖₁ ≤ U·log x`: `Λ(k) ≤ log k ≤ log x` on the `≤ U` supported values
(`vonMangoldt_le_log`); the extra `log` is absorbed by the target `UV log x`. -/
theorem summatory_abs_LambdaLEU_le [ProofData] {x : ℝ} (hx : 2 ≤ x) :
    summatory (fun k => |(Λ≤U : ArithmeticFunction ℝ) k|) x ≤ U * Real.log x := by
  sorry

/-! ### Group F: the two term bounds -/

/-- Term 1 of `Λ♯`: `μ_{≤V} * log`, restricted to coprimes of `r`. -/
theorem Delta_term1_bound [ProofData] {q r : ℕ} [NeZero q] {a : ZMod q}
    (ha : IsUnit a) (hr : r ≤ x) {y : ℝ} (h2y : 2 ≤ y) (hy : y ≤ x) :
    |Δ_[onCoprime r ⇑(μ≤V * log)](y; q, a)| ≤ 4 * (r.divisors.card : ℝ) * V * Real.log x := by
  sorry

/-- Term 2 of `Λ♯`: `Λ_{≤U} * μ_{≤V} * ζ`, restricted to coprimes of `r`. -/
theorem Delta_term2_bound [ProofData] {q r : ℕ} [NeZero q] {a : ZMod q}
    (ha : IsUnit a) (hr : r ≤ x) {y : ℝ} (h2y : 2 ≤ y) (hy : y ≤ x) :
    |Δ_[onCoprime r ⇑(Λ≤U * μ≤V * (ζ : ArithmeticFunction ℝ))](y; q, a)|
      ≤ 2 * (r.divisors.card : ℝ) * U * V * Real.log x := by
  sorry

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
