import Mathlib
import Architect
import BV.Delta
import BV.ForMathlib.Indicator

set_option autoImplicit false

open ArithmeticFunction BV ProofData

variable [ProofData]

@[blueprint "lem:l1-coefficients" (latexEnv := "lemma") (title := /-- $\ell^1$ norms of the coefficient functions -/) (statement := /--
For every real $y$,
$$\sum_{n \le y} \Lambda_{\le U}(n) \le U \log x \qquad\text{and}\qquad \sum_{n \le y} |\mu_{\le V}(n)| \le V ;$$
moreover $0 \le \Lambda_{\le U}(n) \le \log n$ for every $n \ge 1$.
-/) (proof := /--
The function $\Lambda_{\le U}$ is non-negative and supported on the at most $U$ integers $1 \le n \le U$,
and on its support $\Lambda_{\le U}(n) = \Lambda(n) \le \log n \le \log U \le \log x$ by
\Cref{lem:parameters}. Hence its sum over any range is at most $U \log x$. Likewise $\mu_{\le V}$ is
supported on the at most $V$ integers $1 \le n \le V$ and satisfies $|\mu_{\le V}| \le 1$.
-/)]
theorem LambdaLEU_le_log {n : ℕ} : Λ≤U n ≤ Real.log n := by
  by_cases hn : n ≤ U
  · simp [hn, vonMangoldt_le_log]
  · have hn : U < n := by grind
    simp [hn]
    positivity

omit [ProofData] in
@[gcongr]
theorem summatory_mono_fun (f g : ℕ → ℝ) (x : ℝ) (hfg : ∀ n : ℕ, n ≤ x → f n ≤ g n) :
    summatory f x ≤ summatory g x := by
  exact summatory_le_summatory fun n _ hnx ↦ hfg n hnx

omit [ProofData] in
@[gcongr]
theorem summatory_mono {f : ℕ → ℝ} {x y : ℝ} (hxy : x ≤ y) (hf : ∀ n : ℕ, n ≤ y → 0 ≤ f n) :
    summatory f x ≤ summatory f y := by
  simp only [summatory]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro n hn
    rw [Finset.mem_Ioc] at hn ⊢
    exact ⟨hn.1, hn.2.trans (Nat.floor_mono hxy)⟩
  · intro n hn _
    rw [Finset.mem_Ioc] at hn
    apply hf n
    have hy0 : 0 ≤ y := by
      by_contra hny
      have hfloor : ⌊y⌋₊ = 0 := Nat.floor_eq_zero.mpr (by linarith)
      omega
    exact_mod_cast calc n ≤ (⌊y⌋₊ : ℝ) := mod_cast hn.2
      _ ≤ y := Nat.floor_le hy0

@[blueprint "lem:l1-coefficients" (latexEnv := "lemma")]
theorem sum_LambdaLEU_le {y : ℝ} : summatory Λ≤U y ≤ U * Real.log x := by
  trans ‖summatory Λ≤U y‖
  · rw [Real.norm_eq_abs, abs_of_nonneg]
    · positivity
  apply summatory_le_support_mul_UB (S := U)
  · positivity
  · simp +contextual [abs_of_nonneg, vonMangoldt_nonneg]
    intro n hn
    by_cases hn0 : n = 0
    · simp [hn0]
      positivity
    grw [vonMangoldt_le_log]
    gcongr
    grw [hn]
    apply U_le_x
  · simp +contextual

@[blueprint "lem:small-pointwise" (latexEnv := "lemma") (proofUses := ["lem:Delta-trivial"]) (title := /-- Pointwise bound for $\Delta_{\Lambda_{\le U}}$ -/) (statement := /--
For every real $y$, every $q \ge 1$, every $a \in \Z/q\Z$ and every $r \in \N$,
$$|\Delta_{\Lambda_{\le U}}(y; q, a)| \le 2 U \log x \qquad\text{and}\qquad |\Delta_{(\Lambda_{\le U})_r}(y; q, a)| \le 2 U \log x .$$
-/) (proof := /--
Both $\Lambda_{\le U}$ and its restriction $(\Lambda_{\le U})_r$ are non-negative and bounded pointwise by
$\Lambda_{\le U}$, so by \Cref{lem:Delta-trivial} their discrepancies are bounded in absolute value by
$2 \sum_{n \le y} \Lambda_{\le U}(n) \le 2 U \log x$ (\Cref{lem:l1-coefficients}).
-/)]
theorem Delta_LambdaLEU_bound {y : ℝ} {q : ℕ} (hq : 0 < q) {a : ZMod q} :
    |Δ_[Λ≤U](y; q, a)| ≤ 2 * U * Real.log x := by
  rw [Delta]
  grw [abs_sub, abs_mul]
  have : (q.totient : ℝ)⁻¹ ≤ 1 := by
    have : 0 < q.totient := by positivity
    field_simp
    norm_cast
  grw [this, abs_one]
  rw [abs_of_nonneg, abs_of_nonneg]
  · have : summatory ((Nat.modEqs a).indicator ⇑Λ≤U) y ≤ U * Real.log x := by
      apply le_trans (summatory_mono_fun ..) sum_LambdaLEU_le
      intro n hn
      apply Set.indicator_le' (fun _ _ ↦ le_rfl)
      simp
    have : summatory (onCoprime q ⇑Λ≤U) y ≤ U * Real.log x := by
      apply le_trans (summatory_mono_fun ..) sum_LambdaLEU_le
      simp [onCoprime_le_of_nonneg]
    linarith
  · positivity
  · positivity

/-- Canonical `ℝ≥0∞` form of the small-factor estimate. -/
@[blueprint "prop:small-average" (latexEnv := "proposition") (title := /-- The small part on average -/) (statement := /--
For every $A \in \N$ and every real $0 \le Q \le \sqrt{x}/(\log x)^{A+3}$,
$$\sum_{q \le Q}\ \max_{\substack{\sqrt x \le y \le x \\ a \in (\Z/q\Z)^*}} |\Delta_{\Lambda_{\le U}}(y; q, a)| \le \frac{2x}{(\log x)^{A+2}}.$$
-/) (proof := /--
By \Cref{lem:small-pointwise} and \Cref{lem:max}(2), each of the $\lfloor Q \rfloor \le Q$ summands is
at most $2U \log x$. Using $U \le \sqrt x$ (\Cref{lem:parameters}) and the hypothesis on $Q$,
$$Q \cdot 2 U \log x \le \frac{\sqrt x}{(\log x)^{A+3}} \cdot 2 \sqrt x \log x = \frac{2x}{(\log x)^{A+2}}. \qedhere$$
-/)]
theorem BV_LambdaLE_enorm {A : ℕ} (Q : ℝ) (hQ_nonneg : 0 ≤ Q)
    (hQ : Q ≤ √x / (Real.log x) ^ (A + 3)) :
    ∑ q ∈ Finset.Ioc 0 ⌊Q⌋₊,
      maxya q (fun y a ↦ ‖Δ_[Λ≤U](y; q, a)‖ₑ) ≤
        ENNReal.ofReal (2 * x / (Real.log x) ^ (A + 2)) := by
  let B : ℝ := 2 * U * Real.log x
  have hB : 0 ≤ B := by positivity
  have hterm : ∀ q ∈ Finset.Ioc 0 ⌊Q⌋₊,
      maxya q (fun y a ↦ ‖Δ_[Λ≤U](y; q, a)‖ₑ) ≤ ENNReal.ofReal B := by
    intro q hq
    rw [Finset.mem_Ioc] at hq
    apply maxya_Delta_enorm_le_of_abs_le
    intro y _ _ a _
    dsimp [B]
    exact Delta_LambdaLEU_bound (by omega)
  have hreal : ∑ _q ∈ Finset.Ioc 0 ⌊Q⌋₊, B ≤
      2 * x / (Real.log x) ^ (A + 2) := by
    dsimp [B]
    simp only [Finset.sum_const, nsmul_eq_mul]
    simp [card_natIcc, hQ_nonneg]
    grw [Nat.floor_le hQ_nonneg, hQ, U_le_sqrt_x]
    apply le_of_eq
    have : 0 < Real.log x := Real.log_pos (by linarith only [le_x])
    field_simp
    rw [Real.sq_sqrt x_nonneg]
    ring
  calc
    ∑ q ∈ Finset.Ioc 0 ⌊Q⌋₊, maxya q (fun y a ↦ ‖Δ_[Λ≤U](y; q, a)‖ₑ)
        ≤ ∑ _q ∈ Finset.Ioc 0 ⌊Q⌋₊, ENNReal.ofReal B :=
          Finset.sum_le_sum hterm
    _ = ENNReal.ofReal (∑ _q ∈ Finset.Ioc 0 ⌊Q⌋₊, B) := by
          rw [ENNReal.ofReal_sum_of_nonneg (fun _ _ ↦ hB)]
    _ ≤ ENNReal.ofReal (2 * x / (Real.log x) ^ (A + 2)) :=
      ENNReal.ofReal_le_ofReal hreal
