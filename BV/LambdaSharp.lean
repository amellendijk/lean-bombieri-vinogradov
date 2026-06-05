import Mathlib
import Architect
import BV.Delta

open ArithmeticFunction BV ProofData

def C_DLS : ℝ := sorry

-- Note: I think we may assume q ∣ r or (q, r) = 1 if necessary.
@[blueprint (statement := /--
For $U, V \ge 1$, $x \ge 2$, $q \in \N$, $r \le x$ and $a \in (\Z/q\Z)^*$,
$$\max_{y \le x} \max_{a \in (\Z/q\Z)^*} |\Delta_{\Lambda^\sharp_r}(y;\, q,\, a)| \ll UV \log x$$
-/) (proof := /--
Apply \ref{Delta_flog_bound} twice: once with $f = \mu_{\le V,\, r}$, $v = 1$,
and once with $f = \Lambda_{\le U} * \mu_{\le V,\, r}$, $v = 0$, $y = UV$.
-/) (uses := [Delta_flog_bound, Delta_convolution_eq])]
theorem Delta_LambdaSharp_bound [ProofData] {q r : ℕ} [NeZero q] {a : ZMod q} (ha : IsUnit a) (hr : r ≤ x) {y : ℝ} (hy : y ≤ x) :
    |Δ_[onCoprime r Λ♯](y; q, a)| ≤ C_DLS * U * V * Real.log x := by
  -- rw [LambdaSharp]
  -- have := Delta_flog_bound (f := (μ≤V).on {k | Nat.Coprime k r}) le_x a ha (v := 1)
  -- simp only [ArithmeticFunction.ppow_one, Real.norm_eq_abs, pow_one] at this
  sorry

@[blueprint (statement := /--
For each fixed $A \ge 0$, $x \ge 2$ and $1 \le Q \le \sqrt{x}/(\log x)^{A+3}$,
$$\sum_{q \le Q} \max_{\sqrt{x} \le y \le x} \max_{a \in (\Z/q\Z)^*} |\Delta_{\Lambda^\sharp}(y;\, q,\, a)| \ll_A \frac{x}{(\log x)^A}$$
-/) (uses := [Delta_LambdaSharp_bound])]
theorem BV_LambdaSharp [ProofData] {A : ℕ} (Q : ℝ) (h1Q : 1 ≤ Q) (hQ : Q ≤ √x / (Real.log x)^(A+3)) :
    ∑ q ∈ Nat.Icc 0 Q, maxya q (fun y a ↦ Δ_[Λ♯](y; q, a)) ≤ x / (Real.log x)^A := by
  sorry
