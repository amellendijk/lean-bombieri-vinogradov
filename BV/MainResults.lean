import Mathlib
import Architect

import BV.Defs
import BV.LambdaLE
import BV.LambdaSharp
import BV.LambdaFlat

open ArithmeticFunction

open BV

noncomputable section

/-! ## Bombieri-Vinogradov Theorem

This module contains the formalization of the Bombieri-Vinogradov theorem,
a fundamental result in analytic number theory.
-/


/-! Wrapping up -/

def C_BV_L (A : ℝ) : ℝ := sorry

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
    ∑ q ∈ Nat.Icc 0 Q, maxya q (fun y a ↦ Δ_[Λ](y; q, a)) ≤
      C_BV_L A * x / (Real.log x)^A := by
  sorry


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
    ∑ q ∈ Nat.Icc 1 Q, ⨆ y ∈ Set.Icc 1 x, ⨆ a : (ZMod q)ˣ, |ψ (q := q) y a - y / φ q|
      ≤ C_BV A * x / (Real.log x)^A
      := by
  sorry

end
