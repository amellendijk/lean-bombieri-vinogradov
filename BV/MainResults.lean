import Mathlib
import Architect

import BV.Defs
import BV.LambdaLE
import BV.LambdaSharp
import BV.LambdaFlat

open ArithmeticFunction

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
    (∑ q ∈ Nat.Icc 1 Q,
        have : NeZero q := sorry
      ⨆ y ∈ Set.Icc 1 x,
        Finset.univ.sup' Finset.univ_nonempty fun (a : ZMod q) ↦ (|ψ y a - x / φ q|))
      ≤ C_BV A * x / (Real.log x)^A := by
  sorry

end



/- These statements are helpful for deducing the version of BV involving $\pi$ instead of $\psi$, but we leave this out of the blueprint for now.-/

-- @[blueprint (statement :=
-- /--
-- $$\Delta_{1_P}(x; q, a) = \pi(x; q,a) - \frac{1}{\varphi(q)} \sum_{p \le x, p \not\mid q} 1 $$
-- -/
-- )]
-- theorem Delta_primeIndicator_eq : (sorry : Prop) := by
--   sorry


-- @[blueprint (statement :=
-- /--
-- $$ \sum_{p \le x, p \not \mid q} 1 = li(x) + O(xe^{-c\sqrt{\log x}}+\log q)$$
-- -/
-- )]
-- lemma sum_primes_not_dvd_eq_li : (sorry : Prop) := by
--   sorry

-- def C : ℝ := sorry


-- @[blueprint (statement :=
-- /--
-- For $x \ge 2$, $q \in \N$ and $a \in (\Z / q\Z)^*$ we have
-- $$ \max_{y \le x} \left| \Delta_{1_P}(y; q, a) \right| \ll \frac{1}{\log x} \left(\max_{\sqrt x \le y \le x} \left|\Delta_\Lambda(y; q, a)\right| + \sqrt x \right)$$
-- -/
-- ) (proof := /--
-- Uses combinatorics, an estimate on $\sum_{p \le x} 1/\log p$, and partial summation.
-- See Koukoulopoulos p.~279.
-- -/)]
-- theorem max_Delta_1P_le_max_Delta_Lambda : (sorry : Prop) := by
--   sorry

-- @[blueprint (statement :=
-- /--
-- For each fixed $A \ge 0$ we have
-- $$\sum_{q\le Q} \max_{y \le x} \max_{a \in (\mathbb{Z}/q\mathbb{Z})^*} \left| \Delta_{1_P}(y; q,a) \right| \ll_A \frac{x}{(\log x)^{A+1}}$$
-- uniformly for $x \ge 2$ and $1 \le Q \le \sqrt{x}/(\log (x))^{A+3}$
-- -/
-- ) (proof := /--
-- Apply \ref{BombieriVinogradov.max_Delta_1P_le_max_Delta_Lambda} and \ref{BombieriVinogradov.BV_Delta_Lambda};
-- the error terms $\sum_{q \le Q} \sqrt{x}/\varphi(q) \cdot (1/\log x)$ are absorbed by $x/(\log x)^{A+1}$.
-- -/)]
-- theorem BV_Delta_1P : (sorry : Prop) := by
--   sorry

-- end BombieriVinogradov
