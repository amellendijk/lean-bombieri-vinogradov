
import Mathlib
import Architect

import BV.ForMathlib.IsLocallyBounded

open Real MeasureTheory

@[fun_prop]
theorem Real.log_locallyBoundedOn :
    IsLocallyBoundedOn Real.log (Set.Ioi 0) := by
  constructor
  simp
  intro x hx
  simp [Filter.BoundedAtFilter]
  by_cases hx' : 1 ≤ x
  ·
    sorry
  · sorry

theorem Real.log_locallyIntegrableOn :
    LocallyIntegrableOn Real.log ({0}ᶜ) := by
  apply ContinuousOn.locallyIntegrableOn Real.continuousOn_log
  simp

/-- Comparing a logarithmic denominator at `z` with one at `x` when
`√x ≤ z ≤ x`. The hypotheses are independent of the project-specific `ProofData`. -/
@[blueprint (latexEnv := "lemma") (title := /-- Comparing $z/(\log z)^B$ with $x/(\log x)^B$ -/) (statement := /--
Let $B \in \N$ and let $1 < z \le x$ be real numbers with $\sqrt{x} \le z$. Then
$$\frac{z}{(\log z)^B} \le 2^B \frac{x}{(\log x)^B}.$$
-/) (proof := /--
From $z \ge \sqrt x$ we get $\log z \ge \tfrac12 \log x > 0$, so $(\log x)^B \le 2^B (\log z)^B$. Combining
with $z \le x$ gives $z (\log x)^B \le 2^B x (\log z)^B$, which is the claim after dividing by the
positive quantity $(\log z)^B (\log x)^B$.
-/)]
theorem pnt_ratio_bound (x z : ℝ) (B : ℕ) (hz : 1 < z) (hzx : z ≤ x)
    (hsqrt : √x ≤ z) :
    z / (Real.log z) ^ B ≤ 2 ^ B * x / (Real.log x) ^ B := by
  have hx0 : 0 ≤ x := le_trans (by positivity : 0 ≤ z) hzx
  have hxpos : 0 < x := lt_of_lt_of_le (by positivity : 0 < z) hzx
  have hsx : 0 < √x := Real.sqrt_pos.2 hxpos
  have hlogz : 0 < Real.log z := Real.log_pos hz
  have hlogx : 0 < Real.log x := Real.log_pos (lt_of_lt_of_le hz hzx)
  have hlogsqrt : Real.log x / 2 ≤ Real.log z := by
    rw [← Real.log_sqrt hx0]
    exact Real.log_le_log hsx hsqrt
  have hlog : Real.log x ≤ 2 * Real.log z := by linarith
  have hp : (Real.log x) ^ B ≤ 2 ^ B * (Real.log z) ^ B := by
    calc
      (Real.log x) ^ B ≤ (2 * Real.log z) ^ B := by gcongr
      _ = 2 ^ B * (Real.log z) ^ B := mul_pow _ _ _
  have hL : 0 < (Real.log x) ^ B := pow_pos hlogx _
  have hZ : 0 < (Real.log z) ^ B := pow_pos hlogz _
  rw [div_le_div_iff₀ hZ hL]
  nlinarith
