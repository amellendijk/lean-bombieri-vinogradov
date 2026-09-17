import Mathlib
import Architect

import BV.Axioms
import BV.Defs
import BV.VonMangoldt

open ArithmeticFunction

noncomputable def C_D1 (A : ℕ) : ℝ := C_SW A 0

/-- The prime number theorem consequence of Siegel–Walfisz at an explicit endpoint. -/
@[blueprint (title := /-- The prime number theorem with logarithmic savings -/) (statement := /--
For every $A \in \N$ and every real $z \ge 2$,
$$\sum_{n \le z} \Lambda(n) = z + O_A\!\left(\frac{z}{(\log z)^A}\right).$$
-/) (proof := /--
Apply \Cref{siegel_walfisz} with $C = 0$, $q = 1$ (note $1 \le (\log z)^0 = 1$) and $a = 1$: then
$\psi(z; 1, 1) = \sum_{n \le z} \Lambda(n)$ and $\varphi(1) = 1$.
-/)]
lemma PNT (A : ℕ) {z : ℝ} (hz : 2 ≤ z) :
    |summatory (fun n ↦ Λ n) z - z| ≤ C_D1 A * (z / Real.log z ^ A) := by
  have h := siegel_walfisz A 0 hz (q := 1) (by positivity) (by simp)
    (a := (1 : ZMod 1)) (by simp)
  simp only [ψ_one_one] at h
  rw [← summatory_vonMangoldt] at h
  simpa [C_D1] using h

noncomputable def C_SVNC : ℝ := (Real.log 2)⁻¹

theorem C_SVNC_le : C_SVNC ≤ (Real.log 2)⁻¹ := le_rfl

/-- The unique project-facing non-coprime von Mangoldt estimate. -/
lemma sum_vonMangoldt_not_coprime_ll_logq {z : ℝ} (hz : 2 ≤ z)
    {q : ℕ} (hq : 0 < q) :
    |summatory (fun n ↦ if ¬q.Coprime n then Λ n else 0) z| ≤
      C_SVNC * (Real.log q * Real.log z) := by
  rw [abs_of_nonneg]
  · simpa [summatory_apply, C_SVNC, div_eq_mul_inv, mul_assoc, mul_left_comm,
      mul_comm] using sum_vonMangoldt_not_coprime_le hz hq
  · positivity

/-- Public generic coprime-error consequence of Siegel–Walfisz. -/
@[blueprint (title := /-- Prime number theorem for integers coprime to $q$ -/) (statement := /--
For every $B \in \N$, every real $z \ge 2$ and every integer $q \ge 1$,
$$\sum_{\substack{n \le z \\ (n, q) = 1}} \Lambda(n) = z + O_B\!\left(\frac{z}{(\log z)^B}\right) + O\big(\log q \cdot \log z\big),$$
the second error term having an absolute implied constant.
-/) (proof := /--
Write $\sum_{n \le z, (n,q) = 1} \Lambda(n) - z = \big(\sum_{n \le z} \Lambda(n) - z\big) - \sum_{n \le z, (n, q) > 1} \Lambda(n)$
and apply the triangle inequality: the first term is bounded by \Cref{PNT} and the second by
\Cref{sum_vonMangoldt_not_coprime_le}.
-/)]
lemma coprime_vonMangoldt_error (B : ℕ) {z : ℝ} (hz : 2 ≤ z)
    {q : ℕ} (hq : 0 < q) :
    |summatory (fun n ↦ if q.Coprime n then Λ n else 0) z - z| ≤
      C_D1 B * (z / (Real.log z) ^ B) + C_SVNC * (Real.log q * Real.log z) := by
  have hsplit :
      summatory (fun n ↦ if q.Coprime n then Λ n else 0) z - z =
        (summatory (fun n ↦ Λ n) z - z) -
          summatory (fun n ↦ if ¬q.Coprime n then Λ n else 0) z := by
    rw [← summatory_sub_ite]
    ring
  rw [hsplit]
  exact (abs_sub _ _).trans (add_le_add (PNT B hz)
    (sum_vonMangoldt_not_coprime_ll_logq hz hq))

open ProofData in
lemma PNT_at_x [ProofData] (A : ℕ) :
    |summatory (fun n ↦ Λ n) x - x| ≤ C_D1 A * (x / Real.log x ^ A) :=
  PNT A le_x

open ProofData in
lemma coprime_vonMangoldt_error_at_x [ProofData] (B : ℕ) {q : ℕ} (hq : 0 < q) :
    |summatory (fun n ↦ if q.Coprime n then Λ n else 0) x - x| ≤
      C_D1 B * (x / (Real.log x) ^ B) + C_SVNC * (Real.log q * Real.log x) :=
  coprime_vonMangoldt_error B le_x hq
