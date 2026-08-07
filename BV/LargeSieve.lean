import Mathlib
import Architect

import LargeSieve.Multiplicative

open ArithmeticFunction
open scoped Nat

/-- The large sieve constant, made explicit via Gallagher's 1967 additive large sieve
(`LargeSieve.multiplicative_large_sieve_gallagher`). Formerly an opaque `axiom C_LS : ℝ`. -/
noncomputable def C_LS : ℝ := 8 * Real.pi ^ 2 + 2

/- Formerly `axiom large_sieve`. Now a theorem, discharged from
`LargeSieve.multiplicative_large_sieve_gallagher`.

Two changes from the original axiom statement are mathematically necessary:
* the inner sum ranges over **primitive** characters (`∑*`), matching the classical
  multiplicative large sieve and this repository's own downstream usage
  (`Flat/Perron.lean`, `LambdaFlat.lean`, both `∑ χ … with χ.IsPrimitive`). The
  original all-characters form is false: the principal character contributes ≈ N²
  to the left side, breaking the bound for large Q.
* characters are `ℂ`-valued (as used downstream) rather than `ℚ`-valued. -/
open scoped Classical in
@[blueprint (latexEnv := "assumption") (statement :=
/--
Let $Q \ge 1$, $H \in \Z$, $N \in \Z_{\ge 1}$ and $c = (c_{H+1}, \dots, c_{H+N}) \in \C^N$ We then have
$$\sum_{q \le Q} \sumstar_{\chi \pmod q} \frac{q}{\varphi(q)} \left| \sum_{H < n \le H+N} c_n \chi(n) \right|^2 \ll (N+Q^2) \| \vec{c} \|_2^2,$$
-/
)]
theorem large_sieve (Q : ℝ) (hQ : 1 ≤ Q) (H : ℤ) (N : ℕ) (hN : 0 < N) (c : ℤ → ℂ) :
    ∑ q ∈ Finset.Ioc 0 ⌊Q⌋₊,
      ∑ χ : DirichletCharacter ℂ q with χ.IsPrimitive,
        (q : ℝ) / φ q * ‖∑ n ∈ Finset.Ioc H (H+N), c n * χ n‖^2 ≤
    C_LS * (N+Q^2) * ∑ n ∈ Finset.Ioc H (H+N), ‖c n‖^2 := by
  classical
  exact multiplicative_large_sieve_gallagher Q hQ H N hN c
    (fun q => Finset.univ.filter (fun χ : DirichletCharacter ℂ q => χ.IsPrimitive))
    (fun _ _ hχ => (Finset.mem_filter.mp hχ).2)
