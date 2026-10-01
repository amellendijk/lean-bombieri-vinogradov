import Mathlib
import Architect

import BV.Chebyshev

open ArithmeticFunction

open scoped Nat

/-- The implied constant in the Sielgel-Walfisz Theorem -/
@[blueprint "thm:siegel-walfisz" (latexEnv := "theorem") (hasProof := true)]
axiom C_SW (A : ℕ) (C : ℕ) : ℝ

@[blueprint "thm:siegel-walfisz" (latexEnv := "theorem") (hasProof := true) (title := /-- Siegel--Walfisz -/) (statement := /--
Let $A, C \in \N$. For all real $x \ge 2$, all integers $1 \le q \le (\log x)^C$ and all $a \in (\Z/q\Z)^*$,
$$\psi(x; q, a) = \frac{x}{\varphi(q)} + O_{A, C}\!\left(\frac{x}{(\log x)^A}\right).$$
-/) (proof := /--
This is the Siegel--Walfisz theorem \cite{Siegel1935, Walfisz1936} in the form ``an arbitrary power
of $\log$ savings, uniformly for $q \le (\log x)^C$''; see for instance \cite[Ch.~22]{Davenport2000} or
\cite[Thm.~13.5]{Koukoulopoulos2019}. It is taken as an external input, and no proof is given here.
The implied constant is ineffective. Only the cases $C = 0$ (\Cref{cor:pnt}) and $C$ even
(\Cref{lem:SW-Lambda-q}) are used.
-/)]
axiom siegel_walfisz (A : ℕ) (C : ℕ) {x : ℝ} (hx : 2 ≤ x)
    {q : ℕ} (hq0 : 0 < q) (hq : q ≤ (Real.log x) ^ C) {a : ZMod q} (ha : IsUnit a) :
  |chebyPsi x a - x / φ q| ≤ C_SW A C * (x / (Real.log x) ^ A)


@[blueprint "thm:large-sieve" (latexEnv := "theorem") (hasProof := true)]
axiom C_LS : ℝ

  open Classical in
/- Note: We avoid phrasing this axiom in terms of our own definitions (such as summatory) to minimize the chance this axiom
introduces an inconsistency. -/
@[blueprint "thm:large-sieve" (latexEnv := "theorem") (hasProof := true) (uses := ["not:arith"]) (title := /-- The large sieve inequality -/) (statement := /--
For all real $Q \ge 1$, all $H \in \Z$, all integers $N \ge 1$ and all $c : \Z \to \C$,
$$\sum_{q \le Q} \sumstar_{\chi \bmod q} \frac{q}{\varphi(q)} \left| \sum_{H < n \le H + N} c_n \chi(n) \right|^2 \ll (N + Q^2) \sum_{H < n \le H + N} |c_n|^2,$$
where $\sumstar$ denotes a sum over primitive characters and the implied constant is absolute.
-/) (proof := /--
This is the multiplicative form of the large sieve inequality, due to Bombieri and Davenport and
in this sharp form to Montgomery and Vaughan \cite{MontgomeryVaughan1973}; see
\cite[Thm.~7.13]{IwaniecKowalski2004} or \cite[Thm.~25.6]{Koukoulopoulos2019}. It is taken as an
external input, and no proof is given here. (The inequality is known with the constant $1$ in place
of the implied constant; nothing below depends on this.)
-/)]
axiom large_sieve (Q : ℝ) (hQ : 1 ≤ Q) (H : ℤ) (N : ℕ) (hN : 0 < N) (c : ℤ → ℂ) :
    ∑ q ∈ Finset.Ioc 0 ⌊Q⌋₊, ∑ χ : DirichletCharacter ℂ q with χ.IsPrimitive,
      q / φ q * ‖∑ n ∈ Finset.Ioc H (H+N), c n * χ n‖^2 ≤
    C_LS * (N+Q^2) * ∑ n ∈ Finset.Ioc H (H+N), ‖c n‖^2
