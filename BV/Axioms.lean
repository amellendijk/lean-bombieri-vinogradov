import Mathlib
import Architect
import Challenge.Axioms

/-!
This file simply adds LeanArchitect annotations to the two axioms that are imported by the Comparator challenge file.
-/

attribute [blueprint (latexEnv := "assumption") (statement :=
/--
Let $A, C > 0$. If $1 \leq q \leq (\log x)^C$ and $a \in (\mathbb{Z}/q\mathbb{Z})^*$, then
$$
\psi(x;q,a) = \frac{x}{\varphi(q)} + O_{A, C}\left(\frac{x}{(\log x)^A}\right).
$$
-/
)] siegel_walfisz

attribute [blueprint (latexEnv := "assumption") (statement :=
/--
Let $Q \ge 1$, $H \in \Z$, $N \in \Z_{\ge 1}$ and $c = (c_{H+1}, \dots, c_{H+N}) \in \C^N$ We then have
$$\sum_{q \le Q} \sumstar_{\chi \pmod q} \frac{q}{\varphi(q)} \left| \sum_{H < n \le H+N} c_n \chi(n) \right|^2 \ll (N+Q^2) \| \vec{c} \|_2^2,$$
-/
)] large_sieve
