# Blueprint (informal overview and divergence log)

The maintained, detailed blueprint of this project is **generated from the Lean sources**:
every numbered definition, lemma and theorem carries a
`@[blueprint (title := …) (statement := …) (proof := …)]` annotation in `BV/*.lean`, and the
narrative and ordering live in `blueprint/src/content.tex`. Build it with

```sh
lake build :blueprint          # extracts .lake/build/blueprint/library/BV.tex
uvx leanblueprint pdf          # or: uvx leanblueprint web
```

(or run `./build_blueprint.sh`). The rendered version is linked from the README. When a Lean
statement changes, change the annotation next to it; the LaTeX in `content.tex` should not need
to change.

This file is only a short informal summary of the argument, followed by a log of the places
where the formal proof deviates from the textbook (Koukoulopoulos, *The Distribution of Prime
Numbers*, Chapter 26), which the original hand-written blueprint followed.

## The argument in one page

Write $\Delta_f(y;q,a) = \sum_{n\le y,\, n\equiv a\ (q)} f(n) - \varphi(q)^{-1}\sum_{n\le y,\,(n,q)=1} f(n)$.

1. **Reduction to $\Delta_\Lambda$.** $\psi(y;q,a) - y/\varphi(q) = \Delta_\Lambda(y;q,a) + \varphi(q)^{-1}(\sum_{n\le y,(n,q)=1}\Lambda(n) - y)$;
   the bracket is controlled by the PNT with logarithmic savings (Siegel–Walfisz at $q=1$) and the
   elementary bound $\sum_{n\le y,(n,q)>1}\Lambda(n) \le \log q\log y/\log 2$. Summing
   $1/\varphi(q)$ over $q\le Q$ costs $\log x$. The range $y<\sqrt x$ uses the trivial bound
   $|\psi(y;q,a)-y/\varphi(q)| \le (\log 4+5)y$.
2. **Vaughan's identity.** With $UV\le\sqrt x$, $U,V\ge e^{\sqrt{\log x}}$:
   $\Lambda = \Lambda^\sharp + \Lambda^\flat + \Lambda_{\le U}$, $\Lambda^\sharp = \mu_{\le V}*\log - \Lambda_{\le U}*\mu_{\le V}*1$,
   $\Lambda^\flat = (\Lambda_{>U}*1)*\mu_{>V}$.
3. **Small part.** $|\Delta_{\Lambda_{\le U}}| \le 2U\log x$ pointwise; $Q\cdot 2U\log x \le 2x/(\log x)^{A+2}$.
4. **Type I.** $|\Delta_{f*\log^v}(y;q,a)| \le 2(\log y)^v\|f\|_1$ (Abel summation against $|\Delta_1|\le 1$).
   For the *restricted* function $\Lambda^\sharp_r$ one Möbius-expands $\log_r, 1_r$ into $\tau(r)$
   dilated copies, giving $|\Delta_{\Lambda^\sharp_r}| \le 6\,\tau(r)\,UV\log x$; averaging $\tau$
   over $q\le Q$ gives $\ll x/(\log x)^A$.
5. **Type II.** Expand $\varphi(q)\Delta_{\Lambda^\flat}(y;q,a)$ in characters and group by conductor $d\mid q$.
   Conductors $d\le(\log x)^C$: Möbius-invert back to discrepancies of $\Lambda^\flat_q$ modulo
   $s\le(\log x)^C$ and apply Siegel–Walfisz (via $\Lambda^\flat_q = \Lambda_q - \Lambda^\sharp_q - (\Lambda_{\le U})_q$).
   Conductors $d>(\log x)^C$: regroup by $r=q/d$ into
   $T_r(Q) = \sum_{(\log x)^C<d\le Q/r}\varphi(d)^{-1}\sum^*_{\xi\ (d)}\max_y|\sum_{n\le y}\Lambda^\flat_r(n)\xi(n)|$,
   dyadically decompose $\Lambda^\flat_r = \sum_j (f_j)_r*(g_j)_r$, and apply the maximal large sieve
   for convolutions (Theorem 26.6) to each block. With $C=A+4$ this gives $\ll_A x/(\log x)^A$.
6. **Theorem 26.6** is proved with a *smoothed* cutoff $\widetilde 1_\varepsilon$ (from PNT+) instead of the
   truncated Perron formula: at half-integers $y=K+\tfrac12$ and $\varepsilon = 1/(6\log 2\cdot x)$ the
   smoothed and sharp cutoffs agree exactly; Mellin inversion on $\Re s = 1/\log(x+1)$, Cauchy–Schwarz,
   the large sieve twice, and a kernel integral $J\ll\log(x+1)$ finish the proof.

## Divergences from the textbook / the original hand-written blueprint

| Topic | Textbook / old blueprint | Formal proof |
|---|---|---|
| Statement | $\pi(y;q,a) - \mathrm{li}(y)/\varphi(q)$, $x/(\log x)^{A+1}$ | $\psi(y;q,a) - y/\varphi(q)$, $x/(\log x)^{A}$, $1\le y\le x$ |
| Range of $x$ | $x\ge 2$ | $x\ge 2$; the parameter constraints force $\log x\ge 16$, so $x\le e^{32}$ is handled by the trivial bound and $U=V=e^{\sqrt{\log x}}$ is only used for $x>e^{32}$ |
| Type I bound for $\Lambda^\sharp_r$ | $\ll UV\log x$ | needs a factor $\tau(r)$ (restriction commutes with convolution, so the smooth factor becomes $\log_r$); the old bound is unprovable as stated |
| Small conductors | stated with $1/\varphi(q)$ on both sides, no range for $q$ | stated without $1/\varphi(q)$; needs $q\le\sqrt x$ to absorb $\tau(q)\le 2x^{1/4}$; uses Siegel–Walfisz with exponents $(A+2C+1, 2C)$ |
| `character_sum_Mobius` | $F_P(q) = \Delta_{f_{rP}}$; hypothesis $r\le x$ | $F_P(q) = \varphi(q)\Delta_{f_{rP}}$; no hypothesis on $r$ |
| `character_sum_by_conductor` | as stated | needs $q\ge 1$ and excludes $d=1$ (the original statement was off by $f(\chi_0)$) |
| Reduction to $T_r$ | $Q$ arbitrary | needs $Q\le\sqrt x$; regrouping is an inequality of index sets, not an equality |
| $T_r$ bound | $T_r\ll \dots$ | needs $C\ge 3$, $2\le Q\le x$; the $1/\sqrt U,1/\sqrt V$ savings come termwise from $U<2^j\le 2x/V$ (no geometric series), costing one $\log$ from the number of blocks |
| Large sieve for convolutions | truncated Perron formula, $x,Q\ge 1$ | smoothed cutoff, exact at half-integers; $x\ge 2$ in the real version, $\log(x+1)$ in the smoothed version |
| Maxima | real maxima with boundedness side conditions | suprema in $[0,\infty]$ (`maxy`, `maxya`), finiteness is part of each estimate |
| Choice of $U,V$ | $U=V=e^{\sqrt{\log x}}$ throughout | all estimates uniform in any datum with $UV\le\sqrt x$, $U,V\ge e^{\sqrt{\log x}}$ |

Related notes: `notes/delta_lambda_sharp_bound.md` (the $\tau(r)$ correction),
`notes/theorem26_6_smooth.md` (the smoothed Perron argument), `notes/main_results_refactor.md`.
