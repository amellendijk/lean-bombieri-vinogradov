
These notes were written (and corrected) mostly by an LLM, adapted from the proof of Theorem 26.6 in Koukoulopoulos.

# Proof of Theorem 26.6 via Mellin Smoothing

This is an amended proof of Theorem 26.6 using the Mellin smoothing infrastructure from PNT+ rather than the classical truncated Perron formula. The mathematical content is the same but the analytic argument is restructured to avoid:

- finite truncation of the Perron integral (no parameter $T$),
- the quantitative half-integer trick (no lower bound on $|\log(y/mn)|$).

We *do* still replace $y$ by $\lfloor y \rfloor + 1/2$, but only as the trivial substitution justified by the step-function structure of $\sum_{n \leq y}$; no analytic bound on $|\log(y/mn)|$ is required.

---

## Theorem 26.6

Let $f$ and $g$ be arithmetic functions supported on $[1,M]$ and $[1,N]$ respectively. For $x, Q \geq 1$,
$$
S := \sum_{\substack{q \leq Q \\ \chi \pmod{q}}}^{*} \frac{q}{\varphi(q)} \max_{y \leq x} \left|\sum_{n \leq y} (f * g)(n)\chi(n)\right|
\;\ll\;
\bigl(\sqrt{MN} + \sqrt{M}\,Q + \sqrt{N}\,Q + Q^2\bigr)(\log x)\,\|f\|_2\,\|g\|_2.
$$

---

## PNT+ ingredients used

| PNT+ name | Role |
|---|---|
| `SmoothExistence` | Provides a smooth bump $\nu \geq 0$, $\operatorname{supp}\nu \subseteq [1/2,2]$, $\int_0^\infty \nu(x)\,dx/x = 1$ |
| `DeltaSpike ν ε` | The rescaled spike $\nu_\varepsilon(x) = \nu(x^{1/\varepsilon})/\varepsilon$ |
| `Smooth1 ν ε` | The Mellin convolution $\widetilde{1}_\varepsilon = 1_{(0,1]} * \nu_\varepsilon$ |
| `Smooth1Properties_below` | $\widetilde{1}_\varepsilon(x) = 1$ for $x \leq 1 - c_1\varepsilon$, where $c_1 = \log 2$ |
| `Smooth1Properties_above` | $\widetilde{1}_\varepsilon(x) = 0$ for $x \geq 1 + c_2\varepsilon$ (with $\varepsilon < 1$), where $c_2 = 2\log 2$ |
| `MellinConvolutionTransform` | $\mathcal{M}[f * g](s) = \mathcal{M}[f](s)\cdot\mathcal{M}[g](s)$ |
| `MellinOfDeltaSpike` | $\mathcal{M}[\nu_\varepsilon](s) = \mathcal{M}[\nu](\varepsilon s)$ |
| Rapid decay of $\mathcal{M}[\nu]$ | $|\mathcal{M}[\nu](\xi)| \ll_A (1+|\xi|)^{-A}$ on any bounded vertical strip (since $\nu \in C^\infty_c((0,\infty))$) |

---

## Proof

We may assume $x \geq M, N$ (replacing $f, g$ by $f \cdot 1_{[1,x]}, g \cdot 1_{[1,x]}$ otherwise). Fix
$$
\varepsilon := \frac{1}{(2c_1 + 2c_2)(x + 1)}.
$$
This is automatically in $(0,1)$ and is calibrated so that the smoothing transition zone has width $< 1/2$ on either side of any $y \le x + 1$ (Step 1).

### Step 1: For $y = K + 1/2$, the smooth and sharp sums agree exactly

Fix $q$, $\chi$. The sharp inner sum
$$
T(y,\chi) := \sum_{m \leq M,\, n \leq N} f(m)\chi(m)\,g(n)\chi(n)\,\mathbf{1}_{mn \leq y}
$$
is constant in $y$ on each interval $[K, K+1)$ for $K \in \mathbb{Z}_{\ge 0}$. Hence
$$
\max_{y \leq x} |T(y,\chi)| \;=\; \max_{\substack{K \in \mathbb{Z} \\ 0 \le K \le x}} \bigl|T\bigl(K + \tfrac{1}{2},\,\chi\bigr)\bigr|.
$$
This is a free substitution (no estimates involved) — we use it solely to place $y$ midway between integers.

Define the **smooth approximation**
$$
T_\varepsilon(y,\chi) := \sum_{m \leq M,\, n \leq N} f(m)\chi(m)\,g(n)\chi(n)\cdot\widetilde{1}_\varepsilon(mn/y).
$$
**Claim.** For every $K \in \mathbb{Z}_{\ge 0}$ with $K \le x$ and $y = K + 1/2$,
$$
T(y,\chi) = T_\varepsilon(y,\chi).
$$

*Proof.* By `Smooth1Properties_below` and `Smooth1Properties_above`, $\widetilde{1}_\varepsilon(t) = \mathbf{1}_{t \le 1}$ for every $t \notin (1 - c_1\varepsilon,\, 1 + c_2\varepsilon)$. Equivalently, $\widetilde{1}_\varepsilon(mn/y) = \mathbf{1}_{mn \le y}$ whenever $mn \notin (y(1-c_1\varepsilon),\, y(1+c_2\varepsilon))$. By the choice of $\varepsilon$,
$$
c_1 \varepsilon y \;\le\; c_1 \varepsilon (x + 1) \;=\; \frac{c_1}{2(c_1+c_2)} \;<\; \tfrac{1}{2},
\qquad c_2 \varepsilon y \;<\; \tfrac{1}{2},
$$
so the transition zone
$$
\bigl(y(1-c_1\varepsilon),\, y(1+c_2\varepsilon)\bigr) \;\subseteq\; \bigl(y - \tfrac{1}{2},\, y + \tfrac{1}{2}\bigr) \;=\; (K, K+1)
$$
contains no integer. Since $mn \in \mathbb{Z}$, every term of $T(y,\chi)$ and $T_\varepsilon(y,\chi)$ satisfies $\widetilde{1}_\varepsilon(mn/y) = \mathbf{1}_{mn \le y}$, so the sums coincide. $\square$

In particular, **there is no transition-zone error term**: $\max_{y \le x} |T(y,\chi)| = \max_{K \le x} |T_\varepsilon(K+1/2,\chi)|$.

### Step 2: Mellin-integral representation of the smooth sum

Since $\widetilde{1}_\varepsilon$ is $C^\infty$ with compact support in $(0,\infty)$, its Mellin transform $\mathcal{M}[\widetilde{1}_\varepsilon]$ is entire and Schwartz along verticals, so Mellin inversion
$$
\widetilde{1}_\varepsilon(t) = \frac{1}{2\pi i}\int_{(\sigma)} \mathcal{M}[\widetilde{1}_\varepsilon](s)\,t^{-s}\,ds
$$
is valid for any $\sigma > 0$. Substituting $t = mn/y$ and summing the finite double sum:
$$
T_\varepsilon(y,\chi) = \frac{1}{2\pi i}\int_{(\sigma)} F_s(\chi)\,G_s(\chi)\,y^s\,\mathcal{M}[\widetilde{1}_\varepsilon](s)\,ds, \tag{$*$}
$$
where
$$
F_s(\chi) := \sum_{m \leq M} \frac{f(m)\chi(m)}{m^s}, \qquad G_s(\chi) := \sum_{n \leq N} \frac{g(n)\chi(n)}{n^s}.
$$
The interchange is justified by absolute convergence (Step 3).

**Mellin transform of $\widetilde{1}_\varepsilon$.** By `MellinConvolutionTransform`, `MellinOf1`, and `MellinOfDeltaSpike`:
$$
\mathcal{M}[\widetilde{1}_\varepsilon](s) \;=\; \mathcal{M}[1_{(0,1]}](s)\cdot\mathcal{M}[\nu_\varepsilon](s) \;=\; \frac{1}{s}\cdot\mathcal{M}[\nu](\varepsilon s).
$$
Using the rapid-decay bound $|\mathcal{M}[\nu](\xi)| \ll_A (1+|\xi|)^{-A}$ on the strip $0 \le \operatorname{Re}(\xi) \le 1$: for each $A \ge 0$ there exists $C_A > 0$ with
$$
\bigl|\mathcal{M}[\widetilde{1}_\varepsilon](\sigma + it)\bigr| \;\le\; \frac{C_A}{|\sigma+it|\,(1 + \varepsilon\,|\sigma+it|)^A}. \tag{$**$}
$$

### Step 3: Pointwise bound on the smooth sum

Choose $\sigma = 1/\log x$, so $y^\sigma \leq x^\sigma = e$ for all $y \leq x$.

From $(*)$, $(**)$, and the triangle inequality:
$$
|T_\varepsilon(y,\chi)| \;\le\; \frac{e\,C_A}{2\pi}\int_{-\infty}^{\infty} \frac{|F_{\sigma+it}(\chi)|\,|G_{\sigma+it}(\chi)|}{|\sigma+it|\,(1 + \varepsilon |\sigma+it|)^A}\,dt.
$$
The right-hand side is independent of $y$, so
$$
\max_{y \leq x} |T_\varepsilon(y,\chi)| \;\le\; \frac{e\,C_A}{2\pi}\int_{-\infty}^{\infty} \frac{|F_{\sigma+it}(\chi)|\,|G_{\sigma+it}(\chi)|}{|\sigma+it|\,(1 + \varepsilon |\sigma+it|)^A}\,dt. \tag{$***$}
$$

### Step 4: Summing over characters

Sum $(***)$ over $q \leq Q$ and primitive $\chi \pmod{q}$, then interchange sum and integral (absolute convergence, using $(MN)^{1/2}$ as a uniform bound on $|F_{\sigma+it} G_{\sigma+it}|$).

By Cauchy–Schwarz and **two applications of Theorem 25.15** (the large sieve), one with $c_m = f(m)/m^{\sigma+it}$ supported on $[1,M]$ and one with $c_n = g(n)/n^{\sigma+it}$ supported on $[1,N]$:
$$
\sum_{q,\chi}^{*}\frac{q}{\varphi(q)}|F_{\sigma+it}(\chi)|\,|G_{\sigma+it}(\chi)| \;\ll\; \sqrt{(M+Q^2)(N+Q^2)}\,\|f\|_2\,\|g\|_2.
$$
(The $m^{-\sigma}$ factors with $\sigma > 0$ and $m \ge 1$ only shrink $\ell^2$ norms.)

Therefore
$$
\sum_{q,\chi}^{*}\frac{q}{\varphi(q)}\max_{y \leq x}|T_\varepsilon(y,\chi)| \;\ll\; \sqrt{(M+Q^2)(N+Q^2)}\,\|f\|_2\,\|g\|_2 \cdot J,
$$
where
$$
J := \int_{-\infty}^{\infty} \frac{dt}{|\sigma + it|\,(1 + \varepsilon|\sigma+it|)^A}.
$$

**Bounding $J$.** Split at $|t| = 1/\varepsilon$:

- *Centre $|t| \le 1/\varepsilon$.* Here $\varepsilon|\sigma + it| \le \varepsilon\sigma + 1 \le 2$, so $(1+\varepsilon|\sigma+it|)^A \asymp 1$ and
$$
\int_{|t|\le 1/\varepsilon} \frac{dt}{|\sigma + it|} \;\le\; 2\int_0^{1/\varepsilon}\frac{dt}{\sigma + t} \;=\; 2\log\!\Bigl(1 + \tfrac{1}{\sigma\varepsilon}\Bigr) \;\ll\; \log\!\tfrac{1}{\sigma\varepsilon}.
$$
- *Tails $|t| > 1/\varepsilon$.* Here $\varepsilon|t| \ge 1$ so $(1+\varepsilon|\sigma+it|)^A \gtrsim (\varepsilon|t|)^A$, and (taking $A = 2$)
$$
\int_{|t| > 1/\varepsilon} \frac{dt}{|t|\,(\varepsilon|t|)^2} \;=\; 2\,\varepsilon^{-2}\!\int_{1/\varepsilon}^\infty \frac{dt}{t^3} \;=\; 1.
$$

Hence
$$
J \;\ll\; \log\!\tfrac{1}{\sigma\varepsilon} \;=\; \log\bigl(\log x \cdot (2c_1+2c_2)(x+1)\bigr) \;\asymp\; \log x.
$$

**Conclusion.** Combining Steps 1 and 4:
$$
S \;=\; \sum_{q,\chi}^{*}\frac{q}{\varphi(q)}\max_{y \leq x}|T(y,\chi)|
\;=\; \sum_{q,\chi}^{*}\frac{q}{\varphi(q)}\max_{\substack{K \in \mathbb{Z}\\ 0\le K \le x}} |T_\varepsilon(K+\tfrac12,\chi)|
\;\ll\; \log x \cdot \sqrt{(M+Q^2)(N+Q^2)}\,\|f\|_2\,\|g\|_2.
$$
Since $\sqrt{(M+Q^2)(N+Q^2)} \asymp \sqrt{MN} + \sqrt{M}\,Q + \sqrt{N}\,Q + Q^2$, this is the bound claimed. $\square$

---

## Comparison with the classical proof

| Feature | Classical (Lemma 7.1, truncated Perron) | This proof (Mellin smoothing) |
|---|---|---|
| Perron kernel | $x^s/s$, truncated to $|\operatorname{Im}(s)| \leq T$ | $x^s\,\mathcal{M}[\widetilde{1}_\varepsilon](s)$, full line |
| Truncation error | $O\!\left(\frac{x^\alpha}{T|\log(y/mn)|}\right)$ | None — kernel decays $\ll (1+\varepsilon|t|)^{-A}$ |
| Use of $y = K + 1/2$ | Quantitative ($|\log(y/mn)| \gg 1/y$) | Trivial substitution: places $y$ between integers so the transition zone is integer-free |
| Sharp/smooth comparison | (implicit) | **Exact equality** with $\varepsilon \asymp 1/x$ |
| Log from analysis | $\int_{-T}^{T} dt/\max\{\alpha,|t|\}$ | $J \ll \log(1/(\sigma\varepsilon)) \asymp \log x$ |

---

## Lean formalization notes

1. **Step-function reduction**: $\sum_{n \le y} a_n$ is constant on $[K, K+1)$, so $\max_{y \le x} = \max_{K \in \mathbb{Z}_{\ge 0}, K \le x}$ evaluated at $y = K + 1/2$. Routine.

2. **Integer-free transition zone**: For $y = K + 1/2$ with $K \le x$ and $\varepsilon = 1/((2c_1+2c_2)(x+1))$, the open interval $(y(1 - c_1\varepsilon), y(1 + c_2\varepsilon))$ is contained in $(K, K+1)$. A single arithmetic lemma combining the bound on $c_i \varepsilon y$ with `Smooth1Properties_below` and `Smooth1Properties_above` gives the pointwise identity $\widetilde{1}_\varepsilon(mn/y) = \mathbf{1}_{mn \le y}$ for every $mn \in \mathbb{Z}$.

3. **Mellin inversion** (equation $(*)$): $\mathcal{M}[\widetilde{1}_\varepsilon]$ is entire and Schwartz along verticals (since `Smooth1 ν ε` is $C^\infty_c((0,\infty))$ by `DeltaSpikeSupport` plus support of $\nu$). Inversion holds for any $\sigma > 0$. Likely a small auxiliary lemma beyond what is in PNT+.

4. **Rapid decay of $\mathcal{M}[\nu]$**: Replace `MellinOfPsi` (which gives only $O(1/|\xi|)$) with a Schwartz-decay bound $|\mathcal{M}[\nu](\xi)| \ll_A (1+|\xi|)^{-A}$ on $0 \le \operatorname{Re}\xi \le 1$. Standard Fourier–analysis, but needs to be stated and proved.

5. **Interchange of sum and integral**: The finite double sum over $m \le M$, $n \le N$ moves inside by linearity + absolute convergence (from $(**)$ with $A \ge 2$). Straightforward.

6. **Large sieve application**: $F_s$ involves $f(m)/m^\sigma$ with $\sigma > 0$, so $\|f(\cdot)/(\cdot)^\sigma\|_2 \le \|f\|_2$.

7. **`SmoothExistence`**: Provides $\nu \in C^\infty_c((0,\infty))$ with $\operatorname{supp}\nu \subseteq [1/2,2]$ and $\int \nu(x)\,dx/x = 1$. Everything else flows from this.
