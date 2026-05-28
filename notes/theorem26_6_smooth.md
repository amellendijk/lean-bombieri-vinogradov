


Corrections:

The estimate in step 1 is not good enough, should use C-S directly on the set R = {(m, n) | y(1-c\eps) \le m n \le y(1+c\eps)}, you get |Error| \le |R| * norm f * norm g

Then $|R| \ll_{\varepsilon'} (\varepsilon y + 1) y^{\varepsilon'}$ using the divisor bound.

OR: We don't even need the divisor bound at all! We can just estimate $\tau(x) \le x$ and fix $\varepsilon = 1/x^2$.

Written by Claude Sonnet (And very incorrect):
# Proof of Theorem 26.6 via Mellin Smoothing

This is an amended proof of Theorem 26.6 using the Mellin smoothing infrastructure from PNT+ rather than the classical truncated Perron formula. The mathematical content is the same but the analytic argument is restructured to avoid:
- finite truncation of the Perron integral (no parameter $T$),
- the half-integer trick ($y = k + 1/2$),
- bounding $|\log(y/mn)|^{-1}$ from below.

Instead the main price is an explicit sharp-to-smooth error analysis via the properties of `Smooth1`.

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
| `MellinOfPsi` | $|\mathcal{M}[\nu](s)| \leq C/|s|$ uniformly for $\operatorname{Re}(s)$ in a bounded strip |

---

## Proof

We may assume $x \geq M, N$ (replacing $f, g$ by $f \cdot 1_{[1,x]}, g \cdot 1_{[1,x]}$ otherwise). Fix $\varepsilon \in (0,1)$; the precise value is chosen at the end.

### Step 1: Smooth approximation to the sharp sum

Fix $q$, $\chi$, and $y \leq x$. Write the sharp inner sum as
$$
T(y,\chi) := \sum_{m \leq M,\, n \leq N} f(m)\chi(m)\,g(n)\chi(n)\,\mathbf{1}_{mn \leq y}.
$$
Define the **smooth approximation**
$$
T_\varepsilon(y,\chi) := \sum_{m \leq M,\, n \leq N} f(m)\chi(m)\,g(n)\chi(n)\cdot\widetilde{1}_\varepsilon(mn/y),
$$
where $\widetilde{1}_\varepsilon = \mathtt{Smooth1}(\nu,\varepsilon)$.

**Error bound.** By `Smooth1Properties_below`, $\widetilde{1}_\varepsilon(t) = 1$ for $t \leq 1 - c_1\varepsilon$. By `Smooth1Properties_above`, $\widetilde{1}_\varepsilon(t) = 0$ for $t \geq 1 + c_2\varepsilon$. Therefore $\mathbf{1}_{mn \leq y} - \widetilde{1}_\varepsilon(mn/y) = 0$ unless $mn \in (y(1-c_1\varepsilon),\, y(1+c_2\varepsilon))$, and
$$
|T(y,\chi) - T_\varepsilon(y,\chi)| \leq \sum_{\substack{m \leq M,\, n \leq N \\ y(1-c_1\varepsilon) < mn < y(1+c_2\varepsilon)}} |f(m)|\,|g(n)|
\;\leq\; \|f\|_1\,\|g\|_1
\;\leq\; \sqrt{MN}\,\|f\|_2\,\|g\|_2.
$$
<!-- (We use the crude upper bound $\|f\|_1 \leq M^{1/2}\|f\|_2$ and similarly for $g$; the short-interval restriction on $mn$ is discarded.) -->

Note: After correction, this bound becomes $\varepsilon x^{1+\varepsilon'}\,\|f\|_2\,\|g\|_2$.
### Step 2: Mellin-integral representation of the smooth sum

We express $T_\varepsilon(y,\chi)$ as a vertical integral. Since $\widetilde{1}_\varepsilon$ is smooth with compact support in $(0,\infty)$, its Mellin transform $\mathcal{M}[\widetilde{1}_\varepsilon]$ is entire, and Mellin inversion gives
$$
\widetilde{1}_\varepsilon(t) = \frac{1}{2\pi i}\int_{(\sigma)} \mathcal{M}[\widetilde{1}_\varepsilon](s)\,t^{-s}\,ds
$$
for any $\sigma > 0$. Substituting $t = mn/y$ and summing over $m, n$:
$$
T_\varepsilon(y,\chi) = \frac{1}{2\pi i}\int_{(\sigma)} F_s(\chi)\,G_s(\chi)\,y^s\,\mathcal{M}[\widetilde{1}_\varepsilon](s)\,ds, \tag{$*$}
$$
where
$$
F_s(\chi) = \sum_{m \leq M} \frac{f(m)\chi(m)}{m^s}, \qquad G_s(\chi) = \sum_{n \leq N} \frac{g(n)\chi(n)}{n^s}.
$$
The interchange of sum and integral is justified by absolute convergence (Step 3 below).

**Mellin transform of $\widetilde{1}_\varepsilon$.** By `MellinConvolutionTransform`:
$$
\mathcal{M}[\widetilde{1}_\varepsilon](s) = \mathcal{M}[1_{(0,1]}](s)\cdot\mathcal{M}[\nu_\varepsilon](s) = \frac{1}{s}\cdot\mathcal{M}[\nu](\varepsilon s).
$$

Note: Instead of MellinOfPsi use the bound $\mathcal{M}[\widetilde{1}_\varepsilon] \ll_A \frac{1}{|s|} (1+\varepsilon |s|)^{-A}$ which we get from $\nu(\xi) \ll_{A} (1+|\xi|)^{-A}$ (using smooth+compact support).
(using `MellinOf1` and `MellinOfDeltaSpike`). By `MellinOfPsi` applied with the strip $\varepsilon\sigma \leq \operatorname{Re}(\varepsilon s) \leq 2$, there exists $C > 0$ such that
$$
\bigl|\mathcal{M}[\widetilde{1}_\varepsilon](\sigma + it)\bigr| \leq \frac{1}{|\sigma+it|}\cdot\frac{C}{\varepsilon\,|\sigma+it|} = \frac{C}{\varepsilon\,(\sigma^2+t^2)}. \tag{$**$}
$$

### Step 3: Bounding the smooth sum

Choose $\sigma = 1/\log x$, so $y^\sigma \leq x^\sigma = e$ for all $y \leq x$.

From $(*)$ and $(**)$ and the triangle inequality:
$$
|T_\varepsilon(y,\chi)| \leq \frac{e}{2\pi}\int_{-\infty}^{\infty} |F_{\sigma+it}(\chi)|\,|G_{\sigma+it}(\chi)|\cdot\frac{C}{\varepsilon(\sigma^2+t^2)}\,dt.
$$
The right-hand side is **independent of $y$**, so
$$
\max_{y \leq x} |T_\varepsilon(y,\chi)| \leq \frac{eC}{2\pi\varepsilon}\int_{-\infty}^{\infty} \frac{|F_{\sigma+it}(\chi)|\,|G_{\sigma+it}(\chi)|}{\sigma^2+t^2}\,dt. \tag{$***$}
$$

### Step 4: Summing over characters

Sum $(***)$ over $q \leq Q$ and primitive $\chi \pmod{q}$, interchange sum and integral (absolute convergence, using $(MN)^{1/2}$ as a uniform bound on $|F_t G_t|$):
$$
\sum_{q \leq Q,\,\chi}^{*} \frac{q}{\varphi(q)}\max_{y \leq x}|T_\varepsilon(y,\chi)| \leq \frac{eC}{2\pi\varepsilon}\int_{-\infty}^{\infty} \left(\sum_{q,\chi}^{*}\frac{q}{\varphi(q)}|F_t(\chi)|\,|G_t(\chi)|\right)\frac{dt}{\sigma^2+t^2}.
$$

By the Cauchy–Schwarz inequality and **two applications of Theorem 25.15** (the large sieve), one with coefficients $c_m = f(m)/m^{\sigma+it}$ supported on $[1,M]$ and one with $c_n = g(n)/n^{\sigma+it}$ supported on $[1,N]$:
$$
\sum_{q,\chi}^{*}\frac{q}{\varphi(q)}|F_t(\chi)|\,|G_t(\chi)| \ll \sqrt{(M+Q^2)(N+Q^2)}\,\|f\|_2\,\|g\|_2.
$$
(The $m^{-\sigma}$ factors affect $\|f\|_2$ by at most $e^{1/2}$ since $\sigma \log M \leq \sigma \log x = 1$.)

The remaining integral evaluates as
$$
\int_{-\infty}^{\infty} \frac{dt}{\sigma^2+t^2} = \frac{\pi}{\sigma} = \pi\log x.
$$
Note: This integral is different now, but it becomes at most $\int_{1 / \varepsilon}^\infty\frac 1 {|t|(1+\varepsilon|t|)} dt = \log 2$ on the tails and $\int_0^{1 / \varepsilon} \frac {dt} {\sigma + t} \ll \log {}\frac 1 {\sigma \varepsilon}$ in the centre

Combining:
$$
\sum_{q,\chi}^{*}\frac{q}{\varphi(q)}\max_{y \leq x}|T_\varepsilon(y,\chi)| \ll \frac{\log x}{\varepsilon}\cdot\sqrt{(M+Q^2)(N+Q^2)}\,\|f\|_2\,\|g\|_2. \tag{A}
$$

### Step 5: Error from the transition zone

From Step 1:
$$
\sum_{q,\chi}^{*}\frac{q}{\varphi(q)}\max_{y \leq x}|T(y,\chi) - T_\varepsilon(y,\chi)|
\leq \left(\sum_{q \leq Q,\,\chi}^{*}\frac{q}{\varphi(q)}\right)\cdot\sqrt{MN}\,\|f\|_2\,\|g\|_2.
$$
Since $\sum_{q \leq Q,\,\chi}^{*} q/\varphi(q) \leq \sum_{q \leq Q} q \ll Q^2$:
$$
\sum_{q,\chi}^{*}\frac{q}{\varphi(q)}\max_{y \leq x}|T - T_\varepsilon| \ll Q^2\sqrt{MN}\,\|f\|_2\,\|g\|_2. \tag{B}
$$

### Step 6: Combining and optimising $\varepsilon$

From the triangle inequality, $S \leq \text{(A)} + \text{(B)}$:
$$
S \ll \left(\frac{\log x}{\varepsilon}\cdot\sqrt{(M+Q^2)(N+Q^2)} + Q^2\sqrt{MN}\right)\|f\|_2\,\|g\|_2.
$$

**Choice $\varepsilon = 1$ (or any fixed constant in $(0,1)$).** This sets $1/\varepsilon = O(1)$, giving
$$
S \ll \left(\log x\cdot\sqrt{(M+Q^2)(N+Q^2)} + Q^2\sqrt{MN}\right)\|f\|_2\,\|g\|_2.
$$
For the second term: $Q^2\sqrt{MN} \leq Q^2\sqrt{(M+Q^2)(N+Q^2)}$, and since $\log x \geq 1$ for $x \geq e$ (and the result is trivial for $x < e$), we have $Q^2 \leq Q^2 \log x$, so:
$$
S \ll \sqrt{(M+Q^2)(N+Q^2)}\cdot\log x\cdot\|f\|_2\,\|g\|_2
\;\asymp\;
\bigl(\sqrt{MN}+\sqrt{M}\,Q+\sqrt{N}\,Q+Q^2\bigr)\log x\cdot\|f\|_2\,\|g\|_2.
$$
$\square$

---

## Comparison with the classical proof

| Feature | Classical (Lemma 7.1, truncated Perron) | This proof (Mellin smoothing) |
|---|---|---|
| Perron kernel | $x^s/s$, truncated to $|\operatorname{Im}(s)| \leq T$ | $x^s\,\mathcal{M}[\widetilde{1}_\varepsilon](s)$, full line |
| Truncation error | $O\!\left(\frac{x^\alpha}{T|\log(y/mn)|}\right)$, requires $y = k+\tfrac12$ | None |
| Half-integer trick | Required ($|{}\log(y/mn){}| \gg 1/y$) | Not needed |
| Kernel decay | $O(1/|t|)$ — forces finite truncation at $T$ | $O(1/(\varepsilon|t|^2))$ — integral over $\mathbb{R}$ converges |
| Log from integral | $\int_{-T}^{T}dt/\max\{\alpha,|t|\} \asymp \log x$ | $\int_{-\infty}^\infty dt/(\sigma^2+t^2) = \pi/\sigma = \pi\log x$ |
| Sharp/smooth issue | Handled implicitly (sharp indicator from the start) | Explicit error bound in Step 5 |

The two proofs produce the same asymptotic bound. The advantage here is entirely in proof cleanness: no finite $T$, no error-term for truncation, no $|\log(y/mn)|$ lower bound.

---

## Lean formalization notes

The main steps that require care in Lean:

1. **Mellin inversion** (equation $(*)$): Requires that $\mathcal{M}[\widetilde{1}_\varepsilon]$ is in the right function space for inversion. Since `Smooth1 ν ε` is smooth and compactly supported in $(0,\infty)$ (by `DeltaSpikeSupport` and the support of $\nu$), its Mellin transform is entire and Schwartz-like in the imaginary direction, so inversion holds for any $\sigma > 0$. This may need a small auxiliary lemma not directly in PNT+.

2. **Interchange of sum and integral**: The finite sum over $m \leq M$, $n \leq N$ can be moved inside the integral by linearity + absolute convergence (from $(**)$). Straightforward.

3. **Large sieve application**: The functions $F_s(\chi)$ involve $f(m)/m^\sigma$; since $\sigma \leq 1/\log x$ and $m \leq M \leq x$, we have $m^\sigma \leq e$, so the norm satisfies $\|f(\cdot)/(\cdot)^\sigma\|_2 \leq e^{1/2}\|f\|_2$. This uses that $M \leq x$.

4. **The $Q^2$ error absorption**: We use $\log x \geq 1$ for $x \geq e$. For $x \in [2, e)$ the bound is $O(1)$ and trivially holds.

5. **`SmoothExistence`**: Provides $\nu$ with $\operatorname{supp}\nu \subseteq [1/2,2]$, $\int \nu/x = 1$, and $C^\infty$, which is exactly what `MellinOfPsi` and `DeltaSpikeMass` require.
