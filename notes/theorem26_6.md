**Theorem 26.6.** Let $f$ and $g$ be two arithmetic functions supported on $[1,M]$ and $[1,N]$, respectively. For $x, Q \geq 1$ we have

$$\sum_{q \leq Q,\ \chi \pmod{q}}^{*} \frac{q}{\varphi(q)} \max_{y \leq x} \left|\sum_{n \leq y} (f * g)(n)\chi(n)\right| \ll \left(\sqrt{MN} + \sqrt{M}Q + \sqrt{N}Q + Q^2\right)(\log x)\,\|f\|_2\,\|g\|_2.$$

**Proof.** Since we are only considering integers $n \leq x$, we may assume that $x \geq M, N$. Indeed, if for example $x > M$, then we replace $f$ by $f \cdot \mathbf{1}_{[1,x]}$.

Let $S$ be the sum in the statement of the theorem, which we write

$$S = \sum_{q \leq Q,\ \chi \pmod{q}}^{*} \frac{q}{\varphi(q)} \max_{y \leq x} \left|\sum_{\substack{m \leq M \\ n \leq N}} f(m)\chi(m)\,g(n)\chi(n)\,\mathbf{1}_{mn \leq y}\right|.$$

We want to apply the Cauchy–Schwarz inequality to $S$ to separate the variables $m, n$ and pass to a product of two second moments, so that we can apply Theorem 25.15 to each variable separately. However, there are two technical obstacles. First, the variables $m$ and $n$ are tangled in the indicator function $\mathbf{1}_{mn \leq y}$; second, we have to take the maximum over $y \leq x$. We take care of both of these issues simultaneously by an application of Perron's inversion formula.

As a preparatory step, note that $mn \leq y$ if and only if $mn \leq \lfloor y \rfloor + 1/2$. Hence, in the definition of $S$ we may replace $\max_{y \leq x}$ by $\max_{y = k+1/2,\ k \in \mathbb{N},\ k \leq x}$.

Now, let $y = k + 1/2$ for some integer $k \in [1, x]$. Lemma 7.1 with $\alpha = 1/\log x$, $T = x^2$ and $mn/y$ in place of $y$ implies that

$$\mathbf{1}_{mn \leq y} = \frac{1}{2\pi i} \int_{\substack{\operatorname{Re}(s)=\alpha \\ |\operatorname{Im}(s)| \leq x^2}} \frac{(y/mn)^s}{s}\,ds + O\!\left(\frac{(y/mn)^\alpha}{x^2|\log(y/mn)|}\right).$$

We have $|y - mn| \geq 1/2$ for all integers $m, n$, by our assumption on $y$. Therefore, $|\log(y/mn)| \gg 1/y \gg 1/x$. Moreover, $(y/mn)^\alpha \ll 1$ for $y \leq x + 1/2$ and $m, n \geq 1$. We thus conclude that

$$\sum_{\substack{m \leq M,\, n \leq N}} f(m)\chi(m)g(n)\chi(n)\mathbf{1}_{mn \leq y} = \frac{1}{2\pi} \int_{-x^2}^{x^2} F_t(\chi)\,G_t(\chi)\,\frac{y^{\alpha+it}}{\alpha+it}\,dt + O\!\left(x^{-1} \sum_{m \leq M} |f(m)| \sum_{n \leq N} |g(n)|\right), \tag{26.12}$$

where

$$F_t(\chi) = \sum_{m \leq M} \frac{f(m)\chi(m)}{m^{\alpha+it}} \qquad \text{and} \qquad G_t(\chi) = \sum_{n \leq N} \frac{g(n)\chi(n)}{n^{\alpha+it}}.$$

The Cauchy–Schwarz inequality and our assumption that $M, N \leq x$ imply that

$$\sum_{m \leq M} |f(m)| \leq x^{1/2}\|f\|_2 \qquad \text{and} \qquad \sum_{n \leq N} |g(n)| \leq x^{1/2}\|g\|_2.$$

In the main term of (26.12), we note that $|y^{\alpha+it}| \ll 1$ for $y \leq x + 1/2$, as well as that $|\alpha + it| \asymp \max\{\alpha, |t|\}$. Therefore,

$$\sum_{\substack{m \leq M,\, n \leq N}} f(m)\chi(m)g(n)\chi(n)\mathbf{1}_{mn \leq y} \ll \int_{-x^2}^{x^2} \frac{|F_t(\chi)G_t(\chi)|}{\max\{\alpha,|t|\}}\,dt + \|f\|_2\|g\|_2.$$

The right-hand side no longer depends on $y$. Consequently,

$$S \ll \int_{-x^2}^{x^2} \left(\sum_{q \leq Q,\ \chi \pmod{q}}^{*} \frac{q}{\varphi(q)} \cdot |F_t(\chi)| \cdot |G_t(\chi)|\right) \frac{dt}{\max\{\alpha,|t|\}} + Q^2\|f\|_2\|g\|_2.$$

By the Cauchy–Schwarz inequality and two applications of Theorem 25.15, one where we take $c_n = f(n)/n^{\alpha+it}$ for $n \in [1, M]$, and another one with $c_n = g(n)/n^{\alpha+it}$ for $n \in [1, N]$, we conclude that

$$\sum_{q \leq Q,\ \chi \pmod{q}}^{*} \frac{q}{\varphi(q)} \cdot |F_t(\chi)| \cdot |G_t(\chi)| \ll \sqrt{(M+Q^2)(N+Q^2)}\,\|f\|_2\|g\|_2.$$

Since $\sqrt{(M+Q^2)(N+Q^2)} \asymp \sqrt{MN} + \sqrt{M}Q + \sqrt{N}Q + Q^2$ and

$$\int_{-x^2}^{x^2} \frac{dt}{\max\{\alpha,|t|\}} = \int_{|t| \leq \alpha} \frac{dt}{\alpha} + \int_{\alpha < |t| \leq x^2} \frac{dt}{|t|} \ll \log x,$$

the theorem has been established. $\square$
