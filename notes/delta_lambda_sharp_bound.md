# Correcting `Delta_LambdaSharp_bound`

This note works out a *correct* proof of the Type I bound
`Delta_LambdaSharp_bound` in `BV/LambdaSharp.lean`. The proof sketch
currently recorded in the blueprint (and in the stubbed Lean file) is
**wrong**; the fix uses a Möbius–inversion / dilation trick. The price is a
divisor-count factor `τ(r)`, which is harmless downstream.

Notation throughout: `f_r := onCoprime r f`, i.e. `f_r(n) = f(n)·1_{(n,r)=1}`.
`Λ♯ = μ_{≤V} * log − Λ_{≤U} * μ_{≤V} * ζ`. We write `δ_e` for the arithmetic
function `δ_e(n) = 1_{n = e}`, so `δ_e * g` is the **dilation**
`(δ_e * g)(n) = 1_{e∣n}·g(n/e)`.

---

## 1. The bug in the old proof

The old plan was: apply `Delta_flog_bound` (which bounds
`|Δ_{f * log^v}| ≤ 2(log x)^v ∑_{k≤x}|f(k)|`) twice, with
`f = μ_{≤V,r}`, `v = 1` and `f = Λ_{≤U} * μ_{≤V,r}`, `v = 0`.

The problem: we need `Δ` of `Λ♯_r`, the function `Λ♯` **restricted to integers
coprime to `r`**, not of `Λ♯` itself. Restriction does not commute with one
factor of a convolution — it must be applied to **both** factors:

> **Lemma A (restriction is a convolution homomorphism).**
> For any set `S ⊆ ℕ` that is *multiplicatively saturated*
> (`ab ∈ S ⟺ a ∈ S ∧ b ∈ S`), and in particular for `S = {n : (n,r) = 1}`,
> ```
> (f * g)_r = f_r * g_r .
> ```
> *Proof.* If `(ab,r)=1` then `(a,r)=(b,r)=1` and conversely, so the indicator
> factors through the divisor sum:
> `1_{(n,r)=1}∑_{ab=n} f(a)g(b) = ∑_{ab=n} 1_{(a,r)=1}f(a)·1_{(b,r)=1}g(b)`.

Hence
```
(μ_{≤V} * log)_r        = μ_{≤V,r} * log_r
(Λ_{≤U} * μ_{≤V} * ζ)_r = Λ_{≤U,r} * μ_{≤V,r} * ζ_r .
```
The **second factor is now `log_r` (resp. `ζ_r`), not `log` (resp. `ζ`).**
`Delta_flog_bound` requires the *literal* `log` / `ζ` in the second slot,
because its proof uses Abel summation against the smooth, monotone function
`x ↦ (log x)^v`. The restricted function `log_r` is neither smooth nor
monotone, so `Delta_flog_bound` no longer applies. This is the bug.

---

## 2. The fix: Möbius-expand the restricted analytic factor

Restrict the *coefficient* factors (`μ_{≤V}`, `Λ_{≤U}`) freely — they only
enter through their `ℓ¹` norm — but rewrite the restricted **analytic** factor
`log_r` / `ζ_r` as a linear combination of literal `log` / `ζ`, dilated by the
divisors of `r`.

Start from Möbius inversion of the coprimality indicator:
```
1_{(n,r)=1} = ∑_{e ∣ gcd(n,r)} μ(e) = ∑_{e ∣ r} μ(e)·1_{e∣n}.
```

**For `ζ_r`:** since `1_{e∣n} = (δ_e * ζ)(n)`,
```
ζ_r = ∑_{e ∣ r} μ(e)·(δ_e * ζ).                                   (B0)
```

**For `log_r`:** when `e ∣ n` we have `log n = log e + log(n/e)`, so
```
1_{e∣n}·log n = log e · 1_{e∣n} + 1_{e∣n}·log(n/e)
              = (δ_e * (log e · ζ + log))(n),
```
using `(δ_e * ζ)(n) = 1_{e∣n}` and `(δ_e * log)(n) = 1_{e∣n}·log(n/e)`. Hence
```
log_r = ∑_{e ∣ r} μ(e)·δ_e * (log e · ζ + log).                   (B1)
```
This is exactly "express `log_r` as a linear combination of (dilated)
logarithms."

> **Lemma B.** Identities (B0) and (B1) hold as arithmetic functions.

---

## 3. Reassembling the convolution

Let `h` be a coefficient function (`h = μ_{≤V,r}` for term 1, or
`h = Λ_{≤U,r} * μ_{≤V,r}` for term 2). Convolving (B0)/(B1) with `h` and using
associativity `h * δ_e = δ_e * h =: dil_e h` (the dilation
`(dil_e h)(n) = 1_{e∣n}·h(n/e)`):

```
h * log_r = ∑_{e ∣ r} μ(e) · [ log e · ((dil_e h) * ζ) + (dil_e h) * log ]   (T1)
h * ζ_r   = ∑_{e ∣ r} μ(e) · (dil_e h) * ζ                                   (T2)
```

Each summand is now of the form `(coefficient fn) * log` or
`(coefficient fn) * ζ` — exactly the shape `Delta_flog_bound` accepts
(`ζ = ppow log 0`, `log = ppow log 1`).

**Key norm fact:** dilation preserves the `ℓ¹` norm,
```
∑_k |(dil_e h)(k)| = ∑_m |h(m)|.
```

Taking `Δ` of (T1)/(T2) (which is linear) and applying `Delta_flog_bound` to
each summand at the point `y` (`1 ≤ y ≤ x`, so `log y ≤ log x`):

- `|Δ_{(dil_e h) * ζ}(y;q,a)|   ≤ 2·‖h‖₁`
- `|Δ_{(dil_e h) * log}(y;q,a)| ≤ 2 log y · ‖h‖₁ ≤ 2 log x · ‖h‖₁`

and `log e ≤ log r ≤ log x` since `e ∣ r ≤ x`. Therefore

```
|Δ_{h * log_r}(y;q,a)| ≤ ∑_{e∣r}|μ(e)| · (2 log e + 2 log y)·‖h‖₁
                       ≤ 4 (∑_{e∣r}|μ(e)|) · ‖h‖₁ · log x
|Δ_{h * ζ_r}(y;q,a)|   ≤ 2 (∑_{e∣r}|μ(e)|) · ‖h‖₁ .
```

The factor is `∑_{e∣r}|μ(e)| = 2^{ω(r)} ≤ τ(r)` (number of divisors).

---

## 4. The two terms

Write `Δ_{Λ♯_r} = Δ_{(μ_{≤V}*log)_r} − Δ_{(Λ_{≤U}*μ_{≤V}*ζ)_r}` and use
Lemma A on each.

**Term 1** (`h = μ_{≤V,r}`, identity (T1)):
`‖h‖₁ = #{m ≤ V : (m,r)=1, μ(m)≠0} ≤ V`, so
```
|Δ_{(μ_{≤V}*log)_r}(y;q,a)| ≤ 4·τ(r)·V·log x .
```

**Term 2** (`h = Λ_{≤U,r} * μ_{≤V,r}`, identity (T2)):
`‖h‖₁ ≤ ‖Λ_{≤U,r}‖₁·‖μ_{≤V,r}‖₁ ≤ ψ(U)·V ≪ U·V` (Chebyshev:
`∑_{a≤U} Λ(a) = ψ(U) ≪ U`), so
```
|Δ_{(Λ_{≤U}*μ_{≤V}*ζ)_r}(y;q,a)| ≤ 2·τ(r)·‖h‖₁ ≪ τ(r)·U·V ≤ τ(r)·U·V·log x
```
(`log x ≥ log 2 > 0` for `x ≥ 2`).

Adding:

> **Corrected theorem.** For `1 ≤ U,V`, `2 ≤ x`, `q ∈ ℕ`, `1 ≤ r ≤ x`,
> `1 ≤ y ≤ x` and `a ∈ (ℤ/qℤ)*`,
> ```
> |Δ_{Λ♯_r}(y; q, a)| ≤ C · τ(r) · U · V · log x
> ```
> for an absolute constant `C`.

---

## 5. Remark: the `τ(r)` factor and the blueprint

The blueprint Corollary (and the current Lean statement) claim `≪ U V log x`
with **no** `r`-dependence. This is too optimistic: `Δ_{log_r}` genuinely
carries a `2^{ω(r)}` factor (its `Δ₁`-discrepancy is a signed sum of `2^{ω(r)}`
classes with no guaranteed cancellation), and the Möbius trick reflects this
honestly. So the Lean statement should be **weakened** to include `τ(r)`:

```lean
theorem Delta_LambdaSharp_bound [ProofData] {q r : ℕ} [NeZero q] {a : ZMod q}
    (ha : IsUnit a) (hr : r ≤ x) {y : ℝ} (hy : y ≤ x) :
    |Δ_[onCoprime r Λ♯](y; q, a)| ≤ C_DLS * r.divisors.card * U * V * Real.log x
```

This is harmless downstream. In the Type II section `Λ♭_r` is used with
`q ≤ (log x)^C` and `U = V = e^{√log x}` (so `UV ≤ √x`), targeting
`≪_{A,C} x/(log x)^A`. Since `τ(r) ≪_ε r^ε ≤ x^ε`, we have
`τ(r)·UV·log x ≤ x^{1/2+ε}·log x = o(x/(log x)^A)`, so the extra `τ(r)`
disappears into the existing slack.

---

## 6. Lean to-do list

New lemmas to add (roughly in dependency order):

1. **`ArithmeticFunction.on_mul`** (Lemma A): for `S` multiplicatively
   saturated, `(f * g).on S = f.on S * g.on S`. Specialize to
   `S = {n | r.Coprime n}` to get `(f*g)_r = f_r * g_r`. Needs:
   `(ab,r)=1 ↔ (a,r)=1 ∧ (b,r)=1` (`Nat.Coprime.mul_right_iff` /
   `Nat.coprime_mul_iff_right`).

2. **Dilation `δ_e * g`**: either define `δ_e` (the `1_{n=e}` arithmetic
   function) or reuse an existing "shift". Prove
   `(δ_e * ζ)(n) = if e ∣ n then 1 else 0`,
   `(δ_e * log)(n) = if e ∣ n then Real.log (n/e) else 0`, and the
   `ℓ¹`-preservation `∑_k |(δ_e * h)(k)| = ∑_m |h(m)|` (a reindex by `n ↦ e·n`).

3. **Lemma B** (B0)/(B1): `ζ.on {coprime r} = ∑_{e∈r.divisors} μ(e)·(δ_e*ζ)`
   and `log.on {coprime r} = ∑_{e∈r.divisors} μ(e)·(δ_e*(log e•ζ + log))`.
   Core input: `∑_{e ∣ gcd(n,r)} μ(e) = if (n,r)=1 then 1 else 0`
   (`Nat.sum_divisors_moebius_eq` / `ArithmeticFunction.moebius` over
   `(gcd n r).divisors`) plus `Real.log_mul` / `Real.log` of `e·(n/e)`.

4. **Assembly** (T1)/(T2): linearity of `Δ` over the `∑_{e∣r}`
   (`Delta` is `ℝ`-linear in `f`; push the finite sum through), then
   `Delta_flog_bound` per summand with `v = 1` (`ppow_one`) and `v = 0`
   (`ppow_zero`).

5. **Norm bounds**: `∑_{k≤V}|μ_{≤V,r}(k)| ≤ V`; `∑_{k≤U} Λ_{≤U,r}(k) ≤ ψ(U) ≪ U`
   (Chebyshev — check Mathlib for `Chebyshev.psi` upper bound, or reuse
   `summatory_vonMangoldt`); `ℓ¹` submultiplicativity of `*`.

6. Define `C_DLS` concretely (currently `sorry`) once the constants are fixed
   (e.g. `C_DLS = 4` works for term 1; take the max with term 2's constant).
