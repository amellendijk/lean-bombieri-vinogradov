# Reusable intermediate lemmas from the main-results refactor

This note records intermediate results exposed by the refactor in
`notes/main_results_refactor.md`. They are candidates for extraction from the
current proofs into reusable lemmas. The first two are the strongest candidates;
the remaining items are smaller project-level conveniences.

## 1. Divisor/hyperbola reindexing

The reindexing step in `BV_LambdaFlat_via_T` currently embeds pairs `(q, d)`
with `d ∣ q` into pairs `(r, d)` via `r = q / d`. The indexing correspondence
should give an equality of the following form:

```lean
∑ q ∈ Finset.Ioc 0 ⌊Q⌋₊,
    ∑ d ∈ q.divisors with L < (d : ℝ), F d (q / d)
  =
∑ r ∈ Finset.Ioc 0 ⌊Q⌋₊,
    ∑ d ∈ Finset.Ioc ⌊L⌋₊ ⌊Q / r⌋₊, F d r
```

The current proof appears in the “Step B” portion of
`BV_LambdaFlat_via_T`. It proves only the inequality needed by that theorem,
using an image inclusion and nonnegativity. Proving the exact reindexing would:

- remove the nonnegativity assumption;
- allow a codomain as general as an additive commutative monoid;
- isolate the endpoint facts `L < d` and `d ≤ Q / r`;
- make the result independent of `ProofData` and the project axioms.

This is a plausible upstream candidate, perhaps near the standard divisor-sum
API. A project-local version could initially live in a `BV/ForMathlib` module.

## 2. Generic dyadic decomposition bound

The final part of `T_r_bound` proves a generic estimate for a nonnegative
function `B`. A natural-endpoint version could look like:

```lean
∑ d ∈ Finset.Ioc P W, B d / (d : ℝ)
  ≤
∑ j ∈ Finset.Icc (Nat.log 2 P) (Nat.log 2 W),
    ((2 : ℝ) ^ j)⁻¹ * summatory B ((2 : ℝ) ^ (j + 1))
```

This uses the facts

```lean
(2 : ℝ) ^ Nat.log 2 d ≤ d
d < 2 ^ (Nat.log 2 d + 1)
```

and groups the original sum by `Nat.log 2 d`. Extracting the argument would
remove substantial endpoint and fibrewise-sum bookkeeping from `T_r_bound`.

The foundational lemma should preferably use natural endpoints `P` and `W`.
A short wrapper can then instantiate it with

```lean
P = ⌊(Real.log x) ^ C⌋₊
W = ⌊Q / r⌋₊.
```

This is likely reusable in later analytic estimates based on bounds for partial
sums.

## 3. Totient inequality along a divisor

The coefficient comparison inside `BV_LambdaFlat_via_T` implicitly proves that
for `0 < q` and `d ∣ q`,

```lean
d.totient * (q / d).totient ≤ q.totient
```

This follows immediately from `Nat.totient_super_multiplicative` after rewriting
`d * (q / d) = q`. Its real inverse consequence is

```lean
(q.totient : ℝ)⁻¹
  ≤ (d.totient : ℝ)⁻¹ * ((q / d).totient : ℝ)⁻¹.
```

The natural-valued statement is the more fundamental reusable lemma and may be
appropriate for Mathlib. The inverse-valued statement can remain a small
project corollary.

## 4. Transporting finite real majorants to `ℝ≥0∞`

Several canonical estimates repeat the following pattern:

```lean
F i ≤ ENNReal.ofReal (b i)
0 ≤ b i
∑ i ∈ s, b i ≤ B
```

from which they conclude

```lean
∑ i ∈ s, F i ≤ ENNReal.ofReal B.
```

A generic helper could have a statement resembling:

```lean
theorem finset_sum_le_ofReal
    (hF : ∀ i ∈ s, F i ≤ ENNReal.ofReal (b i))
    (hb : ∀ i ∈ s, 0 ≤ b i)
    (hB : ∑ i ∈ s, b i ≤ B) :
    ∑ i ∈ s, F i ≤ ENNReal.ofReal B
```

Its proof packages `Finset.sum_le_sum`, `ENNReal.ofReal_sum_of_nonneg`, and
`ENNReal.ofReal_le_ofReal`. It would shorten `BV_LambdaLE_enorm`,
`BV_LambdaSharp_enorm`, `BV_LambdaFlat_via_T`, and the compact and large cases
in `MainResults.lean`.

This helper belongs naturally in `BV/Maximal.lean` or a small generic ENNReal
utility module.

## 5. Common `ProofData` range consequences

The following facts are reproved in several files:

```lean
√x ≤ x
2 ≤ √x
```

They should be placed beside `one_le_log_x` and `sixteen_le_log_x` in
`BV/Defs.lean`.

The conductor-bound proofs also repeatedly derive

```lean
Q ≤ √x
Q ≤ x
```

from

```lean
Q ≤ √x / (Real.log x) ^ n.
```

A project-level helper using `one_le_log_x` could provide `Q ≤ √x`; combining
it with `√x ≤ x` gives the second conclusion. This would remove duplicate
denominator-positivity and `sqrt` algebra from `LambdaSharp.lean`,
`LambdaFlat.lean`, and `MainResults.lean`.

## 6. Monotonicity of the maximal operators

`BV/MaximalTest.lean` already contains the proof of the following result as an
example:

```lean
theorem maxy_mono
    (hfg : ∀ y, √x ≤ y → y ≤ x → f y ≤ g y) :
    maxy f ≤ maxy g
```

The analogous units-only result for `maxya` would also be straightforward:

```lean
theorem maxya_mono
    (hfg : ∀ y, √x ≤ y → y ≤ x →
      ∀ a : ZMod q, IsUnit a → f y a ≤ g y a) :
    maxya q f ≤ maxya q g
```

These would round out the complete-lattice API. They are lower priority because
there is not yet a second production use.

## Result not recommended for extraction

`BV/Dilate.lean` locally proves equalities between

```lean
Finset.Ioc 0 ⌊x⌋₊
```

and the custom real-endpoint interval `Nat.Icc 1 x`. These should not be exposed
as new compatibility lemmas: doing so would extend the API for the interval
that the refactor is trying to retire. Prefer converting the remaining internal
arguments to standard finsets when they are next touched.
