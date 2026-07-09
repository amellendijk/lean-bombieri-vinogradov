# Large Sieve (multiplicative, for primitive Dirichlet characters)

A **sorry-free** Lean 4 / Mathlib formalization of the multiplicative large sieve
inequality for primitive Dirichlet characters:

```
∑_{q ≤ Q} ∑*_{χ mod q} (q/φ(q)) · ‖∑_{H < n ≤ H+N} cₙ χ(n)‖²
      ≤ (8π² + 2) · (N + Q²) · ∑_{H < n ≤ H+N} ‖cₙ‖²
```

where `∑*` ranges over any family of **primitive** characters mod `q`.

The top-level result is `multiplicative_large_sieve_gallagher` in
[`LargeSieve/Multiplicative.lean`](LargeSieve/Multiplicative.lean). It depends
only on the standard axioms `propext`, `Classical.choice`, `Quot.sound`
(verified with `#print axioms`) — no `sorry`.

## Why primitive characters

The unrestricted statement (summing over *all* characters mod `q`, including the
principal character) is **false**: the principal character contributes ~N²/2 to
the left-hand side, which breaks the bound for large `Q`. The classical
multiplicative large sieve — and the downstream Bombieri–Vinogradov machinery —
restricts to primitive characters (the `∑*` of the literature). This is why the
`hS : ∀ q, ∀ χ ∈ S q, χ.IsPrimitive` hypothesis is required.

## The constant

The constant `8π² + 2 ≈ 81` comes from **Gallagher's 1967** proof of the additive
large sieve (a Sobolev/FTC argument), which avoids the Beurling–Selberg extremal
functions needed for the sharp constant `N − 1 + δ⁻¹`. For Bombieri–Vinogradov
the value of the constant is irrelevant — it only affects the implied constant in
the error term — so the non-sharp Gallagher constant is sufficient.

## Structure

```
LargeSieve.lean                     root import (→ Multiplicative)
LargeSieve/
  Additive/
    ExpSum.lean       exponential sums e(x), Farey distance, Gram machinery,
                      geometric-sum bounds, Bombieri's N·δ⁻¹ sieve (sorry-free)
    Gallagher.lean    Gallagher's additive large sieve via Sobolev/FTC
  Farey.lean          Farey spacing (|a/q − a'/q'| ≥ 1/Q²) + finite-group
                      Plancherel for Dirichlet characters
  Character/
    SumHelper.lean    unit-sum / weighted-sum helpers
    PrimeCase.lean    character→exponential reduction for prime moduli
    Reduction.lean    character→exponential reduction for general moduli
                      (primitive), via the primitive Gauss-sum norm |τ(χ)|² = q
  Multiplicative.lean the final multiplicative large sieve (Gallagher route)
docs/
  PROGRESS.md         development log
```

## Proof chain

```
multiplicative_large_sieve_gallagher            (Multiplicative.lean)
  ← character_sum_le_exp_sum_primitive          (Character/Reduction.lean)
      ← gauss_sum_norm_sq_primitive             (Character/Reduction.lean)
      ← plancherel_dirichlet                    (Farey.lean)
  ← farey_collection_bound_gallagher            (Multiplicative.lean)
      ← gallagher_large_sieve                   (Additive/Gallagher.lean)
      ← farey_spacing_Q                         (Farey.lean)
```

## Building

Uses Lean `v4.28.0` + Mathlib `v4.28.0` (see `lean-toolchain`), matching the
toolchain pinned by the surrounding Bombieri–Vinogradov project. This is a
standalone Lake package:

```bash
cd large-sieve-v4.28
lake exe cache get
lake build
```

A `v4.32.0-rc1` version of the same proof lives in the sibling `large-sieve/`
directory; the two are identical modulo Mathlib API renames.

## Relation to `BV/Axioms.lean`

Upstream `BV/Axioms.lean` currently states `large_sieve` as an axiom summing over
`DirichletCharacter ℚ q` for **all** characters. As noted above that form is not
provable; the primitive-restricted statement proved here matches the actual
downstream usage (`LambdaFlat.lean`, `Flat/Perron.lean` already filter on
`χ.IsPrimitive`).
