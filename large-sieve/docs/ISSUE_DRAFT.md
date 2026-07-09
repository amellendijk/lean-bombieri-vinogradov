# Formalized proof of the multiplicative large sieve (for primitive characters)

## Summary

We have a **fully sorry-free** Lean 4 formalization of the multiplicative large sieve inequality for primitive Dirichlet characters:

```
∑_{q ≤ Q} ∑*_{χ primitive mod q} (q/φ(q)) · ‖∑ cₙ χ(n)‖² ≤ (8π² + 2) · (N + Q²) · ∑ ‖cₙ‖²
```

The Lean statement:

```lean
theorem multiplicative_large_sieve_gallagher
    (Q : ℝ) (hQ : 1 ≤ Q) (H : ℤ) (N : ℕ) (hN : 0 < N) (c : ℤ → ℂ)
    (S : (q : ℕ) → Finset (DirichletCharacter ℂ q))
    (hS : ∀ q, ∀ χ ∈ S q, DirichletCharacter.IsPrimitive χ) :
    ∑ q ∈ Finset.Ioc 0 ⌊Q⌋₊,
      ∑ χ ∈ S q,
        (q : ℝ) / (Nat.totient q : ℝ) *
          ‖∑ n ∈ Finset.Ioc H (H + ↑N), c n * (χ n : ℂ)‖ ^ 2 ≤
    (8 * Real.pi ^ 2 + 2) * ((↑N : ℝ) + Q ^ 2) *
      ∑ n ∈ Finset.Ioc H (H + ↑N), ‖c n‖ ^ 2
```

`#print axioms multiplicative_large_sieve_gallagher` outputs only `[propext, Classical.choice, Quot.sound]` — no `sorryAx`.

---

## Compatibility verification

We cloned this repo and verified against your environment:

- **Type-check passes:** A corrected axiom statement with the primitive-character restriction compiles cleanly in your Lean v4.28.0 + Mathlib (only needed `open Classical` for `DecidablePred`).
- **Usage is already correct:** Your actual consumers (`LargeSieve_convolution` in `LambdaFlat.lean`, `summatory_T_ll` in `Flat/Perron.lean`) already filter `with χ.IsPrimitive` — so they're compatible with the corrected axiom.
- **Only the axiom statement needs changing:** The literal axiom in `BV/Axioms.lean` (line 36) sums over all `DirichletCharacter ℚ q`, but everywhere it's applied, primitive filtering is already in place.

---

## Issue with the current axiom statement

Your axiom (line 36-38 of `BV/Axioms.lean`):

```lean
axiom large_sieve (Q : ℝ) (hQ : 1 ≤ Q) (H : ℤ) (N : ℕ) (hN : 0 < N) (c : ℤ → ℂ) :
  ∑ q ∈ Finset.Ioc 0 ⌊Q⌋₊, ∑ χ : DirichletCharacter ℚ q,
    q / φ q * ‖∑ n ∈ Finset.Ioc H (H+N), c n * χ n‖^2 ≤
    C_LS * (N+Q^2) * ∑ n ∈ Finset.Ioc H (H+N), ‖c n‖^2
```

The blueprint annotation correctly says `\sumstar_{\chi \pmod q}` (primitive characters), but the Lean sum `∑ χ : DirichletCharacter ℚ q` ranges over ALL characters mod q. This is mathematically false for any finite constant — the principal character contributes ~N² to the LHS when c ≡ 1.

**Suggested fix:**

```lean
axiom large_sieve (Q : ℝ) (hQ : 1 ≤ Q) (H : ℤ) (N : ℕ) (hN : 0 < N) (c : ℤ → ℂ) :
  ∑ q ∈ Finset.Ioc 0 ⌊Q⌋₊,
    ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).filter (·.IsPrimitive),
      q / φ q * ‖∑ n ∈ Finset.Ioc H (H+N), c n * χ n‖^2 ≤
    C_LS * (N+Q^2) * ∑ n ∈ Finset.Ioc H (H+N), ‖c n‖^2
```

This matches your blueprint's `∑*` and is what your downstream code (`LargeSieve_convolution`, `summatory_T_ll`) already expects.

---

## What we provide

### Option A: Replace the axiom entirely (recommended)

We can provide a sorry-free proof that discharges the corrected axiom with `C_LS = 8π² + 2`. This eliminates the axiom entirely — your BV proof would rest on Siegel-Walfisz alone.

### Option B: Provide as standalone infrastructure

The proof spans ~2100 lines across 4 files. Key components that may be useful independently:

| Component | Lines | What it proves |
|-----------|-------|---------------|
| Gallagher's additive large sieve | 567 | `∑_r ‖S(αᵣ)‖² ≤ (8π²+2)·(N+δ⁻¹)·∑‖a‖²` via Sobolev inequality |
| Farey spacing | 120 | `|a/q - a'/q'| ≥ 1/Q²` for distinct reduced fractions with q,q'≤Q |
| Character→exponential reduction | 529 | Plancherel + Gauss sum norm + reduction to exp sums, all moduli |
| Bridge/assembly | 322 | Combines the above into the multiplicative large sieve |

---

## Technical details

| Aspect | Our proof | Your repo |
|--------|-----------|-----------|
| Lean version | v4.32.0-rc1 | v4.28.0 |
| Character type | `DirichletCharacter ℂ q` | `DirichletCharacter ℚ q` (axiom) / `ℂ` (usage) |
| Constant | Explicit `8π²+2` | Abstract `C_LS` |
| Axioms used | propext, choice, Quot.sound | — |

The Lean version gap (v4.28 → v4.32) means direct file inclusion requires some API adaptation. The character type difference (`ℚ` vs `ℂ`) is also easy to reconcile — your downstream code already uses `DirichletCharacter ℂ q`.

### Proof strategy (Gallagher 1967, no Beurling-Selberg)

```
1. Sobolev/FTC bound: ‖T(x₀)‖² ≤ ∫ (‖T‖² + η‖T'‖²) over δ-neighborhood
2. AM-GM: 2‖T‖·‖T'‖ ≤ η‖T‖² + η⁻¹‖T'‖²
3. Sum over δ-separated points → disjoint intervals (periodicity)
4. Parseval for T and T' → coefficient norms
5. Optimize η = N → constant 8π²+2
```

This avoids Beurling-Selberg extremal functions entirely, at the cost of a non-sharp constant (81 vs 1). For BV this is fine — the constant only affects the implied constant in the O-term.

---

## Proof architecture

```
multiplicative_large_sieve_gallagher [LargeSieve/Multiplicative.lean]
  ├── character_sum_le_exp_sum_primitive [LargeSieve/Character/Reduction.lean]
  │     ├── gauss_sum_norm_sq_primitive:  |τ(χ)|² = q  (primitive χ, general modulus)
  │     ├── char_sum_bound_primitive:     Plancherel + Gauss sum reduction
  │     └── plancherel_dirichlet:         ∑_χ |∑ χ(a⁻¹)f(a)|² = φ(q)·∑|f|²
  └── farey_collection_bound_gallagher [LargeSieve/Multiplicative.lean]
        ├── gallagher_large_sieve [LargeSieve/Additive/Gallagher.lean]
        │     ├── gallagher_pointwise (Sobolev/FTC bound)
        │     ├── gallagher_sum_bound (sum over separated points)
        │     └── Parseval for T and T'
        └── farey_spacing_Q [LargeSieve/Farey.lean]
              └── |a/q - a'/q'| ≥ 1/Q² for distinct reduced fractions
```

---

## Standalone repository

See the `large-sieve/` directory (standalone Lake package).

Build: `cd large-sieve && lake exe cache get && lake build`

Verify axioms: `#print axioms multiplicative_large_sieve_gallagher` → `[propext, Classical.choice, Quot.sound]`
