# Lean Bombieri-Vinogradov — Claude Documentation

## Purpose of This Branch (`asymp-notation`)

This branch is an **experiment with the new big-O notation** from the draft Mathlib PR
[mathlib4#39450](https://github.com/leanprover-community/mathlib4/pull/39450), ported into
`BV/Mathlib/Tactic/Asymptotics/` (import via `BV.Mathlib.Tactic.Asymptotics.Basic`). The
notation provides `asymp% x : α in l => lhs = rhs` statements where the right-hand side may
contain `O(f x)` / `O[l](f x)` terms, backed by `Asymptotics.bigO` sets, `Asymptotics.map`,
and the `AsympRel` relation.

**Goal:** transition as much of this project as possible to the new notation. The notation is
very new and we *expect* to run into issues along the way. The point of the experiment is to
learn:

1. how the notation itself can be improved (elaboration, delaboration, binder names,
   metavariable issues, filter handling, …), and
2. what tactics/lemmas are needed to manipulate these expressions efficiently and clearly
   (currently: `magic_tac`, `push`/`pull`, `grw`/`gcongr` with `AsympRel`/`RightSerial`
   congruence lemmas — see the `terry` example in `BV/Mathlib/Tactic/Asymptotics/Basic.lean`
   for the current workflow and its pain points).

When you hit friction — a statement that can't be expressed, a rewrite that should be one step
but takes five, a delaborator glitch, a missing congruence lemma — **record it** in
`notes/AsympNotationFindings.md` (create it if absent), ideally with a minimal example. These
findings are the primary deliverable of the branch, alongside the converted proofs.

Do not change the pinned mathlib version; the ported files compile against it as-is.

---

## Project Goal

Formalize the **Bombieri-Vinogradov theorem** in Lean 4 / Mathlib, modulo two axioms:
- **Siegel-Walfisz** (`BV/Axioms.lean`)
- **Large sieve inequality** (`BV/Axioms.lean`)

The main theorem (`bombieri_vinogradov` in `BV/MainResults.lean`) states that for fixed $A \ge 0$,
$$\sum_{q \le Q} \max_{y \le x} \max_{a \in (\mathbb{Z}/q\mathbb{Z})^*} \left| \psi(y;q,a) - \frac{y}{\varphi(q)} \right| \ll_A \frac{x}{(\log x)^A}$$
uniformly for $x \ge 2$, $1 \le Q \le \sqrt{x}/(\log x)^{A+3}$.

The proof blueprint is in `notes/Blueprint.md` (follows Koukoulopoulos *The Distribution of Prime Numbers*).

---

## Toolchain & Dependencies

- Lean: `leanprover/lean4:v4.29.0-rc6` (see `lean-toolchain`)
- Dependencies (`lakefile.toml`): `mathlib`, `LeanArchitect`, `checkdecls`, `doc-gen4`

The `LeanArchitect` package provides the `@[blueprint ...]` attribute used throughout to link Lean declarations to the mathematical blueprint.

---

## File Structure

```
BV/
  Defs.lean        — Core definitions: Delta, Lambda decomposition, ψ, summatory, ProofData
  Axioms.lean      — Axiomatic inputs: siegel_walfisz, large_sieve
  MainResults.lean — Top-level theorems: bombieri_vinogradov, BV_Delta_Lambda, BV_Delta_1P
  LambdaSharp.lean — Type I sums (Λ♯ = μ_{≤V} * log − (Λ_{≤U} * μ_{≤V}) * 1)
  LambdaFlat.lean  — Type II sums (Λ♭ = (Λ_{>U} * 1) * μ_{>V})
  LambdaLE.lean    — Small von Mangoldt (Λ_{≤U} = 1_{≤U} · Λ)
BV.lean            — Root import (imports BV.MainResults)
Main.lean          — Entry point
notes/Blueprint.md — Mathematical proof sketch with LaTeX
```

---

## Key Mathematical Objects in Lean

| Math symbol | Lean name | File |
|---|---|---|
| $\Lambda$ (von Mangoldt) | `Λ` (from `ArithmeticFunction`, opened at top of each file) | Mathlib |
| $\Lambda^\sharp$ | `LambdaSharp`, notation `Λ♯` | `BV/Defs.lean` |
| $\Lambda^\flat$ | `LambdaFlat`, notation `Λ♭` | `BV/Defs.lean` |
| $\Lambda_{\le U}$ | `LambdaLE U`, notation `Λ≤[U]` | `BV/Defs.lean` |
| $\Delta_f(x;q,a)$ | `Delta f x q a`, notation `Δ_[f](x; q, a)` | `BV/Defs.lean` |
| $\psi(x;q,a)$ | `ψ x a` (q implicit via `ZMod q`) | `BV/Defs.lean` |
| $\sum_{n \le x} f(n)$ | `summatory f x` | `BV/Defs.lean` |
| $\{1,\ldots,N\} \cap \mathbb{N}$ as `Finset ℕ` | `Nat.Icc x y` | `BV/Defs.lean` |
| $\varphi(q)$ (Euler totient) | `φ q` or `Nat.totient q` | Mathlib |
| $n \equiv a \pmod{q}$ | `n ∈ Nat.modEqs a` | `BV/Defs.lean` |
| $f_r$ (f restricted to coprimes to r) | `onCoprime r f` | `BV/Defs.lean` |
| Parameters $U, V, x, y$ | `ProofData` typeclass fields | `BV/Defs.lean` |

The `ProofData` typeclass bundles all proof parameters with their hypotheses:
- `U, V, x, y : ℝ`
- `le_x : 2 ≤ x`, `sqrt_x_le_y : √x ≤ y`, `y_le_x : y ≤ x`
- `UV_le : U * V ≤ √x`, `le_U : exp(√x) ≤ U`, `le_V : exp(√x) ≤ V`

---

## Working with Lean via the LSP MCP Server

All Lean interaction should go through the `mcp__lean-lsp__*` tools. Never run `lake build` to check proofs — use the LSP instead.

### Checking Proof State

```
lean_goal(file_path, line, column?)
```
- Returns the proof state (goals) at a cursor position.
- Omit `column` to get the state at the start of the line (before tactics).
- `"no goals"` means the proof is complete.

```
lean_diagnostic_messages(file_path, start_line?, end_line?, severity?)
```
- Returns errors/warnings/infos for a file or range.
- Use `severity: "error"` to filter to just errors.
- Use `declaration_name` to check a specific theorem (slow but precise).

### Exploring Types and Signatures

```
lean_hover_info(file_path, line, column)
```
- Returns the type signature and docstring of the identifier at `(line, column)`.
- Column must be at the **start** of the identifier.

```
lean_term_goal(file_path, line, column)
```
- Returns the expected type at a term position (useful inside `show`, `exact`, etc.).

### Finding Lemmas

**Decision tree:**
1. Know a name → `lean_local_search(query)` to verify it exists
2. Need a lemma about concept X → `lean_leansearch("natural language query")`
3. Need a lemma with a specific type pattern → `lean_loogle("type pattern")`
4. What closes this goal? → `lean_state_search(goal)`
5. What to feed to `simp`? → `lean_hammer_premise(goal)`

```
lean_local_search(query, limit?)
```
- Fast prefix/name search across project + Mathlib.
- Use before guessing lemma names.

```
lean_leansearch(query)   # rate-limited: 3/30s
lean_loogle(query)       # rate-limited: 3/30s
lean_leanfinder(query)   # rate-limited: 10/30s
lean_state_search(goal)  # rate-limited: 3/30s
lean_hammer_premise(goal) # rate-limited: 3/30s
```

### Testing Tactics Without Editing

```
lean_multi_attempt(file_path, line, tactics, column?)
```
- Tests a list of tactics at a proof position **without editing the file**.
- Omit `column` for fast line-based REPL mode: `["simp", "ring", "omega"]`
- Provide `column` for exact source position testing.

Example workflow: before editing a `sorry`, try `lean_multi_attempt` with candidate tactics.

### Getting Declaration Source

```
lean_declaration_file(name)
```
- Returns the full source of a declaration. Use sparingly (large output).

```
lean_file_outline(file_path, max_declarations?)
```
- Returns imports + all declarations with type signatures. Token-efficient skeleton view.

### Autocomplete

```
lean_completions(file_path, line, column)
```
- IDE-style autocomplete. Useful when partially writing a lemma name.

### Building (Last Resort)

```
lean_build()
```
- Full rebuild + LSP restart. Very slow. Only use when:
  - Adding new imports that aren't recognized
  - LSP seems stale/broken

---

## Proof Workflow

Most theorems currently have `sorry` bodies with `@[blueprint ...]` annotations. The typical workflow for filling in a proof:

1. **Read the blueprint** (`notes/Blueprint.md`) for the mathematical argument.
2. **Check the current state** with `lean_goal` or `lean_diagnostic_messages`.
3. **Find relevant Mathlib lemmas** with `lean_leansearch` / `lean_loogle` / `lean_local_search`.
4. **Test tactics** with `lean_multi_attempt` before editing.
5. **Edit** the file to replace `sorry` with the proof.
6. **Verify** with `lean_diagnostic_messages` (check for no errors).

### Common Patterns

**Checking if a file is clean:**
```
lean_diagnostic_messages(file_path, severity="error")
```

**Getting proof state mid-proof:**
```
lean_goal(file_path, line_after_tactic)
```

**Searching for an `ArithmeticFunction` lemma:**
```
lean_leansearch("von Mangoldt function convolution")
lean_loogle("ArithmeticFunction.vonMangoldt")
```

**Searching for totient lemmas:**
```
lean_local_search("Nat.totient")
lean_leansearch("Euler phi multiplicative")
```

---

## Notation Reference

These notations are used throughout (scoped in `open BV`):

| Notation | Meaning |
|---|---|
| `Λ♯` | `LambdaSharp` (type I, sharp part) |
| `Λ♭` | `LambdaFlat` (type II, flat part) |
| `Λ≤[U]` | `LambdaLE U` (small primes part) |
| `Δ_[f](x; q, a)` | `Delta f x q a` |
| `ψ x a` | Chebyshev ψ in AP |

The `BV` scope must be open for these notations to work: `open BV` or `open scoped BV`.

---

## Current Status

All main theorems are stubbed with `sorry`. The proof structure/skeleton is in place:

- `BV/Defs.lean` — definitions complete (or nearly so)
- `BV/Axioms.lean` — Siegel-Walfisz and large sieve as axioms
- `BV/MainResults.lean` — main theorem structure in place
- `BV/LambdaSharp.lean` — empty (needs type I sum bounds)
- `BV/LambdaFlat.lean` — early notes only (needs type II sum bounds)
- `BV/LambdaLE.lean` — early notes only (needs Λ_{≤U} bounds)
