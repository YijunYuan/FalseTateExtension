# FalseTateExtension — notes for agents and contributors

Lean 4 (`leanprover/lean4:v4.35.0`, module system) + Mathlib formalization of the false Tate curve
extension `K_FT = K(π^{1/p^∞}, ζ_{p^∞})` of a finite extension `K/ℚ_p`: its finite layers, the Kummer
and cyclotomic subextensions, strict APF (via the `FontaineWintenberger` dependency), Liu's Lemma
5.1.2 on `Gal(K_FT/K)`, the generator `τ` of `Gal(K_FT/K_cyc)`, total ramification over `ℚ_p`, and
Viviani's Corollary 6.10. The six targets and the declarations proving them are listed in `README.md`.
Design decisions and their rationale are in `docs/REFACTOR_PLAN.md`.

Code and docstrings are in English.

## Build

```sh
lake exe cache get      # Mathlib oleans
lake build              # everything
python3 scripts/check_layers.py   # reachability from the root module and layer order (CI)
```

**Performance red line: a single file must compile in under 30 s.** Build only the touched module
with `timeout 120 lake build <Module>`; a timeout means the design is wrong (usually an instance
being rebuilt by `letI`, or a `rfl` that unfolds a large definition), not that you should wait.
Timings of the last full build are in `docs/BUILD_TIMES.md`.

No `sorry`, no `set_option maxHeartbeats`, no warnings (the lakefile enables Mathlib's standard
linter set).

## Standing hypotheses and notation

```lean
open scoped NormedField Valued NNReal FontaineWintenberger
variable (p : ℕ) [Fact p.Prime]
variable {K : Type*} [Field K] [CharZero K] (π : K) [NeZero π]          -- general layer
variable {K : Type*} [NontriviallyNormedField K] [IsCompleteDiscreteValuedField K]
  [Algebra ℚ_[p] K] [FiniteDimensional ℚ_[p] K]
  (π : 𝒪[K]) [Fact (Irreducible π)]                                       -- p-adic layer
variable [Fact (p ≠ 2)]                                                   -- odd prime results
```

- `p` is an explicit parameter throughout (never `residueChar K`); `Padic/Basic.lean` provides
  `residueChar ℚ_[p] = p` for the boundary with FontaineWintenberger.
- Write `ℚ_[p]`, `ℤ_[p]` (Mathlib notation), never `Padic p`, `PadicInt p`.
- Write `𝒪[K]`, `𝓀[K]` (scoped notation of `FontaineWintenberger`) for the integer ring and
  residue field of the base field; never spell out `(NormedField.valuation (K := K)).valuationSubring`
  and never introduce file-local abbreviations (`OK`, `R`, `O`, `A`, …) for it.
- Hypotheses `π ≠ 0`, `Irreducible π`, `p ≠ 2` are instance arguments (`NeZero`, `Fact`), not
  explicit proof arguments; definitions never take proofs as value arguments.
- `IsGalois K K_FT`, `IsAPF K K_FT`, `IsStrictlyAPF K K_FT` (and for `K_Kum`, `K_cyc`) are instances.
  Never install them, or any other instance, with `letI`/`haveI` inside a theorem statement.
- The Galois group of `K_FT/K` is `FalseTateGaloisGroup p π`; the diagonal layer
  `K(π^{1/p^n}, ζ_{p^n})` is `falseTateDiagonalLayer p π n`; the generator is `kummerGenerator p π`
  with scoped notation `τ`.

## `local notation`

- Never write a literal successor `(n + 1)` inside a `local notation`: the `1` elaborates to a
  postponed `OfNat` metavariable, instance queries on towers built from the notation miss the
  cache, and files slow down by an order of magnitude. Write `(n + (1 : ℕ))`.

- Only inside a `section`, only for proof bodies: a public statement must not contain a
  `local notation`. (Scoped/global notations for named definitions — `τ`, `𝒪[K]`, `ℚ_[p]` — are
  display forms and are fine anywhere.)
- Never redefine a notation inside one file; the same object has the same name across files.
- A term appearing in two or more public statements is a `def`/`abbrev`, not a notation.

## Layout and layering

```
<Lib>/
  Mathlib/        upstream candidates: Mathlib names and namespaces, zero project imports
  Padic/          ℚ_[p] instances for FontaineWintenberger, 𝒪[ℚ_[p]] ≃ ℤ_[p]
  Affine/         the affine group A ⋊ H and its closed subgroups; no field theory
  Layers/         pPowRoot, zeta, the finite layers and infinite extensions
  Coordinates/    cyclotomic character and Kummer exponent; the closed affine embedding
  Cyclotomic/     ℚ_p(ζ_{p^∞}): ramification, character, filtration, strict APF
  Kummer/         K(π^{1/p^∞}): Eisenstein layers, APF profile, strict APF
  FalseTate/      K_FT: Liu 5.1.2, τ, strict APF, total ramification, Viviani
<Lib>.lean        imports one aggregate file per layer; its docstring names the target declarations
```

A layer imports only layers above it (`Mathlib < Padic, Affine < Layers < Coordinates <
Cyclotomic, Kummer < FalseTate`); `scripts/check_layers.py` enforces this and that every file is
imported by its layer's aggregate. 

## Naming

Mathlib conventions: `lowerCamelCase` for defs, `snake_case` for theorems, `UpperCamelCase` for
types, `IsFoo` for Prop classes, anonymous instances. The conclusion goes into the name
(`…_eq_one`, `…_ne_zero`). One name per object: `pPowRoot`/`pPowRootLayer`/`pPowRootExt` and
`zeta`/`zetaLayer`/`zetaExt` for the same root in different fields. No filler words ("actual",
"original", "genuine", "canonical", "ordinary", "literal", "intrinsic", "prescribed") in
identifiers, docstrings or section names.

Module docstrings follow the Mathlib template (`#` title, a mathematical statement, `## Main
results`, `## References` citing Liu §5.1 / Lemma 5.1.2, Viviani Cor. 6.10, Serre IV §n,
Wintenberger §n.m.k). Docstrings state the mathematics, not the proof strategy or the Lean encoding.

## Working style

Discuss design changes before executing them; record decisions in `docs/REFACTOR_PLAN.md`.
Dead code is deleted (git history keeps it), not archived. Results that are needed only by
`FalseTateNonliftability` live there, not here.
