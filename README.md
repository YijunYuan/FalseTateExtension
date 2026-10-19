# FalseTateExtension

Lean 4 + Mathlib formalization of the false Tate curve extension. For a prime `p`, a finite
extension `K/ℚ_p` with uniformizer `π`, compatible systems `π^{1/p^m}` of `p`-power roots of `π`
and `ζ_{p^n}` of primitive `p`-power roots of unity, let

```
K_{m,n} = K(π^{1/p^m}, ζ_{p^n}),   K_FT = ⋃ K_{m,n},   K_Kum = K(π^{1/p^∞}),   K_cyc = K(ζ_{p^∞}).
```

The library builds on [FontaineWintenberger](https://github.com/YijunYuan/FontaineWintenberger)
(arithmetically profinite extensions, ramification theory, the field of norms).

## The six targets

| Target | Declaration (module) |
|---|---|
| 1. `K_{m,n}`, `K_FT`, `K_Kum`, `K_cyc` | `falseTateLayer`, `falseTateExtension`, `kummerExtension`, `cyclotomicExtension` (`Layers/Basic`) |
| 2. `K_FT`, `K_Kum`, `K_cyc` are strictly APF | instances `isStrictlyAPF_falseTateExtension_of_finiteDimensional` (`FalseTate/StrictAPF`), `isStrictlyAPF_kummerExtension` (`Kummer/APF`), `isStrictlyAPF_cyclotomicExtension` (`Cyclotomic/APF`) |
| 3. Liu, Lemma 5.1.2 (`p ≥ 3`): `K_Kum ∩ K_cyc = K`, `Gal(K_FT/K_cyc) ≅ ℤ_p`, `Gal(K_FT/K) ≅ ℤ_p ⋊ Gal(K_cyc/K)` | `kummerExtension_inf_cyclotomicExtension`, `falseTateGaloisEquivSemidirectProduct` (`FalseTate/TranslationKernel`); `cyclotomicRelativeGaloisEquiv` (`FalseTate/LiuLemma`) |
| 4. The topological generator `τ` of `Gal(K_FT/K_cyc)`, `τ(π^{1/p^m}) = ζ_{p^m} π^{1/p^m}` | `kummerGenerator` (notation `τ`), `kummerGenerator_pPowRootExt`, `denseRange_kummerGenerator_zpow` (`FalseTate/TranslationKernel`) |
| 5. `K = ℚ_p`: `K_FT/ℚ_p` is totally ramified | `finiteSubextension_falseTate_residueDegree_padic`, `finiteSubextension_falseTate_ramificationIdx_padic`, `falseTateExtension_residueDegree_padic` (`FalseTate/TotalRamification`) |
| 6. Viviani, Corollary 6.10 (corrected as in FalseTateLift, Remark 5.2) | `FalseTate/Viviani/Filtration` for a uniformizer `π`; `FalseTate/Viviani/Corollary` for an integer `a` with `v_p(a) = 1` (`finiteUpperAffine_integerParameter_interval`, `inverseHerbrandFunction_integerParameter_*`, `lowerRamificationGroupReal_integerParameter_*`) |

## Layout

```
<Lib>/
  Mathlib/        upstream candidates (Mathlib names, no project imports)
  Padic/          ℚ_[p] as a local field; scalar indices on closed subgroups of ℤ_[p]
  Affine/         the affine group A ⋊ H and its closed subgroups
  Layers/         compatible roots, finite layers, infinite extensions
  Coordinates/    cyclotomic character, Kummer exponent, the closed affine embedding
  Cyclotomic/     ℚ_p(ζ_{p^∞}) and K(ζ_{p^∞}): ramification, character, filtration, strict APF
  Kummer/         K(π^{1/p^∞}): Eisenstein layers, APF profile, strict APF
  FalseTate/      K_FT: Liu's lemma, τ, strict APF, total ramification, Viviani's filtration
<Lib>.lean        imports one aggregate per layer
```

A layer imports only layers above it; `scripts/check_layers.py` (run in CI) checks this and
that every file is imported by its layer's aggregate.

## Build

Install [elan](https://github.com/leanprover/elan), then run from this directory:

```sh
lake exe cache get
lake build
```

Lean is pinned to `leanprover/lean4:v4.35.0`; Mathlib and FontaineWintenberger commits are
recorded in `lakefile.toml` and `lake-manifest.json`. The library contains no `sorry` and builds
without warnings under Mathlib's standard linter set.

See `CLAUDE.md` for conventions and standing hypotheses, `docs/REFACTOR_PLAN.md` for the design,
`docs/BUILD_TIMES.md` for per-module compile times.

## References

* T. Liu, *On lattices in semi-stable representations: a proof of a conjecture of Breuil*, §5.1.
* F. Viviani, *Ramification groups and Artin conductors of radical extensions of ℚ*, Cor. 6.10.
* J.-P. Serre, *Local Fields*, Chapter IV.
* J.-P. Wintenberger, *Le corps des normes de certaines extensions infinies de corps locaux;
  applications*, Ann. Sci. ENS 16 (1983).

The papers are not distributed with this repository.

## License

Apache 2.0, see `LICENSE`.
