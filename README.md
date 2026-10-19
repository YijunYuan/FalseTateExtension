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
| 1. `K_{m,n}`, `K_FT`, `K_Kum`, `K_cyc` | `falseTateLayer`, `falseTateExtension`, `kummerExtension`, `cyclotomicExtension` (`Layers`) |
| 2. `K_FT`, `K_Kum`, `K_cyc` are strictly APF | `isStrictlyAPF_falseTateExtension_of_finiteDimensional` (`StrictAPF`), `isStrictlyAPF_kummerExtension` (`KummerProfile`), `isStrictlyAPF_cyclotomicExtension` (`Padic.CyclotomicAPF`) |
| 3. Liu, Lemma 5.1.2 (`p ≥ 3`): `K_Kum ∩ K_cyc = K`, `Gal(K_FT/K_cyc) ≅ ℤ_p`, `Gal(K_FT/K) ≅ ℤ_p ⋊ Gal(K_cyc/K)` | `kummerExtension_inf_cyclotomicExtension`, `cyclotomicRelativeGaloisEquiv`, `falseTateGaloisEquiv` (`GaloisStructure`) |
| 4. The topological generator `τ` of `Gal(K_FT/K_cyc)` with `τ(π^{1/p^m}) = ζ_{p^m} π^{1/p^m}` | `tau`, `tau_extensionRadical`, `denseRange_tau_zpow` (`GaloisStructure`) |
| 5. `K = ℚ_p`: `K_FT/ℚ_p` is totally ramified | `falseTateExtension_residueDegree_padic`, `finiteSubextension_falseTate_ramificationIdx_padic` (`Padic.FiniteGaloisStructure`) |
| 6. Viviani, Corollary 6.10 (ramification filtration of `ℚ_p(π^{1/p^n}, ζ_{p^n})`, with the correction of FalseTateLift, Remark 5.2) | `Padic.Viviani` (upper groups `finiteUpperAffine_*`, Herbrand table `inverseHerbrandFunction_falseTate_*`, lower groups `lowerRamificationGroupReal_falseTate_*`) |

The declaration names in this table are those of the current code; they change during the
refactoring described in `docs/REFACTOR_PLAN.md` and the table is updated at its end.

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
