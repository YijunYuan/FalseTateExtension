# Mathlib reuse

What the library takes from Mathlib instead of proving itself, and what it still proves that
Mathlib lacks (the `Mathlib/` directory, upstream candidates). Decisions A5.1–A5.2 of
`REFACTOR_PLAN.md`.

## Used from Mathlib (formerly reproved here)

| Mathlib declaration | replaced |
|---|---|
| `IsCyclotomicExtension.autEquivPow`, `IsPrimitiveRoot.autToPow_eq_modularCyclotomicCharacter` | the cardinality proof that `Gal(ℚ_p(ζ_{p^n})/ℚ_p) ≅ (ZMod (p^n))ˣ` (`cyclotomicLayerGaloisEquivUnits` and four lemmas) |
| `ZMod.card_units_eq_totient` | `card_cyclotomicLayer_character_units` |
| `IsPrimitiveRoot.minpoly_eq_cyclotomic_of_irreducible` | `Padic.minpoly_primitive_root` |
| `IsCyclotomicExtension.finrank` | `Padic.finrank_adjoin_primitive_root` |
| `AlgEquiv.restrictNormalHom`, packaged once as `IntermediateField.restrictNormalHomOfLE` | 25 copies of `RingHom.toAlgebra (Subsemiring.inclusion _)` + `IsScalarTower.of_algebraMap_eq` |
| `Polynomial.cyclotomic_prime_pow_comp_X_add_one_isEisensteinAt` (over `ℤ`) | the Eisenstein criterion is transported to `ℤ_[p]`, not reproved |
| `IsPrimitiveRoot.norm_pow_sub_one_eq_prime_pow_of_ne_zero` | the norm of `ζ - 1` |

## Upstream candidates (`FalseTateExtension/Mathlib/`)

Zero project imports, Mathlib namespaces. Checked absent from the pinned Mathlib.

| file | content |
|---|---|
| `FieldTheory/RestrictNormal` | `IntermediateField.restrictNormalHomOfLE` and its `_commutes`, `_surjective`, `_comp`, `_refl` |
| `FieldTheory/IntermediateField/Supremum` | `IntermediateField.mem_iSup_of_directed`, `_of_monotone` |
| `FieldTheory/Galois/RestrictScalars` | range and index of `AlgEquiv.restrictScalarsHom` |
| `FieldTheory/Galois/InfiniteCorrespondence` | infinite Galois correspondence lemmas, continuity of `restrictScalarsHom`, `fixingSubgroupContinuousMulEquiv` |
| `NumberTheory/Padics/ClosedAddSubgroup` | closed additive subgroups of `ℤ_[p]` are `⊥` or `(p^s)`; relative indices under scalar multiplication |
| `NumberTheory/Padics/Cyclotomic` | `Φ_{p^n}(X+1)` is Eisenstein over `ℤ_[p]`; `cyclotomic (p^n) ℚ_[p]` is irreducible |
| `NumberTheory/Cyclotomic/CharacterNaturality` | `cyclotomicCharacter` commutes with intertwining embeddings |
| `RingTheory/Polynomial/EisensteinUniformizer` | `X^m - C π` is Eisenstein and irreducible for a uniformizer `π` of a DVR |
| `RingTheory/PowerBasis/Eigenvector` | eigenvectors of an automorphism in a power basis |
| `Data/ZMod/UnitsMap` | index and cardinality of `ker (ZMod.unitsMap)` between prime-power levels |

Generic lemmas that depend on FontaineWintenberger were moved there instead (its commit
`6c9e973`): closed-subgroup suprema in compact groups, `irreducible_of_valuation_eq_exp_neg_one`,
Herbrand interval lemmas, APF subgroups of unions and of subextensions, finite-residue inertia
lemmas, and the APF index of a totally ramified extension.
