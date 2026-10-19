# Build times

Per-module wall-clock times of a clean `lake build` of this library only (dependencies cached),
20-core machine. Appended at the end of every refactor phase (see `REFACTOR_PLAN.md` §F).
Targets: every file under 30 s, whole library under 4 min, no `set_option maxHeartbeats`.

## Baseline (2026-10-19, commit 57f549b, before refactoring)

Total: 6 min 44 s wall, 1115 s CPU, 35 modules. `set_option maxHeartbeats`: 16, `synthInstance.maxHeartbeats`: 12.

| module | seconds |
|---|---|
| FalseTateExtension.KummerProfile | 120.0 |
| FalseTateExtension.Padic.Viviani | 85.0 |
| FalseTateExtension.Padic.CyclotomicUpper | 67.0 |
| FalseTateExtension.Padic.NormFieldRamification | 47.0 |
| FalseTateExtension.PadicCoordinates | 46.0 |
| FalseTateExtension.CoordinateTransitions | 46.0 |
| FalseTateExtension.RadicalRamification | 41.0 |
| FalseTateExtension.Padic.FiniteGaloisStructure | 21.0 |
| FalseTateExtension.Padic.CyclotomicAPF | 20.0 |
| FalseTateExtension.Padic.CyclotomicInertia | 19.0 |
| FalseTateExtension.Padic.CyclotomicRamification | 17.0 |
| FalseTateExtension.Padic.CyclotomicResidueBound | 15.0 |
| FalseTateExtension.Padic.CyclotomicInertiaCompletion | 15.0 |
| FalseTateExtension.Padic.NormFieldCoordinates | 13.0 |
| FalseTateExtension.Padic.KummerRamification | 9.8 |
| FalseTateExtension.GaloisStructure | 9.4 |
| FalseTateExtension.CyclotomicImage | 8.8 |
| FalseTateExtension.StrictAPF | 7.3 |
| FalseTateExtension.Padic.NormFieldAction | 6.1 |
| FalseTateExtension.Padic.InfiniteCharacter | 4.7 |
| FalseTateExtension.AffineEmbedding | 4.3 |
| FalseTateExtension.AffineIndex | 3.8 |
| FalseTateExtension.AffineCommutator | 3.7 |
| FalseTateExtension.AffineKernel | 3.3 |
| FalseTateExtension.Padic.TameGenerator | 2.9 |
| FalseTateExtension.Padic.GeneralCharacter | 2.8 |
| FalseTateExtension.FiniteCoordinates | 2.8 |
| FalseTateExtension | 2.7 |
| FalseTateExtension.Padic.ClosedAddSubgroup | 2.6 |
| FalseTateExtension.Layers | 2.5 |
| FalseTateExtension.Padic.TameUnits | 2.4 |
| FalseTateExtension.Padic.FiniteCharacter | 2.1 |
| FalseTateExtension.GaloisLayers | 2.0 |
| FalseTateExtension.CompatibleRoots | 1.8 |
| FalseTateExtension.Padic.Cyclotomic | 1.7 |

## After F1 (performance quick wins)

Total: 6 min 14 s wall, 941 s CPU, 36 modules (new `Mathlib/FieldTheory/RestrictNormal`).
`CoordinateTransitions` 46 s → 2.6 s and `PadicCoordinates` 46 s → 2.3 s by defining the restriction maps
through `IntermediateField.restrictNormalHomOfLE` instead of the categorical `finGaloisGroupMap`.

| module | seconds |
|---|---|
| FalseTateExtension.KummerProfile | 107.0 |
| FalseTateExtension.Padic.Viviani | 78.0 |
| FalseTateExtension.Padic.CyclotomicUpper | 64.0 |
| FalseTateExtension.Padic.NormFieldRamification | 43.0 |
| FalseTateExtension.RadicalRamification | 39.0 |
| FalseTateExtension.Padic.FiniteGaloisStructure | 20.0 |
| FalseTateExtension.Padic.CyclotomicRamification | 18.0 |
| FalseTateExtension.Padic.CyclotomicInertia | 18.0 |
| FalseTateExtension.Padic.CyclotomicAPF | 17.0 |
| FalseTateExtension.Padic.CyclotomicResidueBound | 16.0 |
| FalseTateExtension.Padic.NormFieldCoordinates | 12.0 |
| FalseTateExtension.Padic.CyclotomicInertiaCompletion | 12.0 |
| FalseTateExtension.Padic.KummerRamification | 9.2 |
| FalseTateExtension.GaloisStructure | 8.7 |
| FalseTateExtension.CyclotomicImage | 8.6 |
| FalseTateExtension.Padic.InfiniteCharacter | 6.6 |
| FalseTateExtension.StrictAPF | 6.5 |
| FalseTateExtension.Padic.NormFieldAction | 5.5 |
| FalseTateExtension.AffineCommutator | 3.8 |
| FalseTateExtension.AffineIndex | 3.7 |
| FalseTateExtension.AffineKernel | 3.3 |
| FalseTateExtension.Padic.TameGenerator | 3.0 |
| FalseTateExtension.Padic.GeneralCharacter | 3.0 |
| FalseTateExtension.AffineEmbedding | 3.0 |
| FalseTateExtension.PadicCoordinates | 2.7 |
| FalseTateExtension.FiniteCoordinates | 2.5 |
| FalseTateExtension.Mathlib.FieldTheory.RestrictNormal | 2.3 |
| FalseTateExtension.Padic.TameUnits | 2.2 |
| FalseTateExtension.Padic.FiniteCharacter | 2.2 |
| FalseTateExtension.Layers | 1.9 |
| FalseTateExtension.GaloisLayers | 1.9 |
| FalseTateExtension.CoordinateTransitions | 1.9 |
| FalseTateExtension.CompatibleRoots | 1.9 |
| FalseTateExtension.Padic.Cyclotomic | 1.6 |
| FalseTateExtension | 1.3 |
| FalseTateExtension.Padic.ClosedAddSubgroup | 1.0 |

## After F2 (scope: NormField*, TameUnits, TameGenerator removed)

Total: 4 min 58 s wall, 769 s CPU, 30 modules.

| module | seconds |
|---|---|
| FalseTateExtension.KummerProfile | 107.0 |
| FalseTateExtension.Padic.Viviani | 78.0 |
| FalseTateExtension.Padic.CyclotomicUpper | 62.0 |
| FalseTateExtension.RadicalRamification | 36.0 |
| FalseTateExtension.Padic.FiniteGaloisStructure | 19.0 |
| FalseTateExtension.Padic.CyclotomicInertia | 18.0 |
| FalseTateExtension.Padic.CyclotomicAPF | 16.0 |
| FalseTateExtension.Padic.CyclotomicRamification | 15.0 |
| FalseTateExtension.Padic.CyclotomicResidueBound | 14.0 |
| FalseTateExtension.Padic.CyclotomicInertiaCompletion | 12.0 |
| FalseTateExtension.Padic.KummerRamification | 8.9 |
| FalseTateExtension.GaloisStructure | 8.6 |
| FalseTateExtension.StrictAPF | 6.5 |
| FalseTateExtension.Padic.InfiniteCharacter | 5.7 |
| FalseTateExtension.Padic.GeneralCharacter | 2.9 |
| FalseTateExtension.Padic.FiniteCharacter | 1.9 |
| FalseTateExtension.Padic.Cyclotomic | 1.4 |
| FalseTateExtension | 1.3 |

## After F3 (generic lemmas upstreamed to FontaineWintenberger 6c9e973)

Total: 5:21.10 wall, 812.24 s CPU, 31 modules.

| module | seconds |
|---|---|
| FalseTateExtension.KummerProfile | 95.0 |
| FalseTateExtension.Padic.Viviani | 76.0 |
| FalseTateExtension.Padic.CyclotomicUpper | 60.0 |
| FalseTateExtension.RadicalRamification | 35.0 |
| FalseTateExtension.GaloisLayers | 34.0 |
| FalseTateExtension.Padic.FiniteGaloisStructure | 17.0 |
| FalseTateExtension.Padic.CyclotomicRamification | 17.0 |
| FalseTateExtension.Padic.CyclotomicInertia | 17.0 |
| FalseTateExtension.Padic.CyclotomicAPF | 16.0 |
| FalseTateExtension.Padic.CyclotomicInertiaCompletion | 12.0 |
| FalseTateExtension.Padic.CyclotomicResidueBound | 11.0 |
| FalseTateExtension.Padic.KummerRamification | 8.4 |
| FalseTateExtension.GaloisStructure | 8.3 |
| FalseTateExtension.CyclotomicImage | 7.5 |
| FalseTateExtension.StrictAPF | 5.6 |
| FalseTateExtension.Padic.InfiniteCharacter | 5.2 |
| FalseTateExtension.AffineEmbedding | 3.7 |
| FalseTateExtension.AffineIndex | 3.3 |
| FalseTateExtension.AffineCommutator | 3.2 |
| FalseTateExtension.AffineKernel | 2.9 |
| FalseTateExtension.Padic.GeneralCharacter | 2.5 |
| FalseTateExtension.FiniteCoordinates | 2.2 |
| FalseTateExtension.Padic.FiniteCharacter | 1.9 |
| FalseTateExtension.Mathlib.FieldTheory.RestrictNormal | 1.9 |
| FalseTateExtension.PadicCoordinates | 1.8 |
| FalseTateExtension.Layers | 1.7 |
| FalseTateExtension.CoordinateTransitions | 1.7 |
| FalseTateExtension.Padic.ClosedAddSubgroup | 1.6 |
| FalseTateExtension.CompatibleRoots | 1.6 |
| FalseTateExtension.Padic.Cyclotomic | 1.4 |
| FalseTateExtension | 1.2 |

## After F5 (hypotheses as instances; F4 notation changes included)

Total: 5 min 09 s wall, 805 s CPU, 31 modules.

| module | seconds |
|---|---|
| FalseTateExtension.KummerProfile | 88.0 |
| FalseTateExtension.Padic.Viviani | 74.0 |
| FalseTateExtension.Padic.CyclotomicUpper | 57.0 |
| FalseTateExtension.RadicalRamification | 33.0 |
| FalseTateExtension.GaloisLayers | 33.0 |
| FalseTateExtension.Padic.CyclotomicRamification | 16.0 |
| FalseTateExtension.Padic.CyclotomicInertia | 16.0 |
| FalseTateExtension.Padic.CyclotomicAPF | 16.0 |
| FalseTateExtension.Padic.FiniteGaloisStructure | 15.0 |
| FalseTateExtension.Padic.CyclotomicResidueBound | 11.0 |
| FalseTateExtension.Padic.CyclotomicInertiaCompletion | 11.0 |
| FalseTateExtension.GaloisStructure | 8.8 |
| FalseTateExtension.Padic.KummerRamification | 8.7 |
| FalseTateExtension.CyclotomicImage | 7.9 |
| FalseTateExtension.Padic.InfiniteCharacter | 5.3 |
| FalseTateExtension.StrictAPF | 5.2 |
| FalseTateExtension.AffineIndex | 3.5 |
| FalseTateExtension.AffineEmbedding | 3.5 |
| FalseTateExtension.AffineCommutator | 3.3 |
| FalseTateExtension.AffineKernel | 3.0 |
| FalseTateExtension.Padic.GeneralCharacter | 2.7 |
| FalseTateExtension.FiniteCoordinates | 2.2 |
| FalseTateExtension.Padic.Basic | 1.9 |
| FalseTateExtension.Mathlib.FieldTheory.RestrictNormal | 1.9 |
| FalseTateExtension.PadicCoordinates | 1.8 |
| FalseTateExtension.Padic.ClosedAddSubgroup | 1.7 |
| FalseTateExtension.Layers | 1.7 |
| FalseTateExtension.CoordinateTransitions | 1.7 |
| FalseTateExtension.CompatibleRoots | 1.7 |
| FalseTateExtension.Padic.Cyclotomic | 1.4 |
| FalseTateExtension | 1.3 |
| FalseTateExtension.Padic.FiniteCharacter | 1.0 |

## Final (2026-10-20, after F10)

Total: 3 min 16 s wall, 510 s CPU, 64 modules; no `set_option maxHeartbeats`. Every module is
under 30 s except `Layers/Galois` (36 s, the cofinality lemmas added in F2; to be profiled).

| module | seconds |
|---|---|
| FalseTateExtension.Layers.Galois | 36.0 |
| FalseTateExtension.Kummer.Eisenstein | 20.0 |
| FalseTateExtension.Kummer.StepProfile | 19.0 |
| FalseTateExtension.FalseTate.Viviani.Filtration | 19.0 |
| FalseTateExtension.Cyclotomic.Ramification | 16.0 |
| FalseTateExtension.Cyclotomic.Inertia | 14.0 |
| FalseTateExtension.Cyclotomic.InertiaImage | 13.0 |
| FalseTateExtension.FalseTate.TotalRamification | 11.0 |
| FalseTateExtension.Cyclotomic.ResidueBound | 11.0 |
| FalseTateExtension.Kummer.FiniteProfile | 10.0 |
| FalseTateExtension.FalseTate.Viviani.Preliminaries | 10.0 |
| FalseTateExtension.Cyclotomic.APF | 9.7 |
| FalseTateExtension.FalseTate.Viviani.TauRamification | 8.5 |
| FalseTateExtension.Cyclotomic.Filtration | 7.6 |
| FalseTateExtension.Coordinates.CyclotomicImage | 6.9 |
| FalseTateExtension.FalseTate.FiniteGaloisGroup | 4.9 |
| FalseTateExtension.FalseTate.StrictAPF | 4.5 |
| FalseTateExtension.FalseTate.LiuLemma | 4.5 |
| FalseTateExtension.Mathlib.FieldTheory.Galois.InfiniteCorrespondence | 4.4 |
| FalseTateExtension.Cyclotomic.Restriction | 4.3 |
| FalseTateExtension.FalseTate.TranslationKernel | 4.1 |
| FalseTateExtension.Cyclotomic.CyclicLayers | 4.1 |
| FalseTateExtension.Padic.Basic | 3.9 |
| FalseTateExtension.Mathlib.FieldTheory.RestrictNormal | 3.9 |
| FalseTateExtension.Mathlib.NumberTheory.Padics.ClosedAddSubgroup | 3.8 |
| FalseTateExtension.Mathlib.RingTheory.PowerBasis.Eigenvector | 3.7 |
| FalseTateExtension.Mathlib.NumberTheory.Padics.Cyclotomic | 3.7 |
| FalseTateExtension.Layers.CompatibleRoots | 3.7 |
| FalseTateExtension.Coordinates.AffineEmbedding | 3.5 |
| FalseTateExtension.Kummer.APF | 3.4 |
| FalseTateExtension.FalseTate.RadicalNotCyclotomic | 3.3 |
| FalseTateExtension.Mathlib.RingTheory.Polynomial.EisensteinUniformizer | 3.2 |
| FalseTateExtension.Mathlib.NumberTheory.Cyclotomic.CharacterNaturality | 3.2 |
| FalseTateExtension.Mathlib.NumberTheory.Padics.Continuity | 3.1 |
| FalseTateExtension.Affine.Index | 3.1 |
| FalseTateExtension.Mathlib.FieldTheory.Galois.RestrictScalars | 3.0 |
| FalseTateExtension.FalseTate.Viviani.Corollary | 2.9 |
| FalseTateExtension.Cyclotomic.InfiniteCharacter | 2.8 |
| FalseTateExtension.Mathlib.FieldTheory.IntermediateField.Supremum | 2.7 |
| FalseTateExtension.FalseTate.AffineImage | 2.7 |
| FalseTateExtension.Cyclotomic.CharacterNaturality | 2.6 |
| FalseTateExtension.Coordinates.AffineKernel | 2.4 |
| FalseTateExtension.Layers.Basic | 2.1 |
| FalseTateExtension.Cyclotomic.FiniteCharacter | 2.1 |
| FalseTateExtension.Mathlib.Topology.Algebra.SemidirectProduct | 2.0 |
| FalseTateExtension.Coordinates.Finite | 2.0 |
| FalseTateExtension.Affine.ClosedSubgroup | 2.0 |
| FalseTateExtension.Padic.ClosedAddSubgroup | 1.9 |
| FalseTateExtension.Coordinates.Padic | 1.9 |
| FalseTateExtension.Mathlib.Data.ZMod.UnitsMap | 1.8 |
| FalseTateExtension.Coordinates.Transitions | 1.8 |
| FalseTateExtension.Mathlib | 1.7 |
| FalseTateExtension.Kummer.Breaks | 1.7 |
| FalseTateExtension.Cyclotomic.Basic | 1.7 |
| FalseTateExtension.Coordinates | 1.7 |
| FalseTateExtension.Affine.Padic | 1.7 |
| FalseTateExtension.Affine.Group | 1.7 |
| FalseTateExtension.Layers | 1.6 |
| FalseTateExtension.Padic | 1.4 |
| FalseTateExtension.Cyclotomic | 1.4 |
| FalseTateExtension.Kummer | 1.3 |
| FalseTateExtension.FalseTate | 1.3 |
| FalseTateExtension | 1.2 |
| FalseTateExtension.Affine | 1.1 |
