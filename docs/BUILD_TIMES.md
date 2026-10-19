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
