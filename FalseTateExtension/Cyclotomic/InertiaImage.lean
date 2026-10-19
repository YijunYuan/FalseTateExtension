/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FalseTateExtension.Cyclotomic.Inertia
public import FalseTateExtension.Cyclotomic.CharacterNaturality
public import FontaineWintenberger.Ramification.Lower.SpectralMaps
public import Mathlib.NumberTheory.Padics.ProperSpace

/-!
# The residue field of `K(ζ_{p^∞})` and the character image of inertia

Let `K/ℚ_[p]` be a finite extension. The residue field of the spectral integer ring of
`K(ζ_{p^∞})` is the union of the residue fields of the layers `K(ζ_{p^{n+1}})`; since their
degrees over `𝓀[K]` are bounded by `e(K/ℚ_[p])`, some layer `K(ζ_{p^{N+1}})` has the same
residue field as `K(ζ_{p^∞})`, and the residue degree of `K(ζ_{p^∞})/K` is finite and at most
`e(K/ℚ_[p])`. The cyclotomic character `χ : Gal(K(ζ_{p^∞})/K) → ℤ_[p]ˣ` is an open embedding,
and the image under `χ` of the inertia subgroup of `Gal(K̄/K)` is an open subgroup of `ℤ_[p]ˣ`
of finite index.

## Main results

* `exists_cyclotomicResidueEquiv`: for some `N`, the residue field of `K(ζ_{p^{N+1}})` maps
  isomorphically onto the residue field of `K(ζ_{p^∞})`
* `cyclotomicExtension_residue_degree_le`: the residue degree of `K(ζ_{p^∞})/K` is at most
  `e(K/ℚ_[p])`
* `cyclotomicInertiaCharacterImage`: the image `χ(Gal(K̄/K)^0) ≤ ℤ_[p]ˣ`
* `isOpenEmbedding_cyclotomicExtensionCharacter`: `χ` is an open embedding
* `isOpen_cyclotomicInertiaCharacterImage`, `cyclotomicInertiaCharacterImage_finiteIndex`:
  `χ(Gal(K̄/K)^0)` is open of finite index in `ℤ_[p]ˣ`

## References

* Liu, *On lattices in semi-stable representations*, §5.1.
-/

@[expose] public section

noncomputable section

open FontaineWintenberger

namespace FalseTateExtension



section CyclotomicResidues

variable (p : ℕ) [Fact p.Prime] (K : Type*) [NontriviallyNormedField K] [CharZero K]
    [IsCompleteDiscreteValuedField K]

/-- The `𝓀[K]`-algebra map from the residue field of `K(ζ_{p^{n+1}})` to the residue field of
`K(ζ_{p^∞})`, induced by the inclusion of spectral integer rings. -/
def cyclotomicResidueToExtension (n : ℕ) :
    IsLocalRing.ResidueField (spectralIntegerRing K (cyclotomicLayer (K := K) p (n + 1))) →ₐ[
      𝓀[K]]
        IsLocalRing.ResidueField (spectralIntegerRing K (cyclotomicExtension (K := K) p)) :=
  spectralResidueInclusion K (IntermediateField.inclusion
    (cyclotomicLayer_le_cyclotomicExtension (K := K) p (n + 1)))

/-- The `𝓀[K]`-algebra map from the residue field of `K(ζ_{p^{n+1}})` to the residue field of
`K(ζ_{p^{m+1}})`, `n ≤ m`, induced by the inclusion of spectral integer rings. -/
def cyclotomicResidueBetweenLayers {n m : ℕ} (h : n ≤ m) :
    IsLocalRing.ResidueField (spectralIntegerRing K (cyclotomicLayer (K := K) p (n + 1))) →ₐ[
      𝓀[K]]
        IsLocalRing.ResidueField (spectralIntegerRing K (cyclotomicLayer (K := K) p (m + 1))) :=
  spectralResidueInclusion K
    (IntermediateField.inclusion (cyclotomicLayer_mono (K := K) p (Nat.add_le_add_right h 1)))

/-- For `n ≤ m`, the residue map from `K(ζ_{p^{n+1}})` to `K(ζ_{p^∞})` factors through the
residue field of `K(ζ_{p^{m+1}})`. -/
theorem cyclotomicResidueToExtension_comp {n m : ℕ} (h : n ≤ m) :
    cyclotomicResidueToExtension p K n =
      (cyclotomicResidueToExtension p K m).comp (cyclotomicResidueBetweenLayers p K h) := by
  unfold cyclotomicResidueToExtension cyclotomicResidueBetweenLayers
  rw [← spectralResidueInclusion_comp]
  congr 1

/-- Every element of the residue field of `K(ζ_{p^∞})` is the image of an element of the residue
field of some layer `K(ζ_{p^{n+1}})`. -/
theorem exists_cyclotomicResidueToExtension_preimage
    (z : IsLocalRing.ResidueField (spectralIntegerRing K (cyclotomicExtension (K := K) p))) :
    ∃ n, ∃ x, cyclotomicResidueToExtension p K n x = z := by
  obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective z
  obtain ⟨m, hm⟩ :=
    (mem_cyclotomicExtension_iff p ((x : cyclotomicExtension (K := K) p) : AlgebraicClosure K)).mp
      (x : cyclotomicExtension (K := K) p).property
  let i := IntermediateField.inclusion
    (cyclotomicLayer_le_cyclotomicExtension (K := K) p (m + 1))
  let y : cyclotomicLayer (K := K) p (m + 1) :=
    ⟨x, cyclotomicLayer_mono p (Nat.le_succ m) hm⟩
  have hyi : i y = (x : cyclotomicExtension (K := K) p) := Subtype.ext rfl
  let : Algebra (cyclotomicLayer (K := K) p (m + 1)) (cyclotomicExtension (K := K) p) :=
    i.toRingHom.toAlgebra
  let : IsScalarTower K (cyclotomicLayer (K := K) p (m + 1)) (cyclotomicExtension (K := K) p) :=
    IsScalarTower.of_algebraMap_eq (fun r ↦ (i.commutes r).symm)
  have hy : y ∈ spectralIntegerRing K (cyclotomicLayer (K := K) p (m + 1)) := by
    rw [mem_spectralIntegerRing, spectralNorm.eq_of_tower (L := cyclotomicExtension (K := K) p) y]
    change spectralNorm K (cyclotomicExtension (K := K) p) (i y) ≤ 1
    rw [hyi]
    exact (mem_spectralIntegerRing K _ _).mp x.property
  refine ⟨m, IsLocalRing.residue _ ⟨y, hy⟩, ?_⟩
  change spectralResidueInclusion K i (IsLocalRing.residue _ ⟨y, hy⟩) = _
  rw [spectralResidueInclusion_residue]
  congr 1

variable [NormedAlgebra (ℚ_[p]) K] [FiniteDimensional (ℚ_[p]) K]

omit [NormedAlgebra ℚ_[p] K] [FiniteDimensional ℚ_[p] K] in
/-- The residue degrees `f(K(ζ_{p^{n+1}})/K)` are nondecreasing in `n`. -/
theorem cyclotomicResidue_degree_monotone :
    Monotone (fun n ↦ Module.finrank
      (𝓀[K])
      (IsLocalRing.ResidueField (spectralIntegerRing K (cyclotomicLayer (K := K) p (n + 1))))) := by
  intro n m h
  exact LinearMap.finrank_le_finrank_of_injective
    (f := (cyclotomicResidueBetweenLayers p K h).toLinearMap)
    (cyclotomicResidueBetweenLayers p K h).injective

/-- For `K/ℚ_[p]` finite, the residue map from some layer `K(ζ_{p^{N+1}})` to `K(ζ_{p^∞})` is
bijective. -/
theorem exists_cyclotomicResidueToExtension_bijective :
    ∃ N, Function.Bijective (cyclotomicResidueToExtension p K N) := by
  obtain ⟨b, N, hN⟩ := converges_of_monotone_of_bounded
    (cyclotomicResidue_degree_monotone p K) (cyclotomicLayer_spectral_residueDegree_le p K)
  have hsur (m : ℕ) (hm : N ≤ m) :
      Function.Surjective (cyclotomicResidueBetweenLayers p K hm) :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (f := (cyclotomicResidueBetweenLayers p K hm).toLinearMap)
      ((hN N le_rfl).trans (hN m hm).symm)).mp
        (cyclotomicResidueBetweenLayers p K hm).injective
  refine ⟨N, spectralResidueInclusion_injective K (IntermediateField.inclusion
    (cyclotomicLayer_le_cyclotomicExtension (K := K) p (N + 1))), ?_⟩
  intro z
  obtain ⟨m, x, hx⟩ := exists_cyclotomicResidueToExtension_preimage p K z
  obtain ⟨y, hy⟩ := hsur (max m N) (le_max_right m N)
    (cyclotomicResidueBetweenLayers p K (le_max_left m N) x)
  refine ⟨y, ?_⟩
  calc
    _ = cyclotomicResidueToExtension p K (max m N)
        (cyclotomicResidueBetweenLayers p K (le_max_right m N) y) :=
      congrArg (fun f ↦ f y) (cyclotomicResidueToExtension_comp p K (le_max_right m N))
    _ = cyclotomicResidueToExtension p K (max m N)
        (cyclotomicResidueBetweenLayers p K (le_max_left m N) x) := congrArg _ hy
    _ = cyclotomicResidueToExtension p K m x :=
      (congrArg (fun f ↦ f x) (cyclotomicResidueToExtension_comp p K (le_max_left m N))).symm
    _ = z := hx

/-- For `K/ℚ_[p]` finite, the residue map from some layer `K(ζ_{p^{N+1}})` to `K(ζ_{p^∞})` is
an isomorphism of `𝓀[K]`-algebras. -/
theorem exists_cyclotomicResidueEquiv :
    ∃ N, ∃ e : IsLocalRing.ResidueField
        (spectralIntegerRing K (cyclotomicLayer (K := K) p (N + 1))) ≃ₐ[
          𝓀[K]]
            IsLocalRing.ResidueField (spectralIntegerRing K (cyclotomicExtension (K := K) p)),
      ∀ x, e x = cyclotomicResidueToExtension p K N x := by
  obtain ⟨N, hN⟩ := exists_cyclotomicResidueToExtension_bijective p K
  exact ⟨N, AlgEquiv.ofBijective (cyclotomicResidueToExtension p K N) hN, fun _ ↦ rfl⟩

/-- For `K/ℚ_[p]` finite, the residue field of `K(ζ_{p^∞})` is finite over `𝓀[K]`. -/
theorem cyclotomicExtension_residue_finiteDimensional :
    FiniteDimensional
      (𝓀[K])
      (IsLocalRing.ResidueField (spectralIntegerRing K (cyclotomicExtension (K := K) p))) := by
  obtain ⟨N, e, _⟩ := exists_cyclotomicResidueEquiv p K
  exact Module.Finite.equiv e.toLinearEquiv

/-- For `K/ℚ_[p]` finite, the residue degree of `K(ζ_{p^∞})/K` is at most `e(K/ℚ_[p])`. -/
theorem cyclotomicExtension_residue_degree_le :
    Module.finrank
      (𝓀[K])
      (IsLocalRing.ResidueField (spectralIntegerRing K (cyclotomicExtension (K := K) p))) ≤
        (IsLocalRing.maximalIdeal 𝒪[K]).ramificationIdx
          𝒪[ℚ_[p]] := by
  let := cyclotomicExtension_residue_finiteDimensional p K
  obtain ⟨N, e, _⟩ := exists_cyclotomicResidueEquiv p K
  exact e.toLinearEquiv.finrank_eq.symm.trans_le (cyclotomicLayer_spectral_residueDegree_le p K N)

end CyclotomicResidues

section InertiaImage

variable (p : ℕ) [Fact p.Prime] (K : Type*) [NontriviallyNormedField K] [CharZero K]
    [IsCompleteDiscreteValuedField K]
    [NormedAlgebra (ℚ_[p]) K] [FiniteDimensional (ℚ_[p]) K]

/-- The subgroup `χ(Gal(K̄/K)^0)` of `ℤ_[p]ˣ`: the image of the inertia subgroup of `Gal(K̄/K)`
under restriction to `K(ζ_{p^∞})` followed by the cyclotomic character. -/
def cyclotomicInertiaCharacterImage : Subgroup (ℤ_[p])ˣ := by
  exact (upperRamificationGroupInfinite K (AlgebraicClosure K) 0).map
    ((cyclotomicExtensionCharacter (K := K) p).comp
      (AlgEquiv.restrictNormalHom (cyclotomicExtension (K := K) p)))

/-- `χ(Gal(K̄/K)^0) = χ(Gal(K(ζ_{p^∞})/K)^0)`. -/
theorem cyclotomicInertiaCharacterImage_eq_map :
    cyclotomicInertiaCharacterImage p K =
      (upperRamificationGroupInfinite K (cyclotomicExtension (K := K) p) 0).map
        (cyclotomicExtensionCharacter p) := by
  unfold cyclotomicInertiaCharacterImage
  rw [← Subgroup.map_map, cyclotomic_inertia_eq_absolute_image p K]

omit [NormedAlgebra ℚ_[p] K] [FiniteDimensional ℚ_[p] K] in
/-- `χ(Gal(K̄/K)^0)` is the image of `Gal(K̄/K)^0` under the cyclotomic character of `K̄`. -/
theorem cyclotomicInertiaCharacterImage_eq_absolute_character :
    cyclotomicInertiaCharacterImage p K =
      (upperRamificationGroupInfinite K (AlgebraicClosure K) 0).map
        ((_root_.cyclotomicCharacter (AlgebraicClosure K) p).comp
          (MulSemiringAction.toRingAut
            (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) (AlgebraicClosure K))) := by
  unfold cyclotomicInertiaCharacterImage
  have hc : (cyclotomicExtensionCharacter (K := K) p).comp
      (AlgEquiv.restrictNormalHom (cyclotomicExtension (K := K) p)) =
    (_root_.cyclotomicCharacter (AlgebraicClosure K) p).comp
      (MulSemiringAction.toRingAut
        (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) (AlgebraicClosure K)) := by
    apply MonoidHom.ext
    intro g
    exact cyclotomicCharacter_restrict_cyclotomicExtension p g
  rw [hc]

omit [IsCompleteDiscreteValuedField K] in
/-- For `K/ℚ_[p]` finite, the cyclotomic character `Gal(K(ζ_{p^∞})/K) → ℤ_[p]ˣ` is an open
embedding. -/
theorem isOpenEmbedding_cyclotomicExtensionCharacter :
    Topology.IsOpenEmbedding (cyclotomicExtensionCharacter (K := K) p) :=
  ⟨(isClosedEmbedding_cyclotomicExtensionCharacter p).isEmbedding,
    isOpen_cyclotomicExtensionCharacter_range p⟩

/-- `χ(Gal(K̄/K)^0)` is an open subgroup of `ℤ_[p]ˣ`. -/
theorem isOpen_cyclotomicInertiaCharacterImage :
    IsOpen (cyclotomicInertiaCharacterImage p K : Set (ℤ_[p])ˣ) := by
  rw [cyclotomicInertiaCharacterImage_eq_map]
  exact (isOpenEmbedding_cyclotomicExtensionCharacter p K).isOpenMap _
    (isOpen_cyclotomic_inertia p K)

/-- `χ(Gal(K̄/K)^0)` has finite index in `ℤ_[p]ˣ`. -/
theorem cyclotomicInertiaCharacterImage_finiteIndex :
    (cyclotomicInertiaCharacterImage p K).FiniteIndex := by
  let := (cyclotomicInertiaCharacterImage p K).quotient_finite_of_isOpen
    (isOpen_cyclotomicInertiaCharacterImage p K)
  exact Subgroup.finiteIndex_of_finite_quotient

end InertiaImage

end FalseTateExtension

end
