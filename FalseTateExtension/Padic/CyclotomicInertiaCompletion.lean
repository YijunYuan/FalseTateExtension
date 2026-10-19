/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FalseTateExtension.Padic.CyclotomicInertia
public import FalseTateExtension.Padic.GeneralCharacter
public import FontaineWintenberger.Ramification.Lower.SpectralMaps
public import Mathlib.NumberTheory.Padics.ProperSpace

/-!
# Completion of the cyclotomic residue and inertia proofs

Original inclusions induce compatible local maps on the actual spectral
integer rings and injective maps on their actual residue fields. Exhaustion
by finite layers and the uniform residue-degree bound show that a finite
layer already maps isomorphically onto the infinite extension's residue
field. The canonical character maps actual inertia onto an open subgroup
of the p-adic units containing a nonidentity element.

This completes blueprint `ft:cyclotomic-infinite-residue-bound` and
`ft:cyclotomic-inertia`. Completion here concerns the proofs, not a
completion of the infinite cyclotomic field as a valued field.
-/

@[expose] public section

noncomputable section

open FontaineWintenberger

namespace FalseTateExtension



section CyclotomicResidues

variable (p : ℕ) [Fact p.Prime] (K : Type*) [NontriviallyNormedField K] [CharZero K]
    [IsCompleteDiscreteValuedField K]

/-- The actual base-residue algebra map from a positive chosen layer to
the residue field of the actual infinite spectral integer ring. -/
def cyclotomicResidueToExtension (n : ℕ) :
    IsLocalRing.ResidueField (spectralIntegerRing K (cyclotomicLayer (K := K) p (n + 1))) →ₐ[
      𝓀[K]]
        IsLocalRing.ResidueField (spectralIntegerRing K (cyclotomicExtension (K := K) p)) :=
  spectralResidueInclusion K (IntermediateField.inclusion
    (cyclotomicLayer_le_cyclotomicExtension (K := K) p (n + 1)))

/-- The actual residue inclusion between two positive chosen layers. -/
def cyclotomicResidueBetweenLayers {n m : ℕ} (h : n ≤ m) :
    IsLocalRing.ResidueField (spectralIntegerRing K (cyclotomicLayer (K := K) p (n + 1))) →ₐ[
      𝓀[K]]
        IsLocalRing.ResidueField (spectralIntegerRing K (cyclotomicLayer (K := K) p (m + 1))) :=
  spectralResidueInclusion K
    (IntermediateField.inclusion (cyclotomicLayer_mono (K := K) p (Nat.add_le_add_right h 1)))

theorem cyclotomicResidueToExtension_comp {n m : ℕ} (h : n ≤ m) :
    cyclotomicResidueToExtension p K n =
      (cyclotomicResidueToExtension p K m).comp (cyclotomicResidueBetweenLayers p K h) := by
  unfold cyclotomicResidueToExtension cyclotomicResidueBetweenLayers
  rw [← spectralResidueInclusion_comp]
  congr 1

/-- Every actual infinite residue class has an integral representative
already in a positive chosen finite layer. -/
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
theorem cyclotomicResidue_degree_monotone :
    Monotone (fun n ↦ Module.finrank
      (𝓀[K])
      (IsLocalRing.ResidueField (spectralIntegerRing K (cyclotomicLayer (K := K) p (n + 1))))) := by
  intro n m h
  exact LinearMap.finrank_le_finrank_of_injective
    (f := (cyclotomicResidueBetweenLayers p K h).toLinearMap)
    (cyclotomicResidueBetweenLayers p K h).injective

/-- Bounded finite residue degrees make the actual residue map from some
positive chosen layer bijective onto the actual infinite residue field. -/
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

/-- An attained finite layer's actual residue field is isomorphic to the
actual infinite residue field, with its original residue-map evaluation. -/
theorem exists_cyclotomicResidueEquiv :
    ∃ N, ∃ e : IsLocalRing.ResidueField
        (spectralIntegerRing K (cyclotomicLayer (K := K) p (N + 1))) ≃ₐ[
          𝓀[K]]
            IsLocalRing.ResidueField (spectralIntegerRing K (cyclotomicExtension (K := K) p)),
      ∀ x, e x = cyclotomicResidueToExtension p K N x := by
  obtain ⟨N, hN⟩ := exists_cyclotomicResidueToExtension_bijective p K
  exact ⟨N, AlgEquiv.ofBijective (cyclotomicResidueToExtension p K N) hN, fun _ ↦ rfl⟩

/-- The actual infinite residue extension is finite-dimensional. This is
proved before using a natural-number finrank bound for that extension. -/
theorem cyclotomicExtension_residue_finiteDimensional :
    FiniteDimensional
      (𝓀[K])
      (IsLocalRing.ResidueField (spectralIntegerRing K (cyclotomicExtension (K := K) p))) := by
  obtain ⟨N, e, _⟩ := exists_cyclotomicResidueEquiv p K
  exact Module.Finite.equiv e.toLinearEquiv

/-- The actual infinite residue degree satisfies the sharp bound by the
original base ramification index. -/
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

/-- The character image of actual absolute zero upper inertia, through
ordinary restriction to the original infinite cyclotomic field. -/
def cyclotomicInertiaCharacterImage : Subgroup (ℤ_[p])ˣ := by
  exact (upperRamificationGroupInfinite K (AlgebraicClosure K) 0).map
    ((cyclotomicExtensionCharacter (K := K) p).comp
      (AlgEquiv.restrictNormalHom (cyclotomicExtension (K := K) p)))

/-- Full infinite upper restriction identifies the absolute inertia image
with the character image of the actual infinite cyclotomic zero upper group. -/
theorem cyclotomicInertiaCharacterImage_eq_map :
    cyclotomicInertiaCharacterImage p K =
      (upperRamificationGroupInfinite K (cyclotomicExtension (K := K) p) 0).map
        (cyclotomicExtensionCharacter p) := by
  unfold cyclotomicInertiaCharacterImage
  rw [← Subgroup.map_map, cyclotomic_inertia_eq_absolute_image p K]

omit [NormedAlgebra ℚ_[p] K] [FiniteDimensional ℚ_[p] K] in
/-- Naturality identifies the same image with the original canonical
character acting on the actual algebraic closure. -/
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
/-- The existing canonical character is an open embedding because its
actual closed image has already been proved open. -/
theorem isOpenEmbedding_cyclotomicExtensionCharacter :
    Topology.IsOpenEmbedding (cyclotomicExtensionCharacter (K := K) p) :=
  ⟨(isClosedEmbedding_cyclotomicExtensionCharacter p).isEmbedding,
    isOpen_cyclotomicExtensionCharacter_range p⟩

/-- Actual absolute inertia has open character image in the p-adic units. -/
theorem isOpen_cyclotomicInertiaCharacterImage :
    IsOpen (cyclotomicInertiaCharacterImage p K : Set (ℤ_[p])ˣ) := by
  rw [cyclotomicInertiaCharacterImage_eq_map]
  exact (isOpenEmbedding_cyclotomicExtensionCharacter p K).isOpenMap _
    (isOpen_cyclotomic_inertia p K)

theorem cyclotomicInertiaCharacterImage_finiteIndex :
    (cyclotomicInertiaCharacterImage p K).FiniteIndex := by
  let := (cyclotomicInertiaCharacterImage p K).quotient_finite_of_isOpen
    (isOpen_cyclotomicInertiaCharacterImage p K)
  exact Subgroup.finiteIndex_of_finite_quotient

end InertiaImage

end FalseTateExtension

end
