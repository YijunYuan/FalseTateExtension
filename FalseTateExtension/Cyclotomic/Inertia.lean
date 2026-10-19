/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FalseTateExtension.Cyclotomic.ResidueBound
public import FalseTateExtension.Cyclotomic.Restriction
public import FontaineWintenberger.LocalField.Residue.Basic
public import FontaineWintenberger.Ramification.Infinite.Restriction
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra

/-!
# Stabilization of cyclotomic inertia preimages

Restriction to the finite cyclotomic layers gives decreasing
open normal subgroups. Their indices are the finite residue degrees,
uniformly bounded by the base ramification index. Their stabilization and
cofinality of the layers prove openness of the infinite zero
upper group. Infinite restriction identifies it with the image of
the zero upper group of the algebraic closure.

This proves blueprint `ft:cyclotomic-inertia-preimages`. No identification
with an infinite residue quotient is asserted here.
-/

@[expose] public section

noncomputable section

open FontaineWintenberger

namespace FalseTateExtension

section Fields

variable {K : Type*} [Field K] [CharZero K] (p : ℕ) [Fact p.Prime]

/-- The positive layer, viewed by its inclusion as a finite
Galois intermediate field of the infinite cyclotomic field. -/
def cyclotomicFiniteLayer (n : ℕ) :
    FiniteGaloisIntermediateField K (cyclotomicExtension (K := K) p) := by
  let i := IntermediateField.inclusion
    (cyclotomicLayer_le_cyclotomicExtension (K := K) p (n + 1))
  let : Module.Finite K i.fieldRange := Module.Finite.equiv i.equivFieldRange.toLinearEquiv
  let : IsGalois K i.fieldRange := IsGalois.of_algEquiv i.equivFieldRange
  exact .mk i.fieldRange

/-- The inclusion is an isomorphism onto the finite field range. -/
def cyclotomicFiniteLayerEquiv (n : ℕ) :
    cyclotomicLayer (K := K) p (n + 1) ≃ₐ[K] cyclotomicFiniteLayer (K := K) p n :=
  (IntermediateField.inclusion
    (cyclotomicLayer_le_cyclotomicExtension (K := K) p (n + 1))).equivFieldRange

/-- Restriction to the field range is conjugate to restriction to the
finite layer through the inclusion isomorphism. -/
theorem restrictNormal_cyclotomicFiniteLayer (n : ℕ)
    (g : cyclotomicExtension (K := K) p ≃ₐ[K] cyclotomicExtension (K := K) p) :
    g.restrictNormal (cyclotomicFiniteLayer (K := K) p n) =
      (cyclotomicFiniteLayerEquiv (K := K) p n).autCongr
        (cyclotomicRestrictionToLayer p (n + 1) g) := by
  let e := cyclotomicFiniteLayerEquiv (K := K) p n
  apply AlgEquiv.ext
  intro x
  obtain ⟨y, rfl⟩ := e.surjective x
  apply Subtype.ext
  change ((g.restrictNormal (cyclotomicFiniteLayer (K := K) p n)) (e y) :
      cyclotomicExtension (K := K) p) =
    (e (cyclotomicRestrictionToLayer p (n + 1) g (e.symm (e y))) :
      cyclotomicExtension (K := K) p)
  rw [e.symm_apply_apply]
  exact (AlgEquiv.restrictNormal_commutes g (cyclotomicFiniteLayer (K := K) p n) (e y)).trans
    (cyclotomicRestrictionToLayer_commutes p (n + 1) g y).symm

/-- Every finite intermediate field is contained in a positive
cyclotomic layer. No finiteness of the infinite field is needed. -/
theorem exists_le_cyclotomicFiniteLayer
    (E : IntermediateField K (cyclotomicExtension (K := K) p)) [FiniteDimensional K E] :
    ∃ n, E ≤ (cyclotomicFiniteLayer (K := K) p n).toIntermediateField := by
  classical
  have hfg : E.FG := IntermediateField.essFiniteType_iff.mp inferInstance
  obtain ⟨s, hs⟩ := hfg
  have hx (x : cyclotomicExtension (K := K) p) :
      ∃ m, (x : AlgebraicClosure K) ∈ cyclotomicLayer p m :=
    (mem_cyclotomicExtension_iff p (x : AlgebraicClosure K)).mp x.property
  choose level hlevel using hx
  refine ⟨s.sup level, ?_⟩
  rw [← hs]
  apply IntermediateField.adjoin_le_iff.mpr
  intro x hx
  have hmem : (x : AlgebraicClosure K) ∈ cyclotomicLayer p (s.sup level + 1) :=
    cyclotomicLayer_mono p ((Finset.le_sup (f := level) hx).trans (Nat.le_succ _)) (hlevel x)
  change ∃ y : cyclotomicLayer (K := K) p (s.sup level + 1),
    IntermediateField.inclusion (cyclotomicLayer_le_cyclotomicExtension p (s.sup level + 1)) y = x
  exact ⟨⟨x, hmem⟩, Subtype.ext rfl⟩

end Fields

section Valued

variable (p : ℕ) [Fact p.Prime] (K : Type*) [NontriviallyNormedField K] [CharZero K]
    [IsCompleteDiscreteValuedField K]
    [NormedAlgebra (ℚ_[p]) K] [FiniteDimensional (ℚ_[p]) K]

include p in
omit [CharZero K] in
/-- The residue field of a finite compatible extension of the
p-adic rationals is finite. -/
theorem cyclotomicBase_residueFinite :
    Finite (𝓀[K]) := by
  have := normedAlgebra_residueField_finiteDimensional (ℚ_[p]) K
  exact Module.finite_of_finite
    (𝓀[ℚ_[p]])

/-- The finite Galois quotient by zero upper inertia has order the
residue degree, via the residue automorphism group. -/
theorem cyclotomicLayer_inertia_index (n : ℕ) :
    (upperRamificationGroup
      (R := spectralIntegerRing K (cyclotomicLayer (K := K) p (n + 1)))
      (cyclotomicLayer (K := K) p (n + 1) ≃ₐ[K] cyclotomicLayer (K := K) p (n + 1)) 0).index =
    Module.finrank
      (𝓀[K])
      (IsLocalRing.ResidueField (spectralIntegerRing K (cyclotomicLayer (K := K) p (n + 1)))) := by
  let := cyclotomicBase_residueFinite p K
  let R := 𝒪[K]
  let S := spectralIntegerRing K (cyclotomicLayer (K := K) p (n + 1))
  let G := cyclotomicLayer (K := K) p (n + 1) ≃ₐ[K] cyclotomicLayer (K := K) p (n + 1)
  rw [upperRamificationGroup_zero, ← lowerRamificationGroup_zero]
  exact (Nat.card_congr (localResidueGaloisEquiv R S G).toEquiv).trans
    (IsGalois.card_aut_eq_finrank (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField S))

/-- The preimage of finite zero upper inertia in the infinite
cyclotomic Galois group. Its index is numbered by the positive level `n+1`. -/
def cyclotomicInertiaPreimage (n : ℕ) :
    Subgroup (cyclotomicExtension (K := K) p ≃ₐ[K] cyclotomicExtension (K := K) p) := by
  exact (upperRamificationGroup
    (R := spectralIntegerRing K (cyclotomicLayer (K := K) p (n + 1)))
    (cyclotomicLayer (K := K) p (n + 1) ≃ₐ[K] cyclotomicLayer (K := K) p (n + 1)) 0).comap
      (cyclotomicRestrictionToLayer p (n + 1))

instance cyclotomicInertiaPreimage_finiteIndex (n : ℕ) :
    (cyclotomicInertiaPreimage p K n).FiniteIndex := by
  unfold cyclotomicInertiaPreimage
  infer_instance

instance cyclotomicInertiaPreimage_normal (n : ℕ) :
    (cyclotomicInertiaPreimage p K n).Normal := by
  unfold cyclotomicInertiaPreimage
  infer_instance

omit [NormedAlgebra ℚ_[p] K] [FiniteDimensional ℚ_[p] K] in
theorem isOpen_cyclotomicInertiaPreimage (n : ℕ) :
    IsOpen (cyclotomicInertiaPreimage p K n :
      Set (cyclotomicExtension (K := K) p ≃ₐ[K] cyclotomicExtension (K := K) p)) := by
  exact (isOpen_discrete _).preimage (continuous_cyclotomicRestrictionToLayer p (n + 1))

theorem cyclotomicInertiaPreimage_index (n : ℕ) :
    (cyclotomicInertiaPreimage p K n).index = Module.finrank
      (𝓀[K])
      (IsLocalRing.ResidueField (spectralIntegerRing K (cyclotomicLayer (K := K) p (n + 1)))) := by
  rw [cyclotomicInertiaPreimage, Subgroup.index_comap_of_surjective _
    (cyclotomicRestrictionToLayer_surjective p (n + 1))]
  exact cyclotomicLayer_inertia_index p K n

theorem cyclotomicInertiaPreimage_index_le (n : ℕ) :
    (cyclotomicInertiaPreimage p K n).index ≤
      (IsLocalRing.maximalIdeal 𝒪[K]).ramificationIdx
        𝒪[ℚ_[p]] := by
  rw [cyclotomicInertiaPreimage_index]
  exact cyclotomicLayer_spectral_residueDegree_le p K n

/-- Finite upper restriction makes the inertia preimages decrease. -/
theorem cyclotomicInertiaPreimage_antitone : Antitone (cyclotomicInertiaPreimage p K) := by
  let := cyclotomicBase_residueFinite p K
  intro m n h g hg
  let : Algebra (cyclotomicLayer (K := K) p (m + 1)) (cyclotomicLayer (K := K) p (n + 1)) :=
    IntermediateField.algebraOfLE (cyclotomicLayer_mono p (Nat.add_le_add_right h 1))
  have : IsScalarTower K (cyclotomicLayer (K := K) p (m + 1))
      (cyclotomicLayer (K := K) p (n + 1)) :=
    IntermediateField.isScalarTower_of_le (cyclotomicLayer_mono p (Nat.add_le_add_right h 1))
  change cyclotomicRestrictionToLayer p (n + 1) g ∈
    upperRamificationGroup (R := spectralIntegerRing K (cyclotomicLayer (K := K) p (n + 1)))
      (cyclotomicLayer (K := K) p (n + 1) ≃ₐ[K] cyclotomicLayer (K := K) p (n + 1)) 0 at hg
  change cyclotomicRestrictionToLayer p (m + 1) g ∈
    upperRamificationGroup (R := spectralIntegerRing K (cyclotomicLayer (K := K) p (m + 1)))
      (cyclotomicLayer (K := K) p (m + 1) ≃ₐ[K] cyclotomicLayer (K := K) p (m + 1)) 0
  rw [cyclotomicRestrictionToLayer_comp p (Nat.add_le_add_right h 1)]
  rw [← restrictNormalHom_map_upperRamificationGroup_tower K
    (cyclotomicLayer (K := K) p (m + 1)) (cyclotomicLayer (K := K) p (n + 1)) 0
    (by norm_num : (-1 : ℝ) ≤ 0)]
  exact Subgroup.mem_map.mpr ⟨cyclotomicRestrictionToLayer p (n + 1) g, hg, rfl⟩

theorem cyclotomicInertiaPreimage_index_monotone :
    Monotone (fun n ↦ (cyclotomicInertiaPreimage p K n).index) := by
  intro m n h
  exact Subgroup.index_antitone (cyclotomicInertiaPreimage_antitone p K h)

/-- Uniformly bounded positive indices force stabilization of the
decreasing subgroups, and their intersection is an attained preimage. -/
theorem exists_cyclotomicInertiaPreimage_stable :
    ∃ N, (∀ n, N ≤ n → cyclotomicInertiaPreimage p K n = cyclotomicInertiaPreimage p K N) ∧
      (⨅ n, cyclotomicInertiaPreimage p K n) = cyclotomicInertiaPreimage p K N := by
  obtain ⟨b, N, hN⟩ := converges_of_monotone_of_bounded
    (cyclotomicInertiaPreimage_index_monotone p K) (cyclotomicInertiaPreimage_index_le p K)
  have hstable (n : ℕ) (hn : N ≤ n) :
      cyclotomicInertiaPreimage p K n = cyclotomicInertiaPreimage p K N := by
    apply Subgroup.eq_of_index_dvd_index (cyclotomicInertiaPreimage_antitone p K hn)
    rw [hN n hn, hN N le_rfl]
  refine ⟨N, hstable, le_antisymm (iInf_le _ N) (le_iInf fun n ↦ ?_)⟩
  rcases le_total N n with hn | hn
  · rw [hstable n hn]
  · exact cyclotomicInertiaPreimage_antitone p K hn

/-- Cofinality of the positive layers identifies the infinite
zero upper group with the intersection of the inertia preimages. -/
theorem upperRamificationGroupInfinite_cyclotomic_eq_iInf :
    upperRamificationGroupInfinite K (cyclotomicExtension (K := K) p) 0 =
      ⨅ n, cyclotomicInertiaPreimage p K n := by
  let := cyclotomicBase_residueFinite p K
  ext g
  rw [mem_upperRamificationGroupInfinite]
  constructor
  · intro hg
    rw [Subgroup.mem_iInf]
    intro n
    change cyclotomicRestrictionToLayer p (n + 1) g ∈
      upperRamificationGroup (R := spectralIntegerRing K (cyclotomicLayer (K := K) p (n + 1)))
        (cyclotomicLayer (K := K) p (n + 1) ≃ₐ[K] cyclotomicLayer (K := K) p (n + 1)) 0
    have h := hg (cyclotomicFiniteLayer (K := K) p n)
    rw [restrictNormal_cyclotomicFiniteLayer] at h
    rw [← upperRamificationGroup_map_autCongr K (cyclotomicFiniteLayerEquiv (K := K) p n)
      (by norm_num : (-1 : ℝ) ≤ 0), Subgroup.mem_map_equiv] at h
    simpa only [MulEquiv.symm_apply_apply] using h
  · intro hg E
    obtain ⟨n, hn⟩ := exists_le_cyclotomicFiniteLayer p E.toIntermediateField
    let f : Opposite.op (cyclotomicFiniteLayer (K := K) p n) ⟶ Opposite.op E :=
      (CategoryTheory.homOfLE (show E ≤ cyclotomicFiniteLayer (K := K) p n from hn)).op
    have hn' := Subgroup.mem_iInf.mp hg n
    change cyclotomicRestrictionToLayer p (n + 1) g ∈
      upperRamificationGroup (R := spectralIntegerRing K (cyclotomicLayer (K := K) p (n + 1)))
        (cyclotomicLayer (K := K) p (n + 1) ≃ₐ[K] cyclotomicLayer (K := K) p (n + 1)) 0 at hn'
    have hD : g.restrictNormal (cyclotomicFiniteLayer (K := K) p n) ∈
        upperRamificationGroup (R := spectralIntegerRing K (cyclotomicFiniteLayer (K := K) p n))
          (cyclotomicFiniteLayer (K := K) p n ≃ₐ[K] cyclotomicFiniteLayer (K := K) p n) 0 := by
      rw [restrictNormal_cyclotomicFiniteLayer,
        ← upperRamificationGroup_map_autCongr K (cyclotomicFiniteLayerEquiv (K := K) p n)
          (by norm_num : (-1 : ℝ) ≤ 0)]
      exact Subgroup.mem_map.mpr ⟨cyclotomicRestrictionToLayer p (n + 1) g, hn', rfl⟩
    have hres := (InfiniteGalois.algEquivToLimit K (cyclotomicExtension (K := K) p) g).property f
    change (finGaloisGroupMap f).hom.hom
      (g.restrictNormal (cyclotomicFiniteLayer (K := K) p n)) = g.restrictNormal E at hres
    rw [← finGaloisGroupMap_map_upperRamificationGroup K (cyclotomicExtension (K := K) p) f 0
      (by norm_num : (-1 : ℝ) ≤ 0)]
    exact Subgroup.mem_map.mpr ⟨g.restrictNormal (cyclotomicFiniteLayer (K := K) p n), hD, hres⟩

/-- The infinite inertia group is already an attained finite-layer
inertia preimage, and all subsequent preimages are the same subgroup. -/
theorem exists_cyclotomic_inertia_eq_preimage :
    ∃ N, upperRamificationGroupInfinite K (cyclotomicExtension (K := K) p) 0 =
        cyclotomicInertiaPreimage p K N ∧
      ∀ n, N ≤ n → cyclotomicInertiaPreimage p K n = cyclotomicInertiaPreimage p K N := by
  obtain ⟨N, hstable, hinf⟩ := exists_cyclotomicInertiaPreimage_stable p K
  exact ⟨N, (upperRamificationGroupInfinite_cyclotomic_eq_iInf p K).trans hinf, hstable⟩

theorem cyclotomic_inertia_finiteIndex :
    (upperRamificationGroupInfinite K (cyclotomicExtension (K := K) p) 0).FiniteIndex := by
  obtain ⟨N, hN, _⟩ := exists_cyclotomic_inertia_eq_preimage p K
  rw [hN]
  infer_instance

/-- The infinite inertia index retains the sharp finite-layer bound. -/
theorem cyclotomic_inertia_index_le :
    (upperRamificationGroupInfinite K (cyclotomicExtension (K := K) p) 0).index ≤
      (IsLocalRing.maximalIdeal 𝒪[K]).ramificationIdx
        𝒪[ℚ_[p]] := by
  obtain ⟨N, hN, _⟩ := exists_cyclotomic_inertia_eq_preimage p K
  rw [hN]
  exact cyclotomicInertiaPreimage_index_le p K N

/-- The zero upper group is open in the Krull Galois group of the
infinite cyclotomic extension. -/
theorem isOpen_cyclotomic_inertia :
    IsOpen (upperRamificationGroupInfinite K (cyclotomicExtension (K := K) p) 0 :
      Set (cyclotomicExtension (K := K) p ≃ₐ[K] cyclotomicExtension (K := K) p)) := by
  obtain ⟨N, hN, _⟩ := exists_cyclotomic_inertia_eq_preimage p K
  rw [hN]
  exact isOpen_cyclotomicInertiaPreimage p K N

/-- Full infinite restriction identifies the cyclotomic
inertia with the image of the algebraic closure's zero upper group. -/
theorem cyclotomic_inertia_eq_absolute_image :
    (upperRamificationGroupInfinite K (AlgebraicClosure K) 0).map
      (AlgEquiv.restrictNormalHom (cyclotomicExtension (K := K) p)) =
        upperRamificationGroupInfinite K (cyclotomicExtension (K := K) p) 0 := by
  let := cyclotomicBase_residueFinite p K
  exact restrictNormalHom_map_upperRamificationGroupInfinite K (AlgebraicClosure K)
    (cyclotomicExtension (K := K) p) 0 (by norm_num : (-1 : ℝ) ≤ 0)

end Valued

end FalseTateExtension

end
