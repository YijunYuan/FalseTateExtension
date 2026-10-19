/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FalseTateExtension.Padic.CyclotomicRamification
public import FontaineWintenberger.Ramification.Upper.Transport
public import FontaineWintenberger.Ramification.Lower.Inertia
public import FontaineWintenberger.APF.BaseChange.UpperGroups
public import Mathlib.NumberTheory.Padics.RingHoms
public import FontaineWintenberger.LocalField.Spectral.Transport

/-!
# The residue-degree bound for actual finite cyclotomic layers

Inside an actual cyclotomic layer over a finite extension of the p-adic
rationals, the same primitive root generates a rational cyclotomic subfield.
Its total ramification, the minimal-polynomial degree bound and actual local
ramification-index towers give the sharp residue-degree bound by the base
ramification index. Compatible valuation rings are identified explicitly.

This proves blueprint `ft:cyclotomic-finite-residue-bound`.
-/

@[expose] public section

noncomputable section

open Polynomial FontaineWintenberger

namespace FalseTateExtension

variable (p : ℕ) [Fact p.Prime]

/-- Rational cyclotomic layers have full inertia, by the proved actual
ramification index and the actual inertia-cardinality theorem. -/
theorem cyclotomicLayer_padic_upper_zero (n : ℕ) :
    upperRamificationGroup
      (R := spectralIntegerRing (ℚ_[p]) (cyclotomicLayer (K := ℚ_[p]) p (n + 1)))
      (cyclotomicLayer (K := ℚ_[p]) p (n + 1) ≃ₐ[ℚ_[p]]
        cyclotomicLayer (K := ℚ_[p]) p (n + 1)) 0 = ⊤ := by
  rw [upperRamificationGroup_zero]
  apply Subgroup.eq_top_of_card_eq
  have h := spectralIntegerRing_card_lower_zero (ℚ_[p])
    (cyclotomicLayer (K := ℚ_[p]) p (n + 1))
  rw [lowerRamificationGroup_zero, cyclotomicLayer_spectral_ramificationIdx] at h
  exact h.trans ((finrank_cyclotomicLayer_padic p (n + 1)).symm.trans
    (IsGalois.card_aut_eq_finrank (ℚ_[p]) (cyclotomicLayer (K := ℚ_[p]) p (n + 1))).symm)

/-- Total ramification transfers to every actual rational prime-power
cyclotomic field via its canonical field and integer-ring isomorphisms. -/
theorem rationalCyclotomic_ramificationIdx (n : ℕ)
    (F : Type*) [Field F] [Algebra (ℚ_[p]) F] [FiniteDimensional (ℚ_[p]) F]
    [IsCyclotomicExtension {p ^ (n + 1)} (ℚ_[p]) F] :
    (IsLocalRing.maximalIdeal (spectralIntegerRing (ℚ_[p]) F)).ramificationIdx
      𝒪[ℚ_[p]] = (p ^ (n + 1)).totient := by
  have : NeZero (p ^ (n + 1)) := ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
  have : IsGalois (ℚ_[p]) F := IsCyclotomicExtension.isGalois {p ^ (n + 1)} (ℚ_[p]) F
  let e := IsCyclotomicExtension.algEquiv {p ^ (n + 1)} (ℚ_[p])
    (cyclotomicLayer (K := ℚ_[p]) p (n + 1)) F
  have ht : upperRamificationGroup (R := spectralIntegerRing (ℚ_[p]) F)
      (F ≃ₐ[ℚ_[p]] F) 0 = ⊤ := by
    rw [← upperRamificationGroup_map_autCongr (ℚ_[p]) e (by norm_num : (-1 : ℝ) ≤ 0),
      cyclotomicLayer_padic_upper_zero, Subgroup.map_top]
    exact MonoidHom.range_eq_top.mpr e.autCongr.surjective
  have h := spectralIntegerRing_card_lower_zero (ℚ_[p]) F
  rw [lowerRamificationGroup_zero, ← upperRamificationGroup_zero, ht,
    Subgroup.card_top, IsGalois.card_aut_eq_finrank] at h
  exact h.symm.trans
    (e.toLinearEquiv.finrank_eq.symm.trans (finrank_cyclotomicLayer_padic p (n + 1)))

section Fields

variable {K : Type*} [Field K] [CharZero K] [Algebra (ℚ_[p]) K]

/-- The actual finite cyclotomic layer has degree at most the rational
prime-power totient, by minimal-polynomial divisibility under scalar extension. -/
theorem finrank_cyclotomicLayer_le_totient (m : ℕ) :
    Module.finrank K (cyclotomicLayer (K := K) p m) ≤ (p ^ m).totient := by
  have hi := (isPrimitiveRoot_rootOfUnity (K := K) p m).isIntegral
    (pow_pos (Fact.out : p.Prime).pos m)
  have hdim : Module.finrank K (cyclotomicLayer (K := K) p m) =
      (minpoly K (rootOfUnity (K := K) p m)).natDegree :=
    IntermediateField.adjoin.finrank (hi.tower_top : IsIntegral K (rootOfUnity p m))
  rw [hdim]
  have hd := minpoly.dvd_map_of_isScalarTower (ℚ_[p]) K (rootOfUnity (K := K) p m)
  rw [← (isPrimitiveRoot_rootOfUnity (K := K) p m).minpoly_eq_cyclotomic_of_irreducible
    (Padic.irreducible_cyclotomic_prime_pow p m)] at hd
  exact (Polynomial.natDegree_le_of_dvd hd ((cyclotomic.monic _ _).map _).ne_zero).trans_eq
    (by rw [Polynomial.natDegree_map, natDegree_cyclotomic])

/-- The rational cyclotomic subfield inside the same actual finite layer. -/
def rationalCyclotomicSubfield (m : ℕ) :
    IntermediateField (ℚ_[p]) (cyclotomicLayer (K := K) p m) :=
  IntermediateField.adjoin (ℚ_[p])
    {(⟨rootOfUnity p m, rootOfUnity_mem_cyclotomicLayer p m⟩ : cyclotomicLayer (K := K) p m)}

omit [Algebra (ℚ_[p]) K] in
/-- The generator in the original finite layer remains primitive. -/
theorem isPrimitiveRoot_cyclotomicLayer_generator (m : ℕ) :
    IsPrimitiveRoot
      (⟨rootOfUnity p m, rootOfUnity_mem_cyclotomicLayer p m⟩ : cyclotomicLayer (K := K) p m)
      (p ^ m) :=
  (isPrimitiveRoot_rootOfUnity (K := K) p m).of_map_of_injective
    (f := (cyclotomicLayer (K := K) p m).val) (cyclotomicLayer p m).val.injective

variable [FiniteDimensional (ℚ_[p]) K]

instance rationalCyclotomicSubfield_isCyclotomicExtension (m : ℕ) :
    IsCyclotomicExtension {p ^ m} (ℚ_[p]) (rationalCyclotomicSubfield (K := K) p m) := by
  have : NeZero (p ^ m) := ⟨pow_ne_zero m (Fact.out : p.Prime).ne_zero⟩
  let : FiniteDimensional (ℚ_[p]) (cyclotomicLayer (K := K) p m) :=
    FiniteDimensional.trans (ℚ_[p]) K _
  have hζ := (isPrimitiveRoot_cyclotomicLayer_generator (K := K) p m)
  exact hζ.intermediateField_adjoin_isCyclotomicExtension (ℚ_[p])

omit [FiniteDimensional (ℚ_[p]) K] in
instance rationalCyclotomicSubfield_finiteDimensional (m : ℕ) :
    FiniteDimensional (ℚ_[p]) (rationalCyclotomicSubfield (K := K) p m) :=
  IntermediateField.adjoin.finiteDimensional
    (((isPrimitiveRoot_cyclotomicLayer_generator (K := K) p m).isIntegral
      (pow_pos (Fact.out : p.Prime).pos m)).tower_top)

end Fields

section Valued

variable (K : Type*) [NontriviallyNormedField K] [CharZero K]
    [IsCompleteDiscreteValuedField K]
    [NormedAlgebra (ℚ_[p]) K] [FiniteDimensional (ℚ_[p]) K]

/-- The canonical spectral integer ring of the same actual finite layer
has residue degree bounded by the actual base ramification index. -/
theorem cyclotomicLayer_spectral_residueDegree_le (n : ℕ) :
    Module.finrank
        (𝓀[K])
        (IsLocalRing.ResidueField (spectralIntegerRing K (cyclotomicLayer (K := K) p (n + 1)))) ≤
      (IsLocalRing.maximalIdeal 𝒪[K]).ramificationIdx
        𝒪[ℚ_[p]] := by
  let C := cyclotomicLayer (K := K) p (n + 1)
  let : NontriviallyNormedField C := spectralNorm.nontriviallyNormedField K C
  let : NormedAlgebra K C := spectralNorm.normedAlgebra K C
  let : IsUltrametricDist C :=
    IsUltrametricDist.isUltrametricDist_iff_isNonarchimedean_norm.mpr
      (isNonarchimedean_spectralNorm (K := K) (L := C))
  let : NormedAlgebra (ℚ_[p]) C :=
    { (inferInstance : Algebra (ℚ_[p]) C) with
      norm_smul_le r x := by
        rw [Algebra.smul_def]
        rw [IsScalarTower.algebraMap_apply (ℚ_[p]) K C, norm_mul,
          norm_algebraMap, norm_algebraMap]
        simp only [norm_one, mul_one, le_refl] }
  let F := rationalCyclotomicSubfield (K := K) p (n + 1)
  let : NormedAlgebra (ℚ_[p]) F :=
    { (inferInstance : Algebra (ℚ_[p]) F) with
      norm_smul_le r x := by
        rw [Algebra.smul_def]
        change ‖algebraMap (ℚ_[p]) C r * (x : C)‖ ≤ ‖r‖ * ‖(x : C)‖
        rw [norm_mul, norm_algebraMap]
        simp only [norm_one, mul_one, le_refl] }
  let : NormedAlgebra F C := IntermediateField.normedAlgebraAmbient (K := ℚ_[p]) (L := C) F
  let : (spectralValuation (ℚ_[p]) F).HasExtension (spectralValuation K C) :=
    { val_isEquiv_comap := by
        intro x y
        change spectralNorm (ℚ_[p]) F x ≤ spectralNorm (ℚ_[p]) F y ↔
          spectralNorm K C (algebraMap F C x) ≤ spectralNorm K C (algebraMap F C y)
        simp only [← NormedAlgebra.norm_eq_spectralNorm (ℚ_[p]),
          ← NormedAlgebra.norm_eq_spectralNorm K, norm_algebraMap, norm_one, mul_one] }
  let : (NormedField.valuation (K := ℚ_[p])).HasExtension (spectralValuation K C) :=
    { val_isEquiv_comap := by
        intro x y
        change ‖x‖ ≤ ‖y‖ ↔
          spectralNorm K C (algebraMap (ℚ_[p]) C x) ≤ spectralNorm K C (algebraMap (ℚ_[p]) C y)
        simp only [← NormedAlgebra.norm_eq_spectralNorm K, norm_algebraMap, norm_one, mul_one] }
  let R := 𝒪[ℚ_[p]]
  let A := 𝒪[K]
  let B := spectralIntegerRing (ℚ_[p]) F
  let S := spectralIntegerRing K C
  let : FiniteDimensional (ℚ_[p]) C := FiniteDimensional.trans (ℚ_[p]) K C
  let : IsDiscreteValuationRing B := inferInstance
  let : IsDiscreteValuationRing S := inferInstance
  let : IsScalarTower A S C :=
    Valuation.HasExtension.instIsScalarTower_valuationSubring'
      (NormedField.valuation (K := K)) (spectralValuation K C)
  have hF : (IsLocalRing.maximalIdeal B).ramificationIdx R = (p ^ (n + 1)).totient := by
    exact rationalCyclotomic_ramificationIdx p n F
  have hd : Module.finrank K C ≤ (p ^ (n + 1)).totient :=
    finrank_cyclotomicLayer_le_totient (K := K) p (n + 1)
  have hdeg := local_ramificationIdx_mul_residueDegree_eq_finrank A S K C
  have htK := local_ramificationIdx_tower R A S
  have htF := local_ramificationIdx_tower R B S
  have he := local_ramificationIdx_pos A S
  have heF := local_ramificationIdx_pos B S
  have hb : (IsLocalRing.maximalIdeal S).ramificationIdx A *
      Module.finrank (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField S) ≤
        (IsLocalRing.maximalIdeal A).ramificationIdx R *
          (IsLocalRing.maximalIdeal S).ramificationIdx A := by
    calc
      _ = Module.finrank K C := hdeg
      _ ≤ (p ^ (n + 1)).totient := hd
      _ ≤ (p ^ (n + 1)).totient * (IsLocalRing.maximalIdeal S).ramificationIdx B :=
        Nat.le_mul_of_pos_right _ heF
      _ = (IsLocalRing.maximalIdeal S).ramificationIdx R := by rw [← hF, ← htF]
      _ = _ := htK
  exact Nat.le_of_mul_le_mul_left (hb.trans_eq (Nat.mul_comm _ _)) he

omit [NormedAlgebra ℚ_[p] K] [FiniteDimensional ℚ_[p] K] in
/-- Any compatible extension valuation has exactly the original spectral
integer ring, as an actual subring of the same finite cyclotomic layer. -/
theorem cyclotomicLayer_extensionValuationSubring_eq (n : ℕ)
    {Γ : Type*} [LinearOrderedCommGroupWithZero Γ]
    (w : Valuation (cyclotomicLayer (K := K) p (n + 1)) Γ)
    [(NormedField.valuation (K := K)).HasExtension w] :
    spectralIntegerRing K (cyclotomicLayer (K := K) p (n + 1)) = w.valuationSubring := by
  exact spectralIntegerRing_eq_extension_valuationSubring K _ w

end Valued

end FalseTateExtension

end
