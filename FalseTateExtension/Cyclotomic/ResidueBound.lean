/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FalseTateExtension.Cyclotomic.Ramification
public import FontaineWintenberger.Ramification.Upper.Transport
public import FontaineWintenberger.Ramification.Lower.Inertia
public import FontaineWintenberger.APF.BaseChange.UpperGroups
public import Mathlib.NumberTheory.Padics.RingHoms
public import FontaineWintenberger.LocalField.Spectral.Transport

/-!
# The residue degree of the cyclotomic layers over a finite extension of `ℚ_[p]`

Let `K/ℚ_[p]` be a finite extension with ramification index `e = e(K/ℚ_[p])`. The residue
degree of `K(ζ_{p^{n+1}})/K` is at most `e`: the subfield `ℚ_[p](ζ_{p^{n+1}})` of
`K(ζ_{p^{n+1}})` is totally ramified of degree `φ(p^{n+1})` over `ℚ_[p]`, while
`[K(ζ_{p^{n+1}}) : K] ≤ φ(p^{n+1})`. The file also records that the inertia group of
`ℚ_[p](ζ_{p^{n+1}})/ℚ_[p]` is the whole Galois group, that every `p^{n+1}`-th cyclotomic
extension of `ℚ_[p]` is totally ramified, and that the spectral integer ring of
`K(ζ_{p^{n+1}})` is the valuation ring of every valuation extending the valuation of `K`.

## Main results

* `cyclotomicLayer_padic_upper_zero`: `G^0 = G` for `ℚ_[p](ζ_{p^{n+1}})/ℚ_[p]`
* `rationalCyclotomic_ramificationIdx`: every `p^{n+1}`-th cyclotomic extension of `ℚ_[p]` has
  ramification index `φ(p^{n+1})`
* `finrank_cyclotomicLayer_le_totient`: `[K(ζ_{p^m}) : K] ≤ φ(p^m)`
* `cyclotomicLayer_spectral_residueDegree_le`: `f(K(ζ_{p^{n+1}})/K) ≤ e(K/ℚ_[p])`
* `cyclotomicLayer_extensionValuationSubring_eq`: the spectral integer ring of
  `K(ζ_{p^{n+1}})` is the valuation ring of every extension of the valuation of `K`

## References

* Serre, *Local Fields*, Chapter IV, §4, Proposition 17.
* Liu, *On lattices in semi-stable representations*, §5.1.
-/

@[expose] public section

noncomputable section

open Polynomial FontaineWintenberger

namespace FalseTateExtension

variable (p : ℕ) [Fact p.Prime]

/-- The inertia group `G^0` of `ℚ_[p](ζ_{p^{n+1}})/ℚ_[p]` is the whole Galois group. -/
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

/-- Every `p^{n+1}`-th cyclotomic extension `F/ℚ_[p]` is totally ramified: the ramification
index of the spectral integer ring of `F` over `𝒪[ℚ_[p]]` is `φ(p^{n+1})`. -/
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

/-- For `K/ℚ_[p]`, `[K(ζ_{p^m}) : K] ≤ φ(p^m)`. -/
theorem finrank_cyclotomicLayer_le_totient (m : ℕ) :
    Module.finrank K (cyclotomicLayer (K := K) p m) ≤ (p ^ m).totient := by
  have hi := (isPrimitiveRoot_zeta (K := K) p m).isIntegral
    (pow_pos (Fact.out : p.Prime).pos m)
  have hdim : Module.finrank K (cyclotomicLayer (K := K) p m) =
      (minpoly K (zeta (K := K) p m)).natDegree :=
    IntermediateField.adjoin.finrank (hi.tower_top : IsIntegral K (zeta p m))
  rw [hdim]
  have hd := minpoly.dvd_map_of_isScalarTower (ℚ_[p]) K (zeta (K := K) p m)
  rw [← (isPrimitiveRoot_zeta (K := K) p m).minpoly_eq_cyclotomic_of_irreducible
    (Padic.irreducible_cyclotomic_prime_pow p m)] at hd
  exact (Polynomial.natDegree_le_of_dvd hd ((cyclotomic.monic _ _).map _).ne_zero).trans_eq
    (by rw [Polynomial.natDegree_map, natDegree_cyclotomic])

/-- The subfield `ℚ_[p](ζ_{p^m})` of `K(ζ_{p^m})`. -/
def rationalCyclotomicSubfield (m : ℕ) :
    IntermediateField (ℚ_[p]) (cyclotomicLayer (K := K) p m) :=
  IntermediateField.adjoin (ℚ_[p])
    {(⟨zeta p m, zeta_mem_cyclotomicLayer p m⟩ : cyclotomicLayer (K := K) p m)}

omit [Algebra (ℚ_[p]) K] in
/-- `ζ_{p^m}` is a primitive `p^m`-th root of unity in `K(ζ_{p^m})`. -/
theorem isPrimitiveRoot_cyclotomicLayer_generator (m : ℕ) :
    IsPrimitiveRoot
      (⟨zeta p m, zeta_mem_cyclotomicLayer p m⟩ : cyclotomicLayer (K := K) p m)
      (p ^ m) :=
  (isPrimitiveRoot_zeta (K := K) p m).of_map_of_injective
    (f := (cyclotomicLayer (K := K) p m).val) (cyclotomicLayer p m).val.injective

variable [FiniteDimensional (ℚ_[p]) K]

/-- For `K/ℚ_[p]` finite, the subfield `ℚ_[p](ζ_{p^m})` of `K(ζ_{p^m})` is a `p^m`-th cyclotomic
extension of `ℚ_[p]`. -/
instance rationalCyclotomicSubfield_isCyclotomicExtension (m : ℕ) :
    IsCyclotomicExtension {p ^ m} (ℚ_[p]) (rationalCyclotomicSubfield (K := K) p m) := by
  have : NeZero (p ^ m) := ⟨pow_ne_zero m (Fact.out : p.Prime).ne_zero⟩
  let : FiniteDimensional (ℚ_[p]) (cyclotomicLayer (K := K) p m) :=
    FiniteDimensional.trans (ℚ_[p]) K _
  have hζ := (isPrimitiveRoot_cyclotomicLayer_generator (K := K) p m)
  exact hζ.intermediateField_adjoin_isCyclotomicExtension (ℚ_[p])

omit [FiniteDimensional (ℚ_[p]) K] in
/-- The subfield `ℚ_[p](ζ_{p^m})` of `K(ζ_{p^m})` is finite over `ℚ_[p]`. -/
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

/-- For `K/ℚ_[p]` finite, the residue degree of `K(ζ_{p^{n+1}})/K` is at most the ramification
index `e(K/ℚ_[p])`. -/
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
/-- The spectral integer ring of `K(ζ_{p^{n+1}})` is the valuation ring of every valuation on
`K(ζ_{p^{n+1}})` extending the valuation of `K`. -/
theorem cyclotomicLayer_extensionValuationSubring_eq (n : ℕ)
    {Γ : Type*} [LinearOrderedCommGroupWithZero Γ]
    (w : Valuation (cyclotomicLayer (K := K) p (n + 1)) Γ)
    [(NormedField.valuation (K := K)).HasExtension w] :
    spectralIntegerRing K (cyclotomicLayer (K := K) p (n + 1)) = w.valuationSubring := by
  exact spectralIntegerRing_eq_extension_valuationSubring K _ w

end Valued

end FalseTateExtension

end
