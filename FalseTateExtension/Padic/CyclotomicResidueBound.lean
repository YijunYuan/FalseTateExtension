module

public import FalseTateExtension.Padic.CyclotomicRamification
public import FontaineWintenberger.Ramification.FieldEquiv
public import FontaineWintenberger.Ramification.Inertia
public import FontaineWintenberger.APF.FiniteBaseChange
public import Mathlib.NumberTheory.Padics.RingHoms

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

instance padicUnitBall_residueFinite :
    Finite (IsLocalRing.ResidueField (NormedField.valuation (K := Padic p)).valuationSubring) :=
  Finite.of_injective
    ((IsLocalRing.ResidueField.mapEquiv (padicUnitBallEquiv p)).trans
      (PadicInt.residueField (p := p)))
    ((IsLocalRing.ResidueField.mapEquiv (padicUnitBallEquiv p)).trans
      (PadicInt.residueField (p := p))).injective

/-- Rational cyclotomic layers have full inertia, by the proved actual
ramification index and the actual inertia-cardinality theorem. -/
theorem cyclotomicLayer_padic_upper_zero (n : ℕ) :
    upperRamificationGroup
      (R := spectralIntegerRing (Padic p) (cyclotomicLayer (K := Padic p) p (n + 1)))
      (cyclotomicLayer (K := Padic p) p (n + 1) ≃ₐ[Padic p]
        cyclotomicLayer (K := Padic p) p (n + 1)) 0 = ⊤ := by
  rw [upperRamificationGroup_zero]
  apply Subgroup.eq_top_of_card_eq
  have h := spectralIntegerRing_card_lower_zero (Padic p)
    (cyclotomicLayer (K := Padic p) p (n + 1))
  rw [lowerRamificationGroup_zero, cyclotomicLayer_spectral_ramificationIdx] at h
  exact h.trans ((finrank_cyclotomicLayer_padic p (n + 1)).symm.trans
    (IsGalois.card_aut_eq_finrank (Padic p) (cyclotomicLayer (K := Padic p) p (n + 1))).symm)

/-- Total ramification transfers to every actual rational prime-power
cyclotomic field via its canonical field and integer-ring isomorphisms. -/
theorem rationalCyclotomic_ramificationIdx (n : ℕ)
    (F : Type*) [Field F] [Algebra (Padic p) F] [FiniteDimensional (Padic p) F]
    [IsCyclotomicExtension {p ^ (n + 1)} (Padic p) F] :
    (IsLocalRing.maximalIdeal (spectralIntegerRing (Padic p) F)).ramificationIdx
      (NormedField.valuation (K := Padic p)).valuationSubring = (p ^ (n + 1)).totient := by
  have : NeZero (p ^ (n + 1)) := ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
  have : IsGalois (Padic p) F := IsCyclotomicExtension.isGalois {p ^ (n + 1)} (Padic p) F
  let e := IsCyclotomicExtension.algEquiv {p ^ (n + 1)} (Padic p)
    (cyclotomicLayer (K := Padic p) p (n + 1)) F
  have ht : upperRamificationGroup (R := spectralIntegerRing (Padic p) F)
      (F ≃ₐ[Padic p] F) 0 = ⊤ := by
    rw [← upperRamificationGroup_map_autCongr (Padic p) e (by norm_num : (-1 : ℝ) ≤ 0),
      cyclotomicLayer_padic_upper_zero, Subgroup.map_top]
    exact MonoidHom.range_eq_top.mpr e.autCongr.surjective
  have h := spectralIntegerRing_card_lower_zero (Padic p) F
  rw [lowerRamificationGroup_zero, ← upperRamificationGroup_zero, ht,
    Subgroup.card_top, IsGalois.card_aut_eq_finrank] at h
  exact h.symm.trans (e.toLinearEquiv.finrank_eq.symm.trans (finrank_cyclotomicLayer_padic p (n + 1)))

section Fields

variable {K : Type*} [Field K] [CharZero K] [Algebra (Padic p) K]

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
  have hd := minpoly.dvd_map_of_isScalarTower (Padic p) K (rootOfUnity (K := K) p m)
  rw [Padic.minpoly_primitive_root p m (isPrimitiveRoot_rootOfUnity (K := K) p m)] at hd
  exact (Polynomial.natDegree_le_of_dvd hd ((cyclotomic.monic _ _).map _).ne_zero).trans_eq
    (by rw [Polynomial.natDegree_map, natDegree_cyclotomic])

/-- The rational cyclotomic subfield inside the same actual finite layer. -/
def rationalCyclotomicSubfield (m : ℕ) :
    IntermediateField (Padic p) (cyclotomicLayer (K := K) p m) :=
  IntermediateField.adjoin (Padic p)
    {(⟨rootOfUnity p m, rootOfUnity_mem_cyclotomicLayer p m⟩ : cyclotomicLayer (K := K) p m)}

omit [Algebra (Padic p) K] in
/-- The generator in the original finite layer remains primitive. -/
theorem isPrimitiveRoot_cyclotomicLayer_generator (m : ℕ) :
    IsPrimitiveRoot
      (⟨rootOfUnity p m, rootOfUnity_mem_cyclotomicLayer p m⟩ : cyclotomicLayer (K := K) p m)
      (p ^ m) :=
  (isPrimitiveRoot_rootOfUnity (K := K) p m).of_map_of_injective
    (f := (cyclotomicLayer (K := K) p m).val) (cyclotomicLayer p m).val.injective

variable [FiniteDimensional (Padic p) K]

instance rationalCyclotomicSubfield_isCyclotomicExtension (m : ℕ) :
    IsCyclotomicExtension {p ^ m} (Padic p) (rationalCyclotomicSubfield (K := K) p m) := by
  have : NeZero (p ^ m) := ⟨pow_ne_zero m (Fact.out : p.Prime).ne_zero⟩
  let : FiniteDimensional (Padic p) (cyclotomicLayer (K := K) p m) :=
    FiniteDimensional.trans (Padic p) K _
  exact (isPrimitiveRoot_cyclotomicLayer_generator (K := K) p m).intermediateField_adjoin_isCyclotomicExtension
    (Padic p)

omit [FiniteDimensional (Padic p) K] in
instance rationalCyclotomicSubfield_finiteDimensional (m : ℕ) :
    FiniteDimensional (Padic p) (rationalCyclotomicSubfield (K := K) p m) :=
  IntermediateField.adjoin.finiteDimensional
    (((isPrimitiveRoot_cyclotomicLayer_generator (K := K) p m).isIntegral
      (pow_pos (Fact.out : p.Prime).pos m)).tower_top)

end Fields

section Valued

variable (K : Type*) [NontriviallyNormedField K] [CharZero K]
    [IsUltrametricDist K] [CompleteSpace K]
    [NormedAlgebra (Padic p) K] [FiniteDimensional (Padic p) K]

include p in
omit [CharZero K] [CompleteSpace K] in
theorem cyclotomicBase_unitBall_isDiscreteValuationRing :
    IsDiscreteValuationRing (NormedField.valuation (K := K)).valuationSubring :=
  normedAlgebra_unitBall_isDiscreteValuationRing (Padic p) K

/-- The canonical spectral integer ring of the same actual finite layer
has residue degree bounded by the actual base ramification index. -/
theorem cyclotomicLayer_spectral_residueDegree_le (n : ℕ) :
    Module.finrank
        (IsLocalRing.ResidueField (NormedField.valuation (K := K)).valuationSubring)
        (IsLocalRing.ResidueField (spectralIntegerRing K (cyclotomicLayer (K := K) p (n + 1)))) ≤
      (IsLocalRing.maximalIdeal (NormedField.valuation (K := K)).valuationSubring).ramificationIdx
        (NormedField.valuation (K := Padic p)).valuationSubring := by
  let C := cyclotomicLayer (K := K) p (n + 1)
  let : NontriviallyNormedField C := spectralNorm.nontriviallyNormedField K C
  let : NormedAlgebra K C := spectralNorm.normedAlgebra K C
  let : IsUltrametricDist C :=
    IsUltrametricDist.isUltrametricDist_iff_isNonarchimedean_norm.mpr
      (isNonarchimedean_spectralNorm (K := K) (L := C))
  let : NormedAlgebra (Padic p) C :=
    { (inferInstance : Algebra (Padic p) C) with
      norm_smul_le r x := by
        rw [Algebra.smul_def]
        rw [IsScalarTower.algebraMap_apply (Padic p) K C, norm_mul,
          norm_algebraMap, norm_algebraMap]
        simp only [norm_one, mul_one, le_refl] }
  let F := rationalCyclotomicSubfield (K := K) p (n + 1)
  let : NormedAlgebra (Padic p) F :=
    { (inferInstance : Algebra (Padic p) F) with
      norm_smul_le r x := by
        rw [Algebra.smul_def]
        change ‖algebraMap (Padic p) C r * (x : C)‖ ≤ ‖r‖ * ‖(x : C)‖
        rw [norm_mul, norm_algebraMap]
        simp only [norm_one, mul_one, le_refl] }
  let : NormedAlgebra F C := IntermediateField.normedAlgebraAmbient (K := Padic p) (L := C) F
  let : (spectralValuation (Padic p) F).HasExtension (spectralValuation K C) :=
    { val_isEquiv_comap := by
        intro x y
        change spectralNorm (Padic p) F x ≤ spectralNorm (Padic p) F y ↔
          spectralNorm K C (algebraMap F C x) ≤ spectralNorm K C (algebraMap F C y)
        simp only [← NormedAlgebra.norm_eq_spectralNorm (Padic p),
          ← NormedAlgebra.norm_eq_spectralNorm K, norm_algebraMap, norm_one, mul_one] }
  let : (NormedField.valuation (K := Padic p)).HasExtension (spectralValuation K C) :=
    { val_isEquiv_comap := by
        intro x y
        change ‖x‖ ≤ ‖y‖ ↔
          spectralNorm K C (algebraMap (Padic p) C x) ≤ spectralNorm K C (algebraMap (Padic p) C y)
        simp only [← NormedAlgebra.norm_eq_spectralNorm K, norm_algebraMap, norm_one, mul_one] }
  let R := (NormedField.valuation (K := Padic p)).valuationSubring
  let A := (NormedField.valuation (K := K)).valuationSubring
  let B := spectralIntegerRing (Padic p) F
  let S := spectralIntegerRing K C
  let : IsDiscreteValuationRing A := cyclotomicBase_unitBall_isDiscreteValuationRing p K
  let : FiniteDimensional (Padic p) C := FiniteDimensional.trans (Padic p) K C
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

/-- Any compatible extension valuation has exactly the original spectral
integer ring, as an actual subring of the same finite cyclotomic layer. -/
theorem cyclotomicLayer_extensionValuationSubring_eq (n : ℕ)
    {Γ : Type*} [LinearOrderedCommGroupWithZero Γ]
    (w : Valuation (cyclotomicLayer (K := K) p (n + 1)) Γ)
    [(NormedField.valuation (K := K)).HasExtension w] :
    spectralIntegerRing K (cyclotomicLayer (K := K) p (n + 1)) = w.valuationSubring := by
  let : IsDiscreteValuationRing (NormedField.valuation (K := K)).valuationSubring :=
    cyclotomicBase_unitBall_isDiscreteValuationRing p K
  exact spectralIntegerRing_eq_extension_valuationSubring K _ w

/-- Equal compatible valuation subrings are identified over the original
base integer ring by the identity on the common ambient field. -/
def compatibleSpectralIntegerRingEquiv
    (L : Type*) [Field L] [Algebra K L] [FiniteDimensional K L]
    {Γ : Type*} [LinearOrderedCommGroupWithZero Γ] (w : Valuation L Γ)
    [(NormedField.valuation (K := K)).HasExtension w]
    (h : spectralIntegerRing K L = w.valuationSubring) :
    spectralIntegerRing K L ≃ₐ[(NormedField.valuation (K := K)).valuationSubring]
      w.valuationSubring := by
  let e : spectralIntegerRing K L ≃+* w.valuationSubring :=
    RingEquiv.subringCongr (congrArg ValuationSubring.toSubring h)
  exact { e with commutes' a := by apply Subtype.ext; rfl }

/-- The identity on the original field identifies the spectral integer ring
with the integer ring of every compatible extension valuation over the base. -/
def cyclotomicLayerIntegerRingEquiv (n : ℕ)
    {Γ : Type*} [LinearOrderedCommGroupWithZero Γ]
    (w : Valuation (cyclotomicLayer (K := K) p (n + 1)) Γ)
    [(NormedField.valuation (K := K)).HasExtension w] :=
  compatibleSpectralIntegerRingEquiv K _ w (cyclotomicLayer_extensionValuationSubring_eq p K n w)

@[simp]
theorem coe_cyclotomicLayerIntegerRingEquiv (n : ℕ)
    {Γ : Type*} [LinearOrderedCommGroupWithZero Γ]
    (w : Valuation (cyclotomicLayer (K := K) p (n + 1)) Γ)
    [(NormedField.valuation (K := K)).HasExtension w]
    (x : spectralIntegerRing K (cyclotomicLayer (K := K) p (n + 1))) :
    ((cyclotomicLayerIntegerRingEquiv p K n w x : w.valuationSubring) :
      cyclotomicLayer (K := K) p (n + 1)) = x := rfl

/-- The integer-ring identification induces a base-residue-field linear
isomorphism of the actual residue fields. -/
def cyclotomicLayerResidueEquiv (n : ℕ)
    {Γ : Type*} [LinearOrderedCommGroupWithZero Γ]
    (w : Valuation (cyclotomicLayer (K := K) p (n + 1)) Γ)
    [(NormedField.valuation (K := K)).HasExtension w] :
    IsLocalRing.ResidueField (spectralIntegerRing K (cyclotomicLayer (K := K) p (n + 1))) ≃ₐ[
      IsLocalRing.ResidueField (NormedField.valuation (K := K)).valuationSubring]
        IsLocalRing.ResidueField w.valuationSubring :=
  IsLocalRing.ResidueField.mapAlgEquiv' (cyclotomicLayerIntegerRingEquiv p K n w)

@[simp]
theorem cyclotomicLayerResidueEquiv_residue (n : ℕ)
    {Γ : Type*} [LinearOrderedCommGroupWithZero Γ]
    (w : Valuation (cyclotomicLayer (K := K) p (n + 1)) Γ)
    [(NormedField.valuation (K := K)).HasExtension w]
    (x : spectralIntegerRing K (cyclotomicLayer (K := K) p (n + 1))) :
    cyclotomicLayerResidueEquiv p K n w (IsLocalRing.residue _ x) =
      IsLocalRing.residue _ (cyclotomicLayerIntegerRingEquiv p K n w x) := rfl

/-- Residue degree is independent of the compatible extension valuation,
with the original base residue algebra retained. -/
theorem cyclotomicLayer_residueDegree_eq (n : ℕ)
    {Γ : Type*} [LinearOrderedCommGroupWithZero Γ]
    (w : Valuation (cyclotomicLayer (K := K) p (n + 1)) Γ)
    [(NormedField.valuation (K := K)).HasExtension w] :
    Module.finrank
        (IsLocalRing.ResidueField (NormedField.valuation (K := K)).valuationSubring)
        (IsLocalRing.ResidueField w.valuationSubring) =
      Module.finrank
        (IsLocalRing.ResidueField (NormedField.valuation (K := K)).valuationSubring)
        (IsLocalRing.ResidueField (spectralIntegerRing K (cyclotomicLayer (K := K) p (n + 1)))) :=
  (cyclotomicLayerResidueEquiv p K n w).toLinearEquiv.finrank_eq.symm

/-- For every positive cyclotomic level and every compatible extension
valuation, the actual residue degree is at most the base ramification index. -/
theorem cyclotomicLayer_residueDegree_le (n : ℕ)
    {Γ : Type*} [LinearOrderedCommGroupWithZero Γ]
    (w : Valuation (cyclotomicLayer (K := K) p (n + 1)) Γ)
    [(NormedField.valuation (K := K)).HasExtension w] :
    Module.finrank
        (IsLocalRing.ResidueField (NormedField.valuation (K := K)).valuationSubring)
        (IsLocalRing.ResidueField w.valuationSubring) ≤
      (IsLocalRing.maximalIdeal (NormedField.valuation (K := K)).valuationSubring).ramificationIdx
        (NormedField.valuation (K := Padic p)).valuationSubring := by
  rw [cyclotomicLayer_residueDegree_eq p K n w]
  exact cyclotomicLayer_spectral_residueDegree_le p K n

end Valued

end FalseTateExtension

end
