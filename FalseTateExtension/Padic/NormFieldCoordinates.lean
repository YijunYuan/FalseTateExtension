/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FalseTateExtension.StrictAPF
public import FalseTateExtension.Padic.FiniteGaloisStructure
public import FalseTateExtension.Padic.NormFieldRamification
public import FontaineWintenberger.FieldOfNorms.Structure.ResidueEmbedding
public import FontaineWintenberger.FieldOfNorms.Structure.Completeness
public import FontaineWintenberger.FieldOfNorms.Functor.Map
public import FontaineWintenberger.APF.Tower.AlgebraicResidue
public import FontaineWintenberger.LocalField.Laurent.Coordinates
public import FontaineWintenberger.Mathlib.Topology.LaurentSubstitution
public import Mathlib.RingTheory.PowerSeries.Substitution

/-!
# Actual Laurent coordinates for the original false Tate action

The intrinsic residue field is identified with the prime field using original
residue inclusions. Every chosen original norm-field uniformizer then gives
Laurent coordinates for the actual automorphism action.
-/

@[expose] public section

noncomputable section

namespace FalseTateExtension

open FontaineWintenberger WithZero
open scoped Topology PowerSeries.WithPiTopology LaurentSeries

variable (p : ℕ) [Fact p.Prime]

/-- The actual rational valuation-ring residue field is the original prime
field, through the identity-valued identification with the p-adic integers. -/
def padicUnitBallResidueEquiv :
    IsLocalRing.ResidueField (NormedField.valuation (K := Padic p)).valuationSubring ≃+*
      ZMod p :=
  (IsLocalRing.ResidueField.mapEquiv (padicUnitBallEquiv p)).trans
    (PadicInt.residueField (p := p))

variable {π : (NormedField.valuation (K := Padic p)).valuationSubring}

local notation "FT" => falseTateExtension p (π : Padic p)

local instance normFieldCoordinatesIntegralClosureValuationRing :
    ValuationRing
      (integralClosure (NormedField.valuation (K := Padic p)).valuationSubring FT) :=
  integralClosure_valuationRing (Padic p) FT

local notation "κL" => IsLocalRing.ResidueField
  (integralClosure (Valuation.valuationSubring (NormedField.valuation (K := Padic p))) FT)

/-- The intrinsic residue field of the original odd-prime false Tate field
is the prime field. Both intermediate maps are the actual residue inclusions. -/
def falseTateResidueEquiv (hp₂ : p ≠ 2) (hπ : Irreducible π) : κL ≃+* ZMod p :=
  (integralClosureSpectralResidueEquiv (Padic p) (L := FT)).toRingEquiv.trans
    ((RingEquiv.ofBijective
      (algebraMap
        (IsLocalRing.ResidueField (NormedField.valuation (K := Padic p)).valuationSubring)
        (IsLocalRing.ResidueField (spectralIntegerRing (Padic p) FT)))
      ⟨(algebraMap
          (IsLocalRing.ResidueField (NormedField.valuation (K := Padic p)).valuationSubring)
          (IsLocalRing.ResidueField (spectralIntegerRing (Padic p) FT))).injective,
        falseTateExtension_residue_algebraMap_surjective p hp₂ hπ⟩).symm.trans
      (padicUnitBallResidueEquiv p))

/-- On original base-residue constants, the intrinsic identification is
exactly the original rational residue isomorphism. -/
@[simp]
theorem falseTateResidueEquiv_algebraMap (hp₂ : p ≠ 2) (hπ : Irreducible π)
    (a : (NormedField.valuation (K := Padic p)).valuationSubring) :
    falseTateResidueEquiv p hp₂ hπ
      (IsLocalRing.residue _ (algebraMap _
        (integralClosure (NormedField.valuation (K := Padic p)).valuationSubring FT) a)) =
      padicUnitBallResidueEquiv p (IsLocalRing.residue _ a) := by
  let e := RingEquiv.ofBijective
    (algebraMap
      (IsLocalRing.ResidueField (NormedField.valuation (K := Padic p)).valuationSubring)
      (IsLocalRing.ResidueField (spectralIntegerRing (Padic p) FT)))
    ⟨(algebraMap
        (IsLocalRing.ResidueField (NormedField.valuation (K := Padic p)).valuationSubring)
        (IsLocalRing.ResidueField (spectralIntegerRing (Padic p) FT))).injective,
      falseTateExtension_residue_algebraMap_surjective p hp₂ hπ⟩
  change padicUnitBallResidueEquiv p
    (e.symm (integralClosureSpectralResidueEquiv (Padic p) (L := FT)
      (IsLocalRing.residue _ (algebraMap _ _ a)))) = _
  have heq : integralClosureSpectralResidueEquiv (Padic p) (L := FT)
      (IsLocalRing.residue _ (algebraMap _ _ a)) =
      e (IsLocalRing.residue _ a) := by
    rw [integralClosureSpectralResidueEquiv_residue,
      (integralClosureSpectralEquiv (Padic p) FT).commutes]
    rfl
  rw [heq, e.symm_apply_apply]

section OriginalCoordinates

variable (hp₂ : p ≠ 2) (hπ : Irreducible π)

local notation "NX" => FieldOfNorms (Padic p) FT
local instance normFieldCoordinatesInfinite : Fact (¬ Module.Finite (Padic p) FT) :=
  ⟨not_finiteDimensional_falseTateExtension_padic p (π : Padic p)⟩

/-- The prime-field coefficients are the actual original source constants,
under the proved intrinsic residue identification. -/
def falseTateNormCoefficients :
    letI := isAPF_falseTateExtension p hπ
    ZMod p →+* (FieldOfNorms.fieldValuation (Padic p) FT).valuationSubring := by
  have := isAPF_falseTateExtension p hπ
  exact (residueConstantsIntegerHom (Padic p) FT).comp
    (falseTateResidueEquiv p hp₂ hπ).symm.toRingHom

/-- The coefficient residue identification is induced by those same actual
constants, including the source normalization. -/
def falseTateNormCoefficientResidueEquiv :
    letI := isAPF_falseTateExtension p hπ
    ZMod p ≃+* IsLocalRing.ResidueField
      (FieldOfNorms.fieldValuation (Padic p) FT).valuationSubring := by
  have := isAPF_falseTateExtension p hπ
  exact (falseTateResidueEquiv p hp₂ hπ).symm.trans
    (FieldOfNorms.residueEquiv (Padic p) FT)

/-- Reduction of an actual prime coefficient is its actual residue image. -/
@[simp]
theorem falseTateNormCoefficientResidueEquiv_apply (a : ZMod p) :
    letI := isAPF_falseTateExtension p hπ
    falseTateNormCoefficientResidueEquiv p hp₂ hπ a =
      IsLocalRing.residue _ (falseTateNormCoefficients p hp₂ hπ a) := by
  have := isAPF_falseTateExtension p hπ
  exact FieldOfNorms.residueEquiv_apply (Padic p) FT
    ((falseTateResidueEquiv p hp₂ hπ).symm a)

/-- Every original normalized norm-family uniformizer gives actual Laurent
coordinates over the original prime field, with the source coefficients. -/
def falseTateNormFieldLaurentEquiv (u : FieldOfNorms (Padic p) FT)
    (hu : letI := isAPF_falseTateExtension p hπ
      FieldOfNorms.valuation (Padic p) FT u = exp (-1 : ℤ)) :
    letI := isAPF_falseTateExtension p hπ
    LaurentSeries (ZMod p) ≃+* NX := by
  have := isAPF_falseTateExtension p hπ
  letI : UniformSpace (ZMod p) := ⊥
  have : DiscreteUniformity (ZMod p) := inferInstance
  let ϖ : (FieldOfNorms.fieldValuation (Padic p) FT).valuationSubring :=
    ⟨u, hu.le.trans (by simp)⟩
  exact laurentUniformizerEquiv NX (falseTateNormCoefficients p hp₂ hπ)
    (falseTateNormCoefficientResidueEquiv p hp₂ hπ)
    (fun a => (falseTateNormCoefficientResidueEquiv_apply p hp₂ hπ a).symm) ϖ hu

/-- The Laurent parameter is precisely the specified original norm family. -/
@[simp]
theorem falseTateNormFieldLaurentEquiv_X (u : FieldOfNorms (Padic p) FT)
    (hu : letI := isAPF_falseTateExtension p hπ
      FieldOfNorms.valuation (Padic p) FT u = exp (-1 : ℤ)) :
    letI := isAPF_falseTateExtension p hπ
    falseTateNormFieldLaurentEquiv p hp₂ hπ u hu
      (algebraMap (PowerSeries (ZMod p)) (LaurentSeries (ZMod p)) PowerSeries.X) = u := by
  have := isAPF_falseTateExtension p hπ
  let : UniformSpace (ZMod p) := ⊥
  have : DiscreteUniformity (ZMod p) := inferInstance
  exact laurentUniformizerEquiv_X NX _ _ _ _ _

/-- Laurent constants are the prescribed original source coefficients. -/
@[simp]
theorem falseTateNormFieldLaurentEquiv_C (u : FieldOfNorms (Padic p) FT)
    (hu : letI := isAPF_falseTateExtension p hπ
      FieldOfNorms.valuation (Padic p) FT u = exp (-1 : ℤ)) (a : ZMod p) :
    letI := isAPF_falseTateExtension p hπ
    falseTateNormFieldLaurentEquiv p hp₂ hπ u hu
      (algebraMap (ZMod p) (LaurentSeries (ZMod p)) a) =
      (falseTateNormCoefficients p hp₂ hπ a : NX) := by
  have := isAPF_falseTateExtension p hπ
  let : UniformSpace (ZMod p) := ⊥
  have : DiscreteUniformity (ZMod p) := inferInstance
  exact laurentUniformizerEquiv_C NX _ _ _ _ _ a

/-- These coordinates preserve the actual stable valuation on every Laurent
series, including zero and negative orders. -/
theorem valuation_falseTateNormFieldLaurentEquiv (u : FieldOfNorms (Padic p) FT)
    (hu : letI := isAPF_falseTateExtension p hπ
      FieldOfNorms.valuation (Padic p) FT u = exp (-1 : ℤ))
    (A : LaurentSeries (ZMod p)) :
    letI := isAPF_falseTateExtension p hπ
    FieldOfNorms.valuation (Padic p) FT (falseTateNormFieldLaurentEquiv p hp₂ hπ u hu A) =
      (Valued.v A : WithZero (Multiplicative ℤ)) := by
  have := isAPF_falseTateExtension p hπ
  let : UniformSpace (ZMod p) := ⊥
  have : DiscreteUniformity (ZMod p) := inferInstance
  exact valuation_laurentUniformizerEquiv NX _ _ _ _ _ A

/-- Continuity uses the original valuation uniformity on the norm field. -/
theorem uniformContinuous_falseTateNormFieldLaurentEquiv (u : FieldOfNorms (Padic p) FT)
    (hu : letI := isAPF_falseTateExtension p hπ
      FieldOfNorms.valuation (Padic p) FT u = exp (-1 : ℤ)) :
    letI := isAPF_falseTateExtension p hπ
    UniformContinuous (falseTateNormFieldLaurentEquiv p hp₂ hπ u hu) := by
  have := isAPF_falseTateExtension p hπ
  apply valuedRingEquiv_uniformContinuous
  exact valuation_falseTateNormFieldLaurentEquiv p hp₂ hπ u hu

/-- The inverse coordinate expansion preserves the same original uniformities. -/
theorem uniformContinuous_falseTateNormFieldLaurentEquiv_symm (u : FieldOfNorms (Padic p) FT)
    (hu : letI := isAPF_falseTateExtension p hπ
      FieldOfNorms.valuation (Padic p) FT u = exp (-1 : ℤ)) :
    letI := isAPF_falseTateExtension p hπ
    UniformContinuous (falseTateNormFieldLaurentEquiv p hp₂ hπ u hu).symm := by
  have := isAPF_falseTateExtension p hπ
  let e := falseTateNormFieldLaurentEquiv p hp₂ hπ u hu
  apply valuedRingEquiv_uniformContinuous
  intro x
  exact (valuation_falseTateNormFieldLaurentEquiv p hp₂ hπ u hu (e.symm x)).symm.trans
    (congrArg (FieldOfNorms.valuation (Padic p) FT) (e.apply_symm_apply x))

/-- Conjugation transports the literal original norm-field action to the
actual Laurent field. Multiplication is ordinary composition of automorphisms. -/
def falseTateLaurentAction (u : FieldOfNorms (Padic p) FT)
    (hu : letI := isAPF_falseTateExtension p hπ
      FieldOfNorms.valuation (Padic p) FT u = exp (-1 : ℤ)) :
    letI := isAPF_falseTateExtension p hπ
    (FT ≃ₐ[Padic p] FT) →* (LaurentSeries (ZMod p) ≃+* LaurentSeries (ZMod p)) := by
  have := isAPF_falseTateExtension p hπ
  let e := falseTateNormFieldLaurentEquiv p hp₂ hπ u hu
  let a := FieldOfNorms.aut (Padic p) FT
  exact {
    toFun := fun g => (e.trans (a g)).trans e.symm
    map_one' := by
      apply RingEquiv.ext
      intro A
      change e.symm (a 1 (e A)) = A
      rw [map_one]
      exact e.symm_apply_apply A
    map_mul' := by
      intro g h
      apply RingEquiv.ext
      intro A
      change e.symm (a (g * h) (e A)) = e.symm (a g (e (e.symm (a h (e A)))))
      rw [map_mul, e.apply_symm_apply]
      rfl }

/-- The Laurent action is exactly conjugation by the original evaluation map. -/
theorem falseTateLaurentAction_apply (u : FieldOfNorms (Padic p) FT)
    (hu : letI := isAPF_falseTateExtension p hπ
      FieldOfNorms.valuation (Padic p) FT u = exp (-1 : ℤ))
    (g : FT ≃ₐ[Padic p] FT) (A : LaurentSeries (ZMod p)) :
    letI := isAPF_falseTateExtension p hπ
    falseTateLaurentAction p hp₂ hπ u hu g A =
      (falseTateNormFieldLaurentEquiv p hp₂ hπ u hu).symm
        (FieldOfNorms.aut (Padic p) FT g
          (falseTateNormFieldLaurentEquiv p hp₂ hπ u hu A)) := by
  have := isAPF_falseTateExtension p hπ
  rfl

/-- Conjugating the original action preserves the original Laurent valuation. -/
theorem valuation_falseTateLaurentAction (u : FieldOfNorms (Padic p) FT)
    (hu : letI := isAPF_falseTateExtension p hπ
      FieldOfNorms.valuation (Padic p) FT u = exp (-1 : ℤ))
    (g : FT ≃ₐ[Padic p] FT) (A : LaurentSeries (ZMod p)) :
    letI := isAPF_falseTateExtension p hπ
    (Valued.v (falseTateLaurentAction p hp₂ hπ u hu g A) : WithZero (Multiplicative ℤ)) =
      Valued.v A := by
  have := isAPF_falseTateExtension p hπ
  let e := falseTateNormFieldLaurentEquiv p hp₂ hπ u hu
  calc
    _ = FieldOfNorms.valuation (Padic p) FT
        (e (falseTateLaurentAction p hp₂ hπ u hu g A)) :=
      (valuation_falseTateNormFieldLaurentEquiv p hp₂ hπ u hu _).symm
    _ = FieldOfNorms.valuation (Padic p) FT
        (FieldOfNorms.aut (Padic p) FT g (e A)) := by
      rw [falseTateLaurentAction_apply, e.apply_symm_apply]
    _ = FieldOfNorms.valuation (Padic p) FT (e A) :=
      FieldOfNorms.aut_valuation (Padic p) g (e A)
    _ = Valued.v A := valuation_falseTateNormFieldLaurentEquiv p hp₂ hπ u hu A

/-- Each Laurent automorphism is continuous for the original valuation topology. -/
theorem uniformContinuous_falseTateLaurentAction (u : FieldOfNorms (Padic p) FT)
    (hu : letI := isAPF_falseTateExtension p hπ
      FieldOfNorms.valuation (Padic p) FT u = exp (-1 : ℤ))
    (g : FT ≃ₐ[Padic p] FT) :
    letI := isAPF_falseTateExtension p hπ
    UniformContinuous (falseTateLaurentAction p hp₂ hπ u hu g) := by
  have := isAPF_falseTateExtension p hπ
  apply valuedRingEquiv_uniformContinuous
  exact valuation_falseTateLaurentAction p hp₂ hπ u hu g

/-- Every actual automorphism fixes the original prime-field coefficients. -/
@[simp]
theorem falseTateLaurentAction_C (u : FieldOfNorms (Padic p) FT)
    (hu : letI := isAPF_falseTateExtension p hπ
      FieldOfNorms.valuation (Padic p) FT u = exp (-1 : ℤ))
    (g : FT ≃ₐ[Padic p] FT) (a : ZMod p) :
    letI := isAPF_falseTateExtension p hπ
    falseTateLaurentAction p hp₂ hπ u hu g
        (algebraMap (ZMod p) (LaurentSeries (ZMod p)) a) =
      algebraMap (ZMod p) (LaurentSeries (ZMod p)) a := by
  have := isAPF_falseTateExtension p hπ
  exact DFunLike.congr_fun
    (Subsingleton.elim
      ((falseTateLaurentAction p hp₂ hπ u hu g).toRingHom.comp
        (algebraMap (ZMod p) (LaurentSeries (ZMod p))))
      (algebraMap (ZMod p) (LaurentSeries (ZMod p)))) a

/-- The actual image of the parameter is a power-series coordinate with
zero constant coefficient and invertible linear coefficient. -/
theorem exists_falseTatePowerSeriesCoordinate (u : FieldOfNorms (Padic p) FT)
    (hu : letI := isAPF_falseTateExtension p hπ
      FieldOfNorms.valuation (Padic p) FT u = exp (-1 : ℤ))
    (g : FT ≃ₐ[Padic p] FT) :
    letI := isAPF_falseTateExtension p hπ
    ∃ f : PowerSeries (ZMod p),
      (f : LaurentSeries (ZMod p)) = falseTateLaurentAction p hp₂ hπ u hu g
          (HahnSeries.single (1 : ℤ) 1) ∧
        f.constantCoeff = 0 ∧ IsUnit (f.coeff 1) := by
  have := isAPF_falseTateExtension p hπ
  have hX : (Valued.v (HahnSeries.single (1 : ℤ) (1 : ZMod p)) :
      WithZero (Multiplicative ℤ)) = exp (-1 : ℤ) := by
    simpa using LaurentSeries.valuation_X_pow (ZMod p) 1
  have hv : (Valued.v (falseTateLaurentAction p hp₂ hπ u hu g
      (HahnSeries.single (1 : ℤ) 1)) : WithZero (Multiplicative ℤ)) = exp (-1 : ℤ) :=
    (valuation_falseTateLaurentAction p hp₂ hπ u hu g _).trans hX
  have hle : exp (-1 : ℤ) ≤ (1 : WithZero (Multiplicative ℤ)) := by
    rw [← WithZero.exp_zero]
    exact WithZero.exp_le_exp.mpr (by omega)
  obtain ⟨f, hf⟩ := (LaurentSeries.val_le_one_iff_eq_coe (ZMod p) _).mp (hv.le.trans hle)
  have hvf : (Valued.v (f : LaurentSeries (ZMod p)) : WithZero (Multiplicative ℤ)) =
      exp (-1 : ℤ) := by rw [hf]; exact hv
  have hzero : f.constantCoeff = 0 := by
    have hc := LaurentSeries.coeff_zero_of_lt_valuation (ZMod p) hvf.le
      (show (0 : ℤ) < 1 by omega)
    simpa [PowerSeries.coeff_coe] using hc
  have hlinear : f.coeff 1 ≠ 0 := by
    intro hlinear
    have hcoeff (n : ℤ) (hn : n < 2) : (f : LaurentSeries (ZMod p)).coeff n = 0 := by
      by_cases hn0 : n < 0
      · rw [PowerSeries.coeff_coe]
        simp only [hn0, ite_true]
      · rcases (show n = 0 ∨ n = 1 by omega) with rfl | rfl
        · simpa [PowerSeries.coeff_coe] using hzero
        · simpa [PowerSeries.coeff_coe] using hlinear
    have hbound : (Valued.v (f : LaurentSeries (ZMod p)) : WithZero (Multiplicative ℤ)) ≤
        exp (-2 : ℤ) :=
      (LaurentSeries.valuation_le_iff_coeff_lt_eq_zero (ZMod p)).mpr hcoeff
    rw [hvf] at hbound
    exact not_le_of_gt (WithZero.exp_lt_exp.mpr (by omega : (-2 : ℤ) < -1)) hbound
  exact ⟨f, hf, hzero, isUnit_iff_ne_zero.mpr hlinear⟩

/-- The actual power-series coordinate of an original false Tate automorphism. -/
def falseTatePowerSeriesCoordinate (u : FieldOfNorms (Padic p) FT)
    (hu : letI := isAPF_falseTateExtension p hπ
      FieldOfNorms.valuation (Padic p) FT u = exp (-1 : ℤ))
    (g : FT ≃ₐ[Padic p] FT) :
    letI := isAPF_falseTateExtension p hπ
    PowerSeries (ZMod p) := by
  have := isAPF_falseTateExtension p hπ
  exact (exists_falseTatePowerSeriesCoordinate p hp₂ hπ u hu g).choose

/-- Its Laurent image is exactly the image of the original parameter under
the original action in the original coordinates. -/
theorem coe_falseTatePowerSeriesCoordinate (u : FieldOfNorms (Padic p) FT)
    (hu : letI := isAPF_falseTateExtension p hπ
      FieldOfNorms.valuation (Padic p) FT u = exp (-1 : ℤ))
    (g : FT ≃ₐ[Padic p] FT) :
    letI := isAPF_falseTateExtension p hπ
    (falseTatePowerSeriesCoordinate p hp₂ hπ u hu g : LaurentSeries (ZMod p)) =
      falseTateLaurentAction p hp₂ hπ u hu g (HahnSeries.single (1 : ℤ) 1) := by
  have := isAPF_falseTateExtension p hπ
  exact (exists_falseTatePowerSeriesCoordinate p hp₂ hπ u hu g).choose_spec.1

@[simp]
theorem falseTatePowerSeriesCoordinate_constantCoeff (u : FieldOfNorms (Padic p) FT)
    (hu : letI := isAPF_falseTateExtension p hπ
      FieldOfNorms.valuation (Padic p) FT u = exp (-1 : ℤ))
    (g : FT ≃ₐ[Padic p] FT) :
    letI := isAPF_falseTateExtension p hπ
    (falseTatePowerSeriesCoordinate p hp₂ hπ u hu g).constantCoeff = 0 := by
  have := isAPF_falseTateExtension p hπ
  exact (exists_falseTatePowerSeriesCoordinate p hp₂ hπ u hu g).choose_spec.2.1

/-- The linear coefficient is a unit in the original prime field. -/
theorem falseTatePowerSeriesCoordinate_linear_isUnit (u : FieldOfNorms (Padic p) FT)
    (hu : letI := isAPF_falseTateExtension p hπ
      FieldOfNorms.valuation (Padic p) FT u = exp (-1 : ℤ))
    (g : FT ≃ₐ[Padic p] FT) :
    letI := isAPF_falseTateExtension p hπ
    IsUnit ((falseTatePowerSeriesCoordinate p hp₂ hπ u hu g).coeff 1) := by
  have := isAPF_falseTateExtension p hπ
  exact (exists_falseTatePowerSeriesCoordinate p hp₂ hπ u hu g).choose_spec.2.2

/-- The actual coordinate represents precisely the original image of the
specified norm-family uniformizer, as required in the lifting definition. -/
theorem falseTateNormFieldLaurentEquiv_powerSeriesCoordinate (u : FieldOfNorms (Padic p) FT)
    (hu : letI := isAPF_falseTateExtension p hπ
      FieldOfNorms.valuation (Padic p) FT u = exp (-1 : ℤ))
    (g : FT ≃ₐ[Padic p] FT) :
    letI := isAPF_falseTateExtension p hπ
    falseTateNormFieldLaurentEquiv p hp₂ hπ u hu
        (falseTatePowerSeriesCoordinate p hp₂ hπ u hu g : LaurentSeries (ZMod p)) =
      FieldOfNorms.aut (Padic p) FT g u := by
  have := isAPF_falseTateExtension p hπ
  let e := falseTateNormFieldLaurentEquiv p hp₂ hπ u hu
  rw [coe_falseTatePowerSeriesCoordinate, falseTateLaurentAction_apply]
  rw [e.apply_symm_apply]
  have hX : e (HahnSeries.single (1 : ℤ) 1) = u := by
    simpa only [LaurentSeries.coe_algebraMap, HahnSeries.ofPowerSeries_X] using
      falseTateNormFieldLaurentEquiv_X p hp₂ hπ u hu
  rw [hX]

/-- The identity automorphism has exactly the original parameter as coordinate. -/
@[simp]
theorem falseTatePowerSeriesCoordinate_one (u : FieldOfNorms (Padic p) FT)
    (hu : letI := isAPF_falseTateExtension p hπ
      FieldOfNorms.valuation (Padic p) FT u = exp (-1 : ℤ)) :
    letI := isAPF_falseTateExtension p hπ
    falseTatePowerSeriesCoordinate p hp₂ hπ u hu 1 = PowerSeries.X := by
  have := isAPF_falseTateExtension p hπ
  apply HahnSeries.ofPowerSeries_injective (Γ := ℤ)
  rw [coe_falseTatePowerSeriesCoordinate, map_one]
  exact (HahnSeries.ofPowerSeries_X).symm

/-- On every power-series input, the original action is ordinary substitution
at its actual parameter image. -/
theorem falseTateLaurentAction_powerSeries (u : FieldOfNorms (Padic p) FT)
    (hu : letI := isAPF_falseTateExtension p hπ
      FieldOfNorms.valuation (Padic p) FT u = exp (-1 : ℤ))
    (g : FT ≃ₐ[Padic p] FT) (A : PowerSeries (ZMod p)) :
    letI := isAPF_falseTateExtension p hπ
    falseTateLaurentAction p hp₂ hπ u hu g (A : LaurentSeries (ZMod p)) =
      (A.subst (falseTatePowerSeriesCoordinate p hp₂ hπ u hu g) :
        LaurentSeries (ZMod p)) := by
  have := isAPF_falseTateExtension p hπ
  exact map_ofPowerSeries_eq_subst
    (falseTateLaurentAction p hp₂ hπ u hu g).toRingHom
    (uniformContinuous_falseTateLaurentAction p hp₂ hπ u hu g).continuous
    (fun a => by simpa only [LaurentSeries.algebraMap_apply,
      RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom] using
      falseTateLaurentAction_C p hp₂ hπ u hu g a)
    (falseTatePowerSeriesCoordinate p hp₂ hπ u hu g)
    (falseTatePowerSeriesCoordinate_constantCoeff p hp₂ hπ u hu g)
    (coe_falseTatePowerSeriesCoordinate p hp₂ hπ u hu g).symm A

/-- Ordinary composition of the actual automorphisms gives the reversed
composition law for their original power-series coordinates. -/
theorem falseTatePowerSeriesCoordinate_mul (u : FieldOfNorms (Padic p) FT)
    (hu : letI := isAPF_falseTateExtension p hπ
      FieldOfNorms.valuation (Padic p) FT u = exp (-1 : ℤ))
    (g h : FT ≃ₐ[Padic p] FT) :
    letI := isAPF_falseTateExtension p hπ
    falseTatePowerSeriesCoordinate p hp₂ hπ u hu (g * h) =
      (falseTatePowerSeriesCoordinate p hp₂ hπ u hu h).subst
        (falseTatePowerSeriesCoordinate p hp₂ hπ u hu g) := by
  have := isAPF_falseTateExtension p hπ
  apply HahnSeries.ofPowerSeries_injective (Γ := ℤ)
  rw [coe_falseTatePowerSeriesCoordinate, map_mul]
  change falseTateLaurentAction p hp₂ hπ u hu g
    (falseTateLaurentAction p hp₂ hπ u hu h (HahnSeries.single (1 : ℤ) 1)) = _
  rw [← coe_falseTatePowerSeriesCoordinate, falseTateLaurentAction_powerSeries]

/-- Every actual group power is represented by the ordinary iterate of the
same actual power-series substitution. -/
theorem falseTatePowerSeriesCoordinate_pow (u : FieldOfNorms (Padic p) FT)
    (hu : letI := isAPF_falseTateExtension p hπ
      FieldOfNorms.valuation (Padic p) FT u = exp (-1 : ℤ))
    (g : FT ≃ₐ[Padic p] FT) (n : ℕ) :
    letI := isAPF_falseTateExtension p hπ
    falseTatePowerSeriesCoordinate p hp₂ hπ u hu (g ^ n) =
      (PowerSeries.subst (falseTatePowerSeriesCoordinate p hp₂ hπ u hu g) :
        PowerSeries (ZMod p) → PowerSeries (ZMod p))^[n] PowerSeries.X := by
  have := isAPF_falseTateExtension p hπ
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', falseTatePowerSeriesCoordinate_mul, ih, Function.iterate_succ_apply']

/-- The original continuous field coordinate map is uniquely determined by
the original source constants and chosen original uniformizer. -/
theorem falseTateNormFieldLaurentEquiv_unique (u : FieldOfNorms (Padic p) FT)
    (hu : letI := isAPF_falseTateExtension p hπ
      FieldOfNorms.valuation (Padic p) FT u = exp (-1 : ℤ)) :
    letI := isAPF_falseTateExtension p hπ
    ∀ f : LaurentSeries (ZMod p) →+* NX, Continuous f →
      (∀ a, f (algebraMap (ZMod p) (LaurentSeries (ZMod p)) a) =
        (falseTateNormCoefficients p hp₂ hπ a : NX)) →
      f (algebraMap (PowerSeries (ZMod p)) (LaurentSeries (ZMod p)) PowerSeries.X) = u →
      f = (falseTateNormFieldLaurentEquiv p hp₂ hπ u hu).toRingHom := by
  have := isAPF_falseTateExtension p hπ
  let : UniformSpace (ZMod p) := ⊥
  have : DiscreteUniformity (ZMod p) := inferInstance
  intro f hf hC hX
  exact laurentUniformizerEquiv_unique NX _ _ _ _ _ f hf hC hX

/-- The coordinate displacement has exactly the valuation of the actual
original norm-field displacement, for every original automorphism. -/
theorem valuation_falseTatePowerSeriesCoordinate_displacement (u : FieldOfNorms (Padic p) FT)
    (hu : letI := isAPF_falseTateExtension p hπ
      FieldOfNorms.valuation (Padic p) FT u = exp (-1 : ℤ))
    (g : FT ≃ₐ[Padic p] FT) :
    letI := isAPF_falseTateExtension p hπ
    (Valued.v ((falseTatePowerSeriesCoordinate p hp₂ hπ u hu g : LaurentSeries (ZMod p)) -
      HahnSeries.single (1 : ℤ) 1) : WithZero (Multiplicative ℤ)) =
      FieldOfNorms.valuation (Padic p) FT (FieldOfNorms.aut (Padic p) FT g u - u) := by
  have := isAPF_falseTateExtension p hπ
  let e := falseTateNormFieldLaurentEquiv p hp₂ hπ u hu
  have hX : e (HahnSeries.single (1 : ℤ) 1) = u := by
    simpa only [LaurentSeries.coe_algebraMap, HahnSeries.ofPowerSeries_X] using
      falseTateNormFieldLaurentEquiv_X p hp₂ hπ u hu
  have hf : e (falseTatePowerSeriesCoordinate p hp₂ hπ u hu g : LaurentSeries (ZMod p)) =
      FieldOfNorms.aut (Padic p) FT g u :=
    falseTateNormFieldLaurentEquiv_powerSeriesCoordinate p hp₂ hπ u hu g
  calc
    _ = FieldOfNorms.valuation (Padic p) FT
        (e ((falseTatePowerSeriesCoordinate p hp₂ hπ u hu g : LaurentSeries (ZMod p)) -
          HahnSeries.single (1 : ℤ) 1)) :=
      (valuation_falseTateNormFieldLaurentEquiv p hp₂ hπ u hu _).symm
    _ = FieldOfNorms.valuation (Padic p) FT
        (e (falseTatePowerSeriesCoordinate p hp₂ hπ u hu g : LaurentSeries (ZMod p)) -
          e (HahnSeries.single (1 : ℤ) 1)) := congrArg _ (map_sub e _ _)
    _ = _ := congrArg (FieldOfNorms.valuation (Padic p) FT)
      (congrArg₂ (fun x y : NX => x - y) hf hX)

end OriginalCoordinates

end FalseTateExtension
