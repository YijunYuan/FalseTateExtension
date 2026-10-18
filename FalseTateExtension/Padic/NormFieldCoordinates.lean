module

public import FalseTateExtension.StrictAPF
public import FalseTateExtension.Padic.FiniteGaloisStructure
public import FalseTateExtension.Padic.NormFieldRamification
public import FontaineWintenberger.FieldOfNorms.Constants
public import FontaineWintenberger.FieldOfNorms.Completeness
public import FontaineWintenberger.FieldOfNorms.Isomorphism
public import FontaineWintenberger.LocalField.AlgebraicResidue
public import FontaineWintenberger.LocalField.LaurentCoordinates
public import FontaineWintenberger.LocalField.LaurentSubstitution
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

local instance normFieldCoordinatesResidueCharP :
    CharP (IsLocalRing.ResidueField
      (NormedField.valuation (K := Padic p)).valuationSubring) p where
  cast_eq_zero_iff n := by
    rw [← (padicUnitBallResidueEquiv p).injective.eq_iff, map_natCast, map_zero]
    exact CharP.cast_eq_zero_iff (ZMod p) p n

local instance normFieldCoordinatesResiduePerfect :
    PerfectField (IsLocalRing.ResidueField
      (NormedField.valuation (K := Padic p)).valuationSubring) :=
  PerfectField.of_ringEquiv (padicUnitBallResidueEquiv p).symm

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

local notation "NX" => NormLimit (Padic p) FT
local notation "hFT" => isAPF_falseTateExtension p hπ
local notation "hInf" => not_finiteDimensional_falseTateExtension_padic p (π : Padic p)

/-- The prime-field coefficients are the actual original source constants,
under the proved intrinsic residue identification. -/
def falseTateNormCoefficients :
    letI := normLimitField (Padic p) FT p hFT hInf
    ZMod p →+* (normLimitFieldValuation (Padic p) FT p hFT hInf).valuationSubring := by
  letI := normLimitField (Padic p) FT p hFT hInf
  exact (sourceResidueConstantsIntegerHom (Padic p) FT p hFT hInf).comp
    (falseTateResidueEquiv p hp₂ hπ).symm.toRingHom

/-- The coefficient residue identification is induced by those same actual
constants, including the source normalization. -/
def falseTateNormCoefficientResidueEquiv :
    letI := normLimitField (Padic p) FT p hFT hInf
    ZMod p ≃+* IsLocalRing.ResidueField
      (normLimitFieldValuation (Padic p) FT p hFT hInf).valuationSubring := by
  letI := normLimitField (Padic p) FT p hFT hInf
  exact (falseTateResidueEquiv p hp₂ hπ).symm.trans
    (sourceResidueConstantsResidueEquiv (Padic p) FT p hFT hInf)

/-- Reduction of an actual prime coefficient is its actual residue image. -/
@[simp]
theorem falseTateNormCoefficientResidueEquiv_apply (a : ZMod p) :
    letI := normLimitField (Padic p) FT p hFT hInf
    falseTateNormCoefficientResidueEquiv p hp₂ hπ a =
      IsLocalRing.residue _ (falseTateNormCoefficients p hp₂ hπ a) := by
  let := normLimitField (Padic p) FT p hFT hInf
  exact sourceResidueConstantsResidueEquiv_apply (Padic p) FT p hFT hInf
    ((falseTateResidueEquiv p hp₂ hπ).symm a)

/-- Every original normalized norm-family uniformizer gives actual Laurent
coordinates over the original prime field, with the source coefficients. -/
def falseTateNormFieldLaurentEquiv (u : NormLimit (Padic p) FT)
    (hu : normLimitValuation (Padic p) FT hFT u = exp (-1 : ℤ)) :
    letI := normLimitField (Padic p) FT p hFT hInf
    LaurentSeries (ZMod p) ≃+* NX := by
  letI := normLimitField (Padic p) FT p hFT hInf
  letI := normLimitValued (Padic p) FT p hFT hInf
  letI := normLimit_completeSpace (Padic p) FT p hFT hInf
  letI : UniformSpace (ZMod p) := ⊥
  letI : DiscreteUniformity (ZMod p) := inferInstance
  let ϖ : (normLimitFieldValuation (Padic p) FT p hFT hInf).valuationSubring :=
    ⟨u, hu.le.trans (by simp)⟩
  exact laurentUniformizerEquiv NX (falseTateNormCoefficients p hp₂ hπ)
    (falseTateNormCoefficientResidueEquiv p hp₂ hπ)
    (fun a => (falseTateNormCoefficientResidueEquiv_apply p hp₂ hπ a).symm) ϖ hu

/-- The Laurent parameter is precisely the specified original norm family. -/
@[simp]
theorem falseTateNormFieldLaurentEquiv_X (u : NormLimit (Padic p) FT)
    (hu : normLimitValuation (Padic p) FT hFT u = exp (-1 : ℤ)) :
    letI := normLimitField (Padic p) FT p hFT hInf
    falseTateNormFieldLaurentEquiv p hp₂ hπ u hu
      (algebraMap (PowerSeries (ZMod p)) (LaurentSeries (ZMod p)) PowerSeries.X) = u := by
  let := normLimitField (Padic p) FT p hFT hInf
  let := normLimitValued (Padic p) FT p hFT hInf
  let := normLimit_completeSpace (Padic p) FT p hFT hInf
  let : UniformSpace (ZMod p) := ⊥
  let : DiscreteUniformity (ZMod p) := inferInstance
  exact laurentUniformizerEquiv_X NX _ _ _ _ _

/-- Laurent constants are the prescribed original source coefficients. -/
@[simp]
theorem falseTateNormFieldLaurentEquiv_C (u : NormLimit (Padic p) FT)
    (hu : normLimitValuation (Padic p) FT hFT u = exp (-1 : ℤ)) (a : ZMod p) :
    letI := normLimitField (Padic p) FT p hFT hInf
    falseTateNormFieldLaurentEquiv p hp₂ hπ u hu
      (algebraMap (ZMod p) (LaurentSeries (ZMod p)) a) =
      (falseTateNormCoefficients p hp₂ hπ a : NX) := by
  let := normLimitField (Padic p) FT p hFT hInf
  let := normLimitValued (Padic p) FT p hFT hInf
  let := normLimit_completeSpace (Padic p) FT p hFT hInf
  let : UniformSpace (ZMod p) := ⊥
  let : DiscreteUniformity (ZMod p) := inferInstance
  exact laurentUniformizerEquiv_C NX _ _ _ _ _ a

/-- These coordinates preserve the actual stable valuation on every Laurent
series, including zero and negative orders. -/
theorem valuation_falseTateNormFieldLaurentEquiv (u : NormLimit (Padic p) FT)
    (hu : normLimitValuation (Padic p) FT hFT u = exp (-1 : ℤ))
    (A : LaurentSeries (ZMod p)) :
    letI := normLimitField (Padic p) FT p hFT hInf
    normLimitValuation (Padic p) FT hFT (falseTateNormFieldLaurentEquiv p hp₂ hπ u hu A) =
      (Valued.v A : WithZero (Multiplicative ℤ)) := by
  let := normLimitField (Padic p) FT p hFT hInf
  let := normLimitValued (Padic p) FT p hFT hInf
  let := normLimit_completeSpace (Padic p) FT p hFT hInf
  let : UniformSpace (ZMod p) := ⊥
  let : DiscreteUniformity (ZMod p) := inferInstance
  exact valuation_laurentUniformizerEquiv NX _ _ _ _ _ A

/-- Continuity uses the original valuation uniformity on the norm field. -/
theorem uniformContinuous_falseTateNormFieldLaurentEquiv (u : NormLimit (Padic p) FT)
    (hu : normLimitValuation (Padic p) FT hFT u = exp (-1 : ℤ)) :
    letI := normLimitField (Padic p) FT p hFT hInf
    letI := normLimitValued (Padic p) FT p hFT hInf
    UniformContinuous (falseTateNormFieldLaurentEquiv p hp₂ hπ u hu) := by
  let := normLimitField (Padic p) FT p hFT hInf
  let := normLimitValued (Padic p) FT p hFT hInf
  apply valuedRingEquiv_uniformContinuous
  exact valuation_falseTateNormFieldLaurentEquiv p hp₂ hπ u hu

/-- The inverse coordinate expansion preserves the same original uniformities. -/
theorem uniformContinuous_falseTateNormFieldLaurentEquiv_symm (u : NormLimit (Padic p) FT)
    (hu : normLimitValuation (Padic p) FT hFT u = exp (-1 : ℤ)) :
    letI := normLimitField (Padic p) FT p hFT hInf
    letI := normLimitValued (Padic p) FT p hFT hInf
    UniformContinuous (falseTateNormFieldLaurentEquiv p hp₂ hπ u hu).symm := by
  let := normLimitField (Padic p) FT p hFT hInf
  let := normLimitValued (Padic p) FT p hFT hInf
  let e := falseTateNormFieldLaurentEquiv p hp₂ hπ u hu
  apply valuedRingEquiv_uniformContinuous
  intro x
  exact (valuation_falseTateNormFieldLaurentEquiv p hp₂ hπ u hu (e.symm x)).symm.trans
    (congrArg (normLimitValuation (Padic p) FT hFT) (e.apply_symm_apply x))

/-- Conjugation transports the literal original norm-field action to the
actual Laurent field. Multiplication is ordinary composition of automorphisms. -/
def falseTateLaurentAction (u : NormLimit (Padic p) FT)
    (hu : normLimitValuation (Padic p) FT hFT u = exp (-1 : ℤ)) :
    (FT ≃ₐ[Padic p] FT) →* (LaurentSeries (ZMod p) ≃+* LaurentSeries (ZMod p)) := by
  letI := normLimitField (Padic p) FT p hFT hInf
  let e := falseTateNormFieldLaurentEquiv p hp₂ hπ u hu
  let a := normLimitAut (Padic p) p hFT hInf
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
theorem falseTateLaurentAction_apply (u : NormLimit (Padic p) FT)
    (hu : normLimitValuation (Padic p) FT hFT u = exp (-1 : ℤ))
    (g : FT ≃ₐ[Padic p] FT) (A : LaurentSeries (ZMod p)) :
    letI := normLimitField (Padic p) FT p hFT hInf
    falseTateLaurentAction p hp₂ hπ u hu g A =
      (falseTateNormFieldLaurentEquiv p hp₂ hπ u hu).symm
        (normLimitAut (Padic p) p hFT hInf g
          (falseTateNormFieldLaurentEquiv p hp₂ hπ u hu A)) := rfl

/-- Conjugating the original action preserves the original Laurent valuation. -/
theorem valuation_falseTateLaurentAction (u : NormLimit (Padic p) FT)
    (hu : normLimitValuation (Padic p) FT hFT u = exp (-1 : ℤ))
    (g : FT ≃ₐ[Padic p] FT) (A : LaurentSeries (ZMod p)) :
    (Valued.v (falseTateLaurentAction p hp₂ hπ u hu g A) : WithZero (Multiplicative ℤ)) =
      Valued.v A := by
  let := normLimitField (Padic p) FT p hFT hInf
  let e := falseTateNormFieldLaurentEquiv p hp₂ hπ u hu
  calc
    _ = normLimitValuation (Padic p) FT hFT
        (e (falseTateLaurentAction p hp₂ hπ u hu g A)) :=
      (valuation_falseTateNormFieldLaurentEquiv p hp₂ hπ u hu _).symm
    _ = normLimitValuation (Padic p) FT hFT
        (normLimitAut (Padic p) p hFT hInf g (e A)) := by
      rw [falseTateLaurentAction_apply, e.apply_symm_apply]
    _ = normLimitValuation (Padic p) FT hFT (e A) :=
      normLimitAut_valuation (Padic p) p hFT hInf g (e A)
    _ = Valued.v A := valuation_falseTateNormFieldLaurentEquiv p hp₂ hπ u hu A

/-- Each Laurent automorphism is continuous for the original valuation topology. -/
theorem uniformContinuous_falseTateLaurentAction (u : NormLimit (Padic p) FT)
    (hu : normLimitValuation (Padic p) FT hFT u = exp (-1 : ℤ))
    (g : FT ≃ₐ[Padic p] FT) :
    UniformContinuous (falseTateLaurentAction p hp₂ hπ u hu g) := by
  apply valuedRingEquiv_uniformContinuous
  exact valuation_falseTateLaurentAction p hp₂ hπ u hu g

/-- Every actual automorphism fixes the original prime-field coefficients. -/
@[simp]
theorem falseTateLaurentAction_C (u : NormLimit (Padic p) FT)
    (hu : normLimitValuation (Padic p) FT hFT u = exp (-1 : ℤ))
    (g : FT ≃ₐ[Padic p] FT) (a : ZMod p) :
    falseTateLaurentAction p hp₂ hπ u hu g
        (algebraMap (ZMod p) (LaurentSeries (ZMod p)) a) =
      algebraMap (ZMod p) (LaurentSeries (ZMod p)) a := by
  exact DFunLike.congr_fun
    (Subsingleton.elim
      ((falseTateLaurentAction p hp₂ hπ u hu g).toRingHom.comp
        (algebraMap (ZMod p) (LaurentSeries (ZMod p))))
      (algebraMap (ZMod p) (LaurentSeries (ZMod p)))) a

/-- The actual image of the parameter is a power-series coordinate with
zero constant coefficient and invertible linear coefficient. -/
theorem exists_falseTatePowerSeriesCoordinate (u : NormLimit (Padic p) FT)
    (hu : normLimitValuation (Padic p) FT hFT u = exp (-1 : ℤ))
    (g : FT ≃ₐ[Padic p] FT) :
    ∃ f : PowerSeries (ZMod p),
      (f : LaurentSeries (ZMod p)) = falseTateLaurentAction p hp₂ hπ u hu g
          (HahnSeries.single (1 : ℤ) 1) ∧
        f.constantCoeff = 0 ∧ IsUnit (f.coeff 1) := by
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
def falseTatePowerSeriesCoordinate (u : NormLimit (Padic p) FT)
    (hu : normLimitValuation (Padic p) FT hFT u = exp (-1 : ℤ))
    (g : FT ≃ₐ[Padic p] FT) : PowerSeries (ZMod p) :=
  (exists_falseTatePowerSeriesCoordinate p hp₂ hπ u hu g).choose

/-- Its Laurent image is exactly the image of the original parameter under
the original action in the original coordinates. -/
theorem coe_falseTatePowerSeriesCoordinate (u : NormLimit (Padic p) FT)
    (hu : normLimitValuation (Padic p) FT hFT u = exp (-1 : ℤ))
    (g : FT ≃ₐ[Padic p] FT) :
    (falseTatePowerSeriesCoordinate p hp₂ hπ u hu g : LaurentSeries (ZMod p)) =
      falseTateLaurentAction p hp₂ hπ u hu g (HahnSeries.single (1 : ℤ) 1) :=
  (exists_falseTatePowerSeriesCoordinate p hp₂ hπ u hu g).choose_spec.1

@[simp]
theorem falseTatePowerSeriesCoordinate_constantCoeff (u : NormLimit (Padic p) FT)
    (hu : normLimitValuation (Padic p) FT hFT u = exp (-1 : ℤ))
    (g : FT ≃ₐ[Padic p] FT) :
    (falseTatePowerSeriesCoordinate p hp₂ hπ u hu g).constantCoeff = 0 :=
  (exists_falseTatePowerSeriesCoordinate p hp₂ hπ u hu g).choose_spec.2.1

/-- The linear coefficient is a unit in the original prime field. -/
theorem falseTatePowerSeriesCoordinate_linear_isUnit (u : NormLimit (Padic p) FT)
    (hu : normLimitValuation (Padic p) FT hFT u = exp (-1 : ℤ))
    (g : FT ≃ₐ[Padic p] FT) :
    IsUnit ((falseTatePowerSeriesCoordinate p hp₂ hπ u hu g).coeff 1) :=
  (exists_falseTatePowerSeriesCoordinate p hp₂ hπ u hu g).choose_spec.2.2

/-- The actual coordinate represents precisely the original image of the
specified norm-family uniformizer, as required in the lifting definition. -/
theorem falseTateNormFieldLaurentEquiv_powerSeriesCoordinate (u : NormLimit (Padic p) FT)
    (hu : normLimitValuation (Padic p) FT hFT u = exp (-1 : ℤ))
    (g : FT ≃ₐ[Padic p] FT) :
    letI := normLimitField (Padic p) FT p hFT hInf
    falseTateNormFieldLaurentEquiv p hp₂ hπ u hu
        (falseTatePowerSeriesCoordinate p hp₂ hπ u hu g : LaurentSeries (ZMod p)) =
      normLimitAut (Padic p) p hFT hInf g u := by
  let := normLimitField (Padic p) FT p hFT hInf
  let e := falseTateNormFieldLaurentEquiv p hp₂ hπ u hu
  rw [coe_falseTatePowerSeriesCoordinate, falseTateLaurentAction_apply]
  rw [e.apply_symm_apply]
  have hX : e (HahnSeries.single (1 : ℤ) 1) = u := by
    simpa only [LaurentSeries.coe_algebraMap, HahnSeries.ofPowerSeries_X] using
      falseTateNormFieldLaurentEquiv_X p hp₂ hπ u hu
  rw [hX]

/-- The identity automorphism has exactly the original parameter as coordinate. -/
@[simp]
theorem falseTatePowerSeriesCoordinate_one (u : NormLimit (Padic p) FT)
    (hu : normLimitValuation (Padic p) FT hFT u = exp (-1 : ℤ)) :
    falseTatePowerSeriesCoordinate p hp₂ hπ u hu 1 = PowerSeries.X := by
  apply HahnSeries.ofPowerSeries_injective (Γ := ℤ)
  rw [coe_falseTatePowerSeriesCoordinate, map_one]
  exact (HahnSeries.ofPowerSeries_X).symm

/-- On every power-series input, the original action is ordinary substitution
at its actual parameter image. -/
theorem falseTateLaurentAction_powerSeries (u : NormLimit (Padic p) FT)
    (hu : normLimitValuation (Padic p) FT hFT u = exp (-1 : ℤ))
    (g : FT ≃ₐ[Padic p] FT) (A : PowerSeries (ZMod p)) :
    falseTateLaurentAction p hp₂ hπ u hu g (A : LaurentSeries (ZMod p)) =
      (A.subst (falseTatePowerSeriesCoordinate p hp₂ hπ u hu g) :
        LaurentSeries (ZMod p)) := by
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
theorem falseTatePowerSeriesCoordinate_mul (u : NormLimit (Padic p) FT)
    (hu : normLimitValuation (Padic p) FT hFT u = exp (-1 : ℤ))
    (g h : FT ≃ₐ[Padic p] FT) :
    falseTatePowerSeriesCoordinate p hp₂ hπ u hu (g * h) =
      (falseTatePowerSeriesCoordinate p hp₂ hπ u hu h).subst
        (falseTatePowerSeriesCoordinate p hp₂ hπ u hu g) := by
  apply HahnSeries.ofPowerSeries_injective (Γ := ℤ)
  rw [coe_falseTatePowerSeriesCoordinate, map_mul]
  change falseTateLaurentAction p hp₂ hπ u hu g
    (falseTateLaurentAction p hp₂ hπ u hu h (HahnSeries.single (1 : ℤ) 1)) = _
  rw [← coe_falseTatePowerSeriesCoordinate, falseTateLaurentAction_powerSeries]

/-- Every actual group power is represented by the ordinary iterate of the
same actual power-series substitution. -/
theorem falseTatePowerSeriesCoordinate_pow (u : NormLimit (Padic p) FT)
    (hu : normLimitValuation (Padic p) FT hFT u = exp (-1 : ℤ))
    (g : FT ≃ₐ[Padic p] FT) (n : ℕ) :
    falseTatePowerSeriesCoordinate p hp₂ hπ u hu (g ^ n) =
      (PowerSeries.subst (falseTatePowerSeriesCoordinate p hp₂ hπ u hu g) :
        PowerSeries (ZMod p) → PowerSeries (ZMod p))^[n] PowerSeries.X := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', falseTatePowerSeriesCoordinate_mul, ih, Function.iterate_succ_apply']

/-- The original continuous field coordinate map is uniquely determined by
the original source constants and chosen original uniformizer. -/
theorem falseTateNormFieldLaurentEquiv_unique (u : NormLimit (Padic p) FT)
    (hu : normLimitValuation (Padic p) FT hFT u = exp (-1 : ℤ)) :
    letI := normLimitField (Padic p) FT p hFT hInf
    letI := normLimitValued (Padic p) FT p hFT hInf
    ∀ f : LaurentSeries (ZMod p) →+* NX, Continuous f →
      (∀ a, f (algebraMap (ZMod p) (LaurentSeries (ZMod p)) a) =
        (falseTateNormCoefficients p hp₂ hπ a : NX)) →
      f (algebraMap (PowerSeries (ZMod p)) (LaurentSeries (ZMod p)) PowerSeries.X) = u →
      f = (falseTateNormFieldLaurentEquiv p hp₂ hπ u hu).toRingHom := by
  let := normLimitField (Padic p) FT p hFT hInf
  let := normLimitValued (Padic p) FT p hFT hInf
  let := normLimit_completeSpace (Padic p) FT p hFT hInf
  let : UniformSpace (ZMod p) := ⊥
  let : DiscreteUniformity (ZMod p) := inferInstance
  intro f hf hC hX
  exact laurentUniformizerEquiv_unique NX _ _ _ _ _ f hf hC hX

/-- The coordinate displacement has exactly the valuation of the actual
original norm-field displacement, for every original automorphism. -/
theorem valuation_falseTatePowerSeriesCoordinate_displacement (u : NormLimit (Padic p) FT)
    (hu : normLimitValuation (Padic p) FT hFT u = exp (-1 : ℤ))
    (g : FT ≃ₐ[Padic p] FT) :
    letI := normLimitField (Padic p) FT p hFT hInf
    (Valued.v ((falseTatePowerSeriesCoordinate p hp₂ hπ u hu g : LaurentSeries (ZMod p)) -
      HahnSeries.single (1 : ℤ) 1) : WithZero (Multiplicative ℤ)) =
      normLimitValuation (Padic p) FT hFT (normLimitAut (Padic p) p hFT hInf g u - u) := by
  let := normLimitField (Padic p) FT p hFT hInf
  let e := falseTateNormFieldLaurentEquiv p hp₂ hπ u hu
  have hX : e (HahnSeries.single (1 : ℤ) 1) = u := by
    simpa only [LaurentSeries.coe_algebraMap, HahnSeries.ofPowerSeries_X] using
      falseTateNormFieldLaurentEquiv_X p hp₂ hπ u hu
  have hf : e (falseTatePowerSeriesCoordinate p hp₂ hπ u hu g : LaurentSeries (ZMod p)) =
      normLimitAut (Padic p) p hFT hInf g u :=
    falseTateNormFieldLaurentEquiv_powerSeriesCoordinate p hp₂ hπ u hu g
  calc
    _ = normLimitValuation (Padic p) FT hFT
        (e ((falseTatePowerSeriesCoordinate p hp₂ hπ u hu g : LaurentSeries (ZMod p)) -
          HahnSeries.single (1 : ℤ) 1)) :=
      (valuation_falseTateNormFieldLaurentEquiv p hp₂ hπ u hu _).symm
    _ = normLimitValuation (Padic p) FT hFT
        (e (falseTatePowerSeriesCoordinate p hp₂ hπ u hu g : LaurentSeries (ZMod p)) -
          e (HahnSeries.single (1 : ℤ) 1)) := congrArg _ (map_sub e _ _)
    _ = _ := congrArg (normLimitValuation (Padic p) FT hFT)
      (congrArg₂ (fun x y : NX => x - y) hf hX)

end OriginalCoordinates

end FalseTateExtension
