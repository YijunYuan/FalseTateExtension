/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FalseTateExtension.Layers
public import FalseTateExtension.Padic.CyclotomicRamification
public import FontaineWintenberger.Ramification.Norm.Valuation
public import FontaineWintenberger.Ramification.Different.Monogenic
public import FontaineWintenberger.Ramification.Lower.SpectralMaps
public import FontaineWintenberger.Ramification.Different.Subextension
public import Mathlib.RingTheory.Polynomial.Eisenstein.Criterion
public import Mathlib.RingTheory.Polynomial.GaussLemma

/-!
# Ramification in the actual radical tower

Eisenstein polynomials compute the degrees of the actual radical layers.
The actual norm valuation then supplies residue degree one and an actual
uniformizer; the monogenic different formula computes its different.

This implements the finite producers in blueprint `ft:direct-radical-step`.
-/

@[expose] public section

noncomputable section

open Polynomial IsDiscreteValuationRing

namespace FalseTateExtension

section Eisenstein

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

/-- Every positive power polynomial with a uniformizer constant term is
Eisenstein at the actual maximal ideal. -/
theorem X_pow_sub_uniformizer_isEisensteinAt {π : R} (hπ : Irreducible π)
    {m : ℕ} (hm : 0 < m) :
    (X ^ m - C π : R[X]).IsEisensteinAt (IsLocalRing.maximalIdeal R) := by
  apply (monic_X_pow_sub_C π hm.ne').isEisensteinAt_of_mem_of_notMem
    (IsLocalRing.maximalIdeal.isMaximal R).ne_top
  · intro i hi
    rw [natDegree_X_pow_sub_C] at hi
    by_cases hi0 : i = 0
    · subst i
      simpa [coeff_sub, coeff_X_pow, hm.ne] using
        (IsLocalRing.maximalIdeal R).neg_mem hπ.not_isUnit
    · simp [coeff_sub, coeff_X_pow, coeff_C, hi.ne, hi0]
  · have hc : (X ^ m - C π : R[X]).coeff 0 = -π := by
      simp [coeff_sub, coeff_X_pow, coeff_C, hm.ne]
    rw [hc, FontaineWintenberger.mem_maximalIdeal_pow_iff_addVal, AddValuation.map_neg]
    have hv := hπ.addVal_pow 1
    simp only [pow_one, Nat.cast_one] at hv
    rw [hv]
    norm_num

/-- Gauss's lemma makes the actual Eisenstein power polynomial irreducible
over the fraction field. -/
theorem irreducible_X_pow_sub_uniformizer {π : R} (hπ : Irreducible π)
    {m : ℕ} (hm : 0 < m) (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K] :
    Irreducible (X ^ m - C (algebraMap R K π) : K[X]) := by
  have hE := X_pow_sub_uniformizer_isEisensteinAt hπ hm
  have hI := hE.irreducible (inferInstance : (IsLocalRing.maximalIdeal R).IsPrime)
    (monic_X_pow_sub_C π hm.ne').isPrimitive (by simpa using hm)
  have h := (monic_X_pow_sub_C π hm.ne').irreducible_iff_irreducible_map_fraction_map (K := K)
  simpa only [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C]
    using h.mp hI

/-- The actual minimal polynomial of any root of a positive power of a
uniformizer is its Eisenstein polynomial. -/
theorem minpoly_root_uniformizer {π : R} (hπ : Irreducible π)
    {m : ℕ} (hm : 0 < m) (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]
    {L : Type*} [Field L] [Algebra K L] (α : L)
    (hα : α ^ m = algebraMap K L (algebraMap R K π)) :
    minpoly K α = X ^ m - C (algebraMap R K π) := by
  symm
  apply minpoly.eq_of_irreducible_of_monic
    (irreducible_X_pow_sub_uniformizer hπ hm K)
    (by simpa only [map_sub, map_pow, aeval_X, aeval_C] using sub_eq_zero.mpr hα)
    (monic_X_pow_sub_C _ hm.ne')

end Eisenstein

section Layers

variable {K : Type*} [Field K] (p : ℕ) [Fact p.Prime]

/-- The chosen radical in its actual finite intermediate field. -/
def radicalLayerRoot (π : K) (n : ℕ) : radicalLayer p π n :=
  ⟨radical p π n, radical_mem_radicalLayer p π n⟩

/-- The root relation holds in the actual finite field, with its original
base algebra. -/
theorem radicalLayerRoot_pow (π : K) (n : ℕ) :
    radicalLayerRoot p π n ^ (p ^ n) = algebraMap K (radicalLayer p π n) π := by
  apply Subtype.ext
  exact radical_pow p π n

end Layers

section EisensteinLayers

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
    [IsDiscreteValuationRing (NormedField.valuation (K := K)).valuationSubring]
variable (p : ℕ) [Fact p.Prime]

local notation "OK" => Valuation.valuationSubring (NormedField.valuation (K := K))

/-- Eisenstein computes the degree of the actual radical layer, including
the base layer at index zero and every prime. -/
theorem finrank_radicalLayer {π : OK} (hπ : Irreducible π) (n : ℕ) :
    Module.finrank K (radicalLayer p (π : K) n) = p ^ n := by
  have hp : 0 < p ^ n := pow_pos (Fact.out : p.Prime).pos n
  change Module.finrank K (IntermediateField.adjoin K {radical p (π : K) n}) = _
  rw [IntermediateField.adjoin.finrank (Algebra.IsIntegral.isIntegral _),
    minpoly_root_uniformizer hπ hp K _ (radical_pow p (π : K) n), natDegree_X_pow_sub_C]

/-- The minimal polynomial is computed on the original actual finite
field rather than a replacement splitting field. -/
theorem minpoly_radicalLayerRoot {π : OK} (hπ : Irreducible π) (n : ℕ) :
    minpoly K (radicalLayerRoot p (π : K) n) = X ^ (p ^ n) - C (π : K) :=
  minpoly_root_uniformizer hπ (pow_pos (Fact.out : p.Prime).pos n) K _
    (radicalLayerRoot_pow p (π : K) n)

/-- The actual field norm of the chosen radical is a signed original
uniformizer. The sign is retained at every prime and at level zero. -/
theorem norm_radicalLayerRoot {π : OK} (hπ : Irreducible π) (n : ℕ) :
    Algebra.norm K (radicalLayerRoot p (π : K) n) = (-1 : K) ^ (p ^ n + 1) * π := by
  let pb : PowerBasis K (radicalLayer p (π : K) n) := IntermediateField.adjoin.powerBasis
    (show IsIntegral K (radical p (π : K) n) from Algebra.IsIntegral.isIntegral _)
  have hgen : pb.gen = radicalLayerRoot p (π : K) n := rfl
  have hdim : pb.dim = p ^ n := by rw [← pb.finrank, finrank_radicalLayer p hπ]
  have hn := Algebra.PowerBasis.norm_gen_eq_coeff_zero_minpoly pb
  have hc : (X ^ (p ^ n) - C (π : K) : K[X]).coeff 0 = -(π : K) := by
    simp [coeff_sub, coeff_X_pow, coeff_C, (pow_pos (Fact.out : p.Prime).pos n).ne]
  rw [hgen, hdim, minpoly_radicalLayerRoot p hπ, hc] at hn
  simpa only [pow_succ, mul_neg, mul_neg_one, mul_one, neg_mul] using hn

/-- The original inclusion between consecutive actual radical fields has
degree exactly `p`, by their proved absolute Eisenstein degrees. -/
theorem radicalLayer_step_finrank {π : OK} (hπ : Irreducible π) (n : ℕ) :
    letI : Algebra (radicalLayer p (π : K) n) (radicalLayer p (π : K) (n + 1)) :=
      (IntermediateField.inclusion (radicalLayer_le_succ p (π : K) n)).toRingHom.toAlgebra
    Module.finrank (radicalLayer p (π : K) n) (radicalLayer p (π : K) (n + 1)) = p := by
  let F₀ := radicalLayer p (π : K) n
  let F₁ := radicalLayer p (π : K) (n + 1)
  let : Algebra F₀ F₁ :=
    (IntermediateField.inclusion (radicalLayer_le_succ p (π : K) n)).toRingHom.toAlgebra
  have : IsScalarTower K F₀ F₁ := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hd := Module.finrank_mul_finrank K F₀ F₁
  rw [finrank_radicalLayer p hπ n, finrank_radicalLayer p hπ (n + 1), pow_succ] at hd
  exact Nat.eq_of_mul_eq_mul_left (pow_pos (Fact.out : p.Prime).pos n) hd

end EisensteinLayers

section ValuedLayers

variable {K : Type*} [NontriviallyNormedField K]
    [FontaineWintenberger.IsCompleteDiscreteValuedField K]
variable (p : ℕ) [Fact p.Prime]

local notation "OK" => Valuation.valuationSubring (NormedField.valuation (K := K))

variable [CharZero K]

/-- Norm valuation on the actual finite radical field has exponent the
actual residue-field degree and right side the least positive additive
valuation. -/
theorem radicalLayer_normalizedValuation_pow {π : OK} (hπ : Irreducible π) (n : ℕ)
    {Γ : Type*} [LinearOrderedCommGroupWithZero Γ]
    (w : Valuation (radicalLayer p (π : K) n) Γ)
    [(NormedField.valuation (K := K)).HasExtension w] :
    letI := FontaineWintenberger.extensionValuationSubring_isDiscreteValuationRing
      K (radicalLayer p (π : K) n) w
    ((maximalIdeal w.valuationSubring).valuation (radicalLayer p (π : K) n)
      (radicalLayerRoot p (π : K) n)) ^
        Module.finrank (IsLocalRing.ResidueField OK) (IsLocalRing.ResidueField w.valuationSubring) =
      WithZero.exp (-1 : ℤ) := by
  have := FontaineWintenberger.extensionValuationSubring_isDiscreteValuationRing
    K (radicalLayer p (π : K) n) w
  have hn := FontaineWintenberger.extensionValuationSubring_normalizedValuation_norm
    K (radicalLayer p (π : K) n) w (radicalLayerRoot p (π : K) n)
  rw [norm_radicalLayerRoot p hπ] at hn
  have hπv : (maximalIdeal OK).valuation K (π : K) = WithZero.exp (-1 : ℤ) := by
    change (maximalIdeal OK).valuation K (algebraMap OK K π) = _
    rw [IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap]
    exact (maximalIdeal OK).intValuation_singleton hπ.ne_zero hπ.maximalIdeal_eq
  simpa only [map_mul, map_pow, Valuation.map_neg, map_one, one_pow, one_mul, hπv] using hn.symm

/-- Every actual extension valuation has residue degree one on every
radical layer. -/
theorem radicalLayer_residueDegree {π : OK} (hπ : Irreducible π) (n : ℕ)
    {Γ : Type*} [LinearOrderedCommGroupWithZero Γ]
    (w : Valuation (radicalLayer p (π : K) n) Γ)
    [(NormedField.valuation (K := K)).HasExtension w] :
    Module.finrank (IsLocalRing.ResidueField OK)
      (IsLocalRing.ResidueField w.valuationSubring) = 1 := by
  have hl := congrArg WithZero.log (radicalLayer_normalizedValuation_pow p hπ n w)
  simp only [WithZero.log_pow, WithZero.log_exp, nsmul_eq_mul] at hl
  have hd : (Module.finrank (IsLocalRing.ResidueField OK)
      (IsLocalRing.ResidueField w.valuationSubring) : ℤ) ∣ (-1 : ℤ) := ⟨_, hl.symm⟩
  have hd' : (Module.finrank (IsLocalRing.ResidueField OK)
      (IsLocalRing.ResidueField w.valuationSubring) : ℤ) ∣ (1 : ℤ) := by simpa using hd
  exact Nat.dvd_one.mp (Int.natCast_dvd_natCast.mp hd')

/-- The actual normalized extension valuation of the radical is that of
a uniformizer. -/
theorem radicalLayer_normalizedValuation_root {π : OK} (hπ : Irreducible π) (n : ℕ)
    {Γ : Type*} [LinearOrderedCommGroupWithZero Γ]
    (w : Valuation (radicalLayer p (π : K) n) Γ)
    [(NormedField.valuation (K := K)).HasExtension w] :
    letI := FontaineWintenberger.extensionValuationSubring_isDiscreteValuationRing
      K (radicalLayer p (π : K) n) w
    (maximalIdeal w.valuationSubring).valuation (radicalLayer p (π : K) n)
      (radicalLayerRoot p (π : K) n) = WithZero.exp (-1 : ℤ) := by
  have := FontaineWintenberger.extensionValuationSubring_isDiscreteValuationRing
    K (radicalLayer p (π : K) n) w
  simpa only [radicalLayer_residueDegree p hπ n w, pow_one] using
    radicalLayer_normalizedValuation_pow p hπ n w

/-- The actual chosen radical belongs to every compatible extension
valuation ring. -/
theorem radicalLayerRoot_mem {π : OK} (hπ : Irreducible π) (n : ℕ)
    {Γ : Type*} [LinearOrderedCommGroupWithZero Γ]
    (w : Valuation (radicalLayer p (π : K) n) Γ)
    [(NormedField.valuation (K := K)).HasExtension w] :
    radicalLayerRoot p (π : K) n ∈ w.valuationSubring := by
  have := FontaineWintenberger.extensionValuationSubring_isDiscreteValuationRing
    K (radicalLayer p (π : K) n) w
  rw [← w.valuationSubring.normalizedValuation_valuationSubring]
  change (maximalIdeal w.valuationSubring).valuation _ _ ≤ 1
  rw [radicalLayer_normalizedValuation_root p hπ]
  exact WithZero.exp_le_one_iff.mpr (by norm_num)

/-- The chosen radical as an element of the actual chosen integer ring. -/
def radicalUniformizer {π : OK} (hπ : Irreducible π) (n : ℕ)
    {Γ : Type*} [LinearOrderedCommGroupWithZero Γ]
    (w : Valuation (radicalLayer p (π : K) n) Γ)
    [(NormedField.valuation (K := K)).HasExtension w] : w.valuationSubring :=
  ⟨radicalLayerRoot p (π : K) n, radicalLayerRoot_mem p hπ n w⟩

/-- The chosen radical is an actual uniformizer, not merely an element
with a prescribed fractional norm in a larger closure. -/
theorem irreducible_radicalUniformizer {π : OK} (hπ : Irreducible π) (n : ℕ)
    {Γ : Type*} [LinearOrderedCommGroupWithZero Γ]
    (w : Valuation (radicalLayer p (π : K) n) Γ)
    [(NormedField.valuation (K := K)).HasExtension w] :
    Irreducible (radicalUniformizer p hπ n w) := by
  have := FontaineWintenberger.extensionValuationSubring_isDiscreteValuationRing
    K (radicalLayer p (π : K) n) w
  obtain ⟨ϖ, hϖ⟩ := exists_irreducible w.valuationSubring
  have hvϖ : (maximalIdeal w.valuationSubring).valuation (radicalLayer p (π : K) n)
      (ϖ : radicalLayer p (π : K) n) = WithZero.exp (-1 : ℤ) := by
    change (maximalIdeal w.valuationSubring).valuation _
      (algebraMap w.valuationSubring (radicalLayer p (π : K) n) ϖ) = _
    rw [IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap]
    exact (maximalIdeal w.valuationSubring).intValuation_singleton hϖ.ne_zero hϖ.maximalIdeal_eq
  obtain ⟨u, hu⟩ := associated_of_valuation_eq (A := w.valuationSubring)
    (ϖ : radicalLayer p (π : K) n) (radicalLayerRoot p (π : K) n)
    (hvϖ.trans (radicalLayer_normalizedValuation_root p hπ n w).symm)
  apply Associated.irreducible _ hϖ
  refine ⟨u, ?_⟩
  apply Subtype.ext
  change (ϖ : radicalLayer p (π : K) n) *
    ((u : w.valuationSubring) : radicalLayer p (π : K) n) = radicalLayerRoot p (π : K) n
  change ((u : w.valuationSubring) : radicalLayer p (π : K) n) *
    (ϖ : radicalLayer p (π : K) n) = radicalLayerRoot p (π : K) n at hu
  exact (mul_comm _ _).trans hu

/-- Every actual compatible valuation makes the radical layer totally
ramified of the proved Eisenstein degree. -/
theorem radicalLayer_ramificationIdx {π : OK} (hπ : Irreducible π) (n : ℕ)
    {Γ : Type*} [LinearOrderedCommGroupWithZero Γ]
    (w : Valuation (radicalLayer p (π : K) n) Γ)
    [(NormedField.valuation (K := K)).HasExtension w] :
    (IsLocalRing.maximalIdeal w.valuationSubring).ramificationIdx OK = p ^ n := by
  have hd := FontaineWintenberger.extensionValuationSubring_ramificationIdx_mul_residueDegree
    K (radicalLayer p (π : K) n) w
  simpa only [radicalLayer_residueDegree p hπ n w, mul_one, finrank_radicalLayer p hπ n] using hd

/-- The actual root uniformizer generates the full actual integer ring. -/
theorem adjoin_radicalUniformizer_eq_top {π : OK} (hπ : Irreducible π) (n : ℕ)
    {Γ : Type*} [LinearOrderedCommGroupWithZero Γ]
    (w : Valuation (radicalLayer p (π : K) n) Γ)
    [(NormedField.valuation (K := K)).HasExtension w] :
    Algebra.adjoin OK {radicalUniformizer p hπ n w} = ⊤ := by
  have he : (IsLocalRing.maximalIdeal w.valuationSubring).ramificationIdx OK =
      Module.finrank K (radicalLayer p (π : K) n) := by
    rw [radicalLayer_ramificationIdx p hπ n w, finrank_radicalLayer p hπ n]
  exact FontaineWintenberger.extensionValuationSubring_adjoin_uniformizer_eq_top
    K (radicalLayer p (π : K) n) w he (irreducible_radicalUniformizer p hπ n w)

/-- The minimal polynomial over the actual base integers is recovered
from the actual field minimal polynomial by integral closedness. -/
theorem minpoly_radicalUniformizer {π : OK} (hπ : Irreducible π) (n : ℕ)
    {Γ : Type*} [LinearOrderedCommGroupWithZero Γ]
    (w : Valuation (radicalLayer p (π : K) n) Γ)
    [(NormedField.valuation (K := K)).HasExtension w] :
    minpoly OK (radicalUniformizer p hπ n w) = X ^ (p ^ n) - C π := by
  have : IsScalarTower OK w.valuationSubring (radicalLayer p (π : K) n) :=
    Valuation.HasExtension.instIsScalarTower_valuationSubring' (NormedField.valuation (K := K)) w
  have hi : IsIntegral OK (radicalUniformizer p hπ n w) := Algebra.IsIntegral.isIntegral _
  have hfield := minpoly.isIntegrallyClosed_eq_field_fractions
    (K := K) (L := radicalLayer p (π : K) n) hi
  apply Polynomial.map_injective (algebraMap OK K) (IsFractionRing.injective OK K)
  rw [← hfield, Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C]
  exact minpoly_radicalLayerRoot p hπ n

/-- The actual different of a radical layer is computed by the literal
derivative of its proved monogenic Eisenstein polynomial. -/
theorem radicalLayer_different_order {π : OK} (hπ : Irreducible π) (n : ℕ)
    {Γ : Type*} [LinearOrderedCommGroupWithZero Γ]
    (w : Valuation (radicalLayer p (π : K) n) Γ)
    [(NormedField.valuation (K := K)).HasExtension w] :
    letI := FontaineWintenberger.extensionValuationSubring_isDiscreteValuationRing
      K (radicalLayer p (π : K) n) w
    emultiplicity (IsLocalRing.maximalIdeal w.valuationSubring)
        (differentIdeal OK w.valuationSubring) =
      ((p ^ n : ℕ) : ℕ∞) * addVal OK ((p ^ n : ℕ) : OK) + ((p ^ n - 1 : ℕ) : ℕ∞) := by
  have := FontaineWintenberger.extensionValuationSubring_isDiscreteValuationRing
    K (radicalLayer p (π : K) n) w
  have : IsScalarTower OK w.valuationSubring (radicalLayer p (π : K) n) :=
    Valuation.HasExtension.instIsScalarTower_valuationSubring' (NormedField.valuation (K := K)) w
  rw [FontaineWintenberger.differentIdeal_eq_span_derivative_of_adjoin_eq_top
      OK w.valuationSubring K (radicalLayer p (π : K) n)
      (adjoin_radicalUniformizer_eq_top p hπ n w),
    minpoly_radicalUniformizer p hπ n w, FontaineWintenberger.maximalIdeal_emultiplicity_span]
  simp only [derivative_sub, derivative_X_pow, derivative_C, sub_zero,
    map_mul, aeval_C, map_pow, aeval_X, addVal_mul]
  rw [FontaineWintenberger.addVal_algebraMap, radicalLayer_ramificationIdx p hπ n w,
    (irreducible_radicalUniformizer p hπ n w).addVal_pow]

/-- The same actual different order in natural numbers, using the actual
base additive valuation of `p`, with finiteness proved from characteristic
zero. -/
theorem radicalLayer_different_order_toNat {π : OK} (hπ : Irreducible π) (n : ℕ)
    {Γ : Type*} [LinearOrderedCommGroupWithZero Γ]
    (w : Valuation (radicalLayer p (π : K) n) Γ)
    [(NormedField.valuation (K := K)).HasExtension w] :
    letI := FontaineWintenberger.extensionValuationSubring_isDiscreteValuationRing
      K (radicalLayer p (π : K) n) w
    (emultiplicity (IsLocalRing.maximalIdeal w.valuationSubring)
      (differentIdeal OK w.valuationSubring)).toNat =
        p ^ n * n * (addVal OK (p : OK)).toNat + (p ^ n - 1) := by
  have := FontaineWintenberger.extensionValuationSubring_isDiscreteValuationRing
    K (radicalLayer p (π : K) n) w
  have hv : addVal OK ((p ^ n : ℕ) : OK) = (n : ℕ∞) * addVal OK (p : OK) := by
    rw [Nat.cast_pow, addVal_pow, nsmul_eq_mul]
  have hp0 : (p : OK) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hf : addVal OK (p : OK) ≠ ⊤ := addVal_eq_top_iff.not.mpr hp0
  obtain ⟨e, he⟩ := ENat.ne_top_iff_exists.mp hf
  have hd := radicalLayer_different_order p hπ n w
  rw [hv, ← he, ← Nat.cast_mul, ← Nat.cast_mul, ← Nat.cast_add] at hd
  have hd' := congrArg ENat.toNat hd
  simpa only [← he, ENat.toNat_natCast, mul_assoc] using hd'

section Relative

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

variable {π : Valuation.valuationSubring (NormedField.valuation (K := K))}
    (hπ : Irreducible π) (n : ℕ)

local notation "F₀" => radicalLayer (K := K) p (π : K) n
local notation "F₁" => radicalLayer (K := K) p (π : K) (n + 1)
local notation "O₀" => FontaineWintenberger.spectralIntegerRing K F₀
local notation "O₁" => FontaineWintenberger.spectralIntegerRing K F₁

include hπ

/-- The canonical integer-ring inclusion in a consecutive radical step
has ramification index `p`; both rings retain their original spectral
valuations over `K`. -/
theorem radicalLayer_step_ramificationIdx :
    letI : Algebra F₀ F₁ :=
      (IntermediateField.inclusion (radicalLayer_le_succ p (π : K) n)).toRingHom.toAlgebra
    letI : IsScalarTower K F₀ F₁ := IsScalarTower.of_algebraMap_eq fun _ => rfl
    letI := FontaineWintenberger.spectralValuation_hasExtension_tower K (E := F₀) (L := F₁)
    (IsLocalRing.maximalIdeal O₁).ramificationIdx O₀ = p := by
  let : Algebra F₀ F₁ :=
    (IntermediateField.inclusion (radicalLayer_le_succ p (π : K) n)).toRingHom.toAlgebra
  have : IsScalarTower K F₀ F₁ := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have := FontaineWintenberger.spectralValuation_hasExtension_tower K (E := F₀) (L := F₁)
  have : IsScalarTower OK O₀ O₁ :=
    Valuation.HasExtension.valuationSubring_isScalarTower (NormedField.valuation (K := K))
      (FontaineWintenberger.spectralValuation K F₀) (FontaineWintenberger.spectralValuation K F₁)
  have he := FontaineWintenberger.local_ramificationIdx_tower OK O₀ O₁
  rw [radicalLayer_ramificationIdx p hπ n, radicalLayer_ramificationIdx p hπ (n + 1),
    pow_succ] at he
  exact Nat.eq_of_mul_eq_mul_left (pow_pos (Fact.out : p.Prime).pos n) he.symm

set_option synthInstance.maxHeartbeats 100000 in
-- The spectral integer-ring tower requires extra dependent instance synthesis.
set_option maxHeartbeats 1000000 in
/-- The residue fields of two consecutive actual radical layers have
degree one, with the original canonical residue inclusion. -/
theorem radicalLayer_step_residueDegree :
    letI : Algebra F₀ F₁ :=
      (IntermediateField.inclusion (radicalLayer_le_succ p (π : K) n)).toRingHom.toAlgebra
    letI : IsScalarTower K F₀ F₁ := IsScalarTower.of_algebraMap_eq fun _ => rfl
    letI := FontaineWintenberger.spectralValuation_hasExtension_tower K (E := F₀) (L := F₁)
    Module.finrank (IsLocalRing.ResidueField O₀) (IsLocalRing.ResidueField O₁) = 1 := by
  let : Algebra F₀ F₁ :=
    (IntermediateField.inclusion (radicalLayer_le_succ p (π : K) n)).toRingHom.toAlgebra
  have : IsScalarTower K F₀ F₁ := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have := FontaineWintenberger.spectralValuation_hasExtension_tower K (E := F₀) (L := F₁)
  have : IsScalarTower OK O₀ O₁ :=
    Valuation.HasExtension.valuationSubring_isScalarTower (NormedField.valuation (K := K))
      (FontaineWintenberger.spectralValuation K F₀) (FontaineWintenberger.spectralValuation K F₁)
  have : Module.Finite O₀ O₁ := Module.Finite.of_restrictScalars_finite OK O₀ O₁
  have : IsScalarTower O₀ F₀ F₁ := Valuation.HasExtension.instIsScalarTower_valuationSubring
    (L := F₁) (FontaineWintenberger.spectralValuation K F₀)
  have : IsScalarTower O₀ O₁ F₁ := Valuation.HasExtension.instIsScalarTower_valuationSubring'
    (FontaineWintenberger.spectralValuation K F₀) (FontaineWintenberger.spectralValuation K F₁)
  have hd := FontaineWintenberger.local_ramificationIdx_mul_residueDegree_eq_finrank O₀ O₁ F₀ F₁
  rw [radicalLayer_step_ramificationIdx p hπ n, radicalLayer_step_finrank p hπ n] at hd
  exact Nat.eq_of_mul_eq_mul_left (Fact.out : p.Prime).pos (by simpa only [mul_one] using hd)

set_option synthInstance.maxHeartbeats 100000 in
-- The spectral integer-ring tower requires extra dependent instance synthesis.
set_option maxHeartbeats 1000000 in
/-- The actual relative different exponent follows from canonical
different transitivity and the two actual absolute exponents. -/
theorem radicalLayer_step_different_order :
    letI : Algebra F₀ F₁ :=
      (IntermediateField.inclusion (radicalLayer_le_succ p (π : K) n)).toRingHom.toAlgebra
    letI : IsScalarTower K F₀ F₁ := IsScalarTower.of_algebraMap_eq fun _ => rfl
    letI := FontaineWintenberger.spectralValuation_hasExtension_tower K (E := F₀) (L := F₁)
    (emultiplicity (IsLocalRing.maximalIdeal O₁) (differentIdeal O₀ O₁)).toNat =
      p ^ (n + 1) * (addVal OK (p : OK)).toNat + (p - 1) := by
  let : Algebra F₀ F₁ :=
    (IntermediateField.inclusion (radicalLayer_le_succ p (π : K) n)).toRingHom.toAlgebra
  have : IsScalarTower K F₀ F₁ := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have := FontaineWintenberger.spectralValuation_hasExtension_tower K (E := F₀) (L := F₁)
  have : IsScalarTower OK O₀ O₁ :=
    Valuation.HasExtension.valuationSubring_isScalarTower (NormedField.valuation (K := K))
      (FontaineWintenberger.spectralValuation K F₀) (FontaineWintenberger.spectralValuation K F₁)
  have : Module.Finite O₀ O₁ := Module.Finite.of_restrictScalars_finite OK O₀ O₁
  have hd := FontaineWintenberger.differentIdeal_order_toNat_tower OK O₀ O₁
  rw [radicalLayer_different_order_toNat p hπ (n + 1),
    radicalLayer_different_order_toNat p hπ n, radicalLayer_step_ramificationIdx p hπ n] at hd
  have hsub₀ := Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr
    (pow_ne_zero n (Fact.out : p.Prime).ne_zero))
  have hsub₁ := Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr
    (pow_ne_zero (n + 1) (Fact.out : p.Prime).ne_zero))
  have hsubp := Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr (Fact.out : p.Prime).ne_zero)
  have hsubmul := congrArg (fun x : ℕ => p * x) hsub₀
  rw [pow_succ] at hd hsub₁ ⊢
  nlinarith [hsubmul, hsub₁, hsubp]

end Relative

end ValuedLayers

section PadicBase

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
    [IsDiscreteValuationRing (NormedField.valuation (K := K)).valuationSubring]
variable (p : ℕ) [Fact p.Prime]

local notation "OK" => Valuation.valuationSubring (NormedField.valuation (K := K))

variable [Algebra (Padic p) K]
    [(NormedField.valuation (K := Padic p)).HasExtension (NormedField.valuation (K := K))]

local notation "Zp₀" => Valuation.valuationSubring (NormedField.valuation (K := Padic p))

/-- On the actual base integer ring over `ℚp`, the normalized additive
valuation of `p` is its canonical absolute ramification index. -/
theorem addVal_p_eq_padic_ramificationIdx :
    addVal OK (p : OK) = ((IsLocalRing.maximalIdeal OK).ramificationIdx Zp₀ : ℕ∞) := by
  have hpπ : Irreducible (p : Zp₀) := by
    have h := (MulEquiv.irreducible_iff (f := (padicUnitBallEquiv p).symm)).mpr
      PadicInt.irreducible_p
    simpa only [map_natCast] using h
  have h := FontaineWintenberger.addVal_algebraMap Zp₀ OK (p : Zp₀)
  simpa only [map_natCast, addVal_uniformizer hpπ, mul_one] using h

/-- The natural-valued normalized additive valuation of `p` is the same
actual ramification index. -/
theorem addVal_p_toNat_eq_padic_ramificationIdx :
    (addVal OK (p : OK)).toNat = (IsLocalRing.maximalIdeal OK).ramificationIdx Zp₀ := by
  rw [addVal_p_eq_padic_ramificationIdx p]
  rfl

end PadicBase

end FalseTateExtension
