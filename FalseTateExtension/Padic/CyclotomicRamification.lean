/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FalseTateExtension.Padic.Cyclotomic
public import FalseTateExtension.GaloisLayers
public import FontaineWintenberger.Ramification.Norm.Valuation
public import FontaineWintenberger.Ramification.Lower.Basic
public import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots

/-!
# Total ramification of the actual rational cyclotomic layers

The norm of a primitive prime-power root minus one is `(-1)^d * p`, retaining
the sign at order two. The actual normalized norm-valuation identity then
forces residue degree one and makes this element a uniformizer of the actual
extension valuation ring. The actual ramification index is the field degree.
This proves blueprint `ft:cyclotomic-total-ramification`; see Serre,
*Local Fields*, Chapter IV, Section 4, Proposition 17.
-/

@[expose] public section

noncomputable section

open Polynomial IsDiscreteValuationRing
open FontaineWintenberger

namespace FalseTateExtension

variable (p : ℕ) [Fact p.Prime]

/-- The actual chosen primitive root, viewed in its finite cyclotomic field. -/
def cyclotomicLayerRoot (m : ℕ) : cyclotomicLayer (K := ℚ_[p]) p m :=
  ⟨rootOfUnity p m, rootOfUnity_mem_cyclotomicLayer p m⟩

theorem isPrimitiveRoot_cyclotomicLayerRoot (m : ℕ) :
    IsPrimitiveRoot (cyclotomicLayerRoot p m) (p ^ m) :=
  (isPrimitiveRoot_rootOfUnity (K := ℚ_[p]) p m).of_map_of_injective
    (f := (cyclotomicLayer (K := ℚ_[p]) p m).val) (cyclotomicLayer p m).val.injective

instance cyclotomicLayer_padic_isCyclotomicExtension (m : ℕ) :
    IsCyclotomicExtension {p ^ m} (ℚ_[p]) (cyclotomicLayer (K := ℚ_[p]) p m) := by
  have : NeZero (p ^ m) := ⟨pow_ne_zero m (Fact.out : p.Prime).ne_zero⟩
  have hζ := (isPrimitiveRoot_rootOfUnity (K := ℚ_[p]) p m)
  exact hζ.intermediateField_adjoin_isCyclotomicExtension (ℚ_[p])

/-- The norm of the actual cyclotomic uniformizer candidate, with its sign
retained also for `p = 2` at the first level. -/
theorem norm_cyclotomicLayerRoot_sub_one (n : ℕ) :
    Algebra.norm (ℚ_[p]) (cyclotomicLayerRoot p (n + 1) - 1) =
      (-1 : ℚ_[p]) ^ (p ^ (n + 1)).totient * p := by
  have : NeZero (p ^ (n + 1)) := ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
  let hζ := isPrimitiveRoot_cyclotomicLayerRoot p (n + 1)
  let pb := hζ.subOnePowerBasis (ℚ_[p])
  have hdim : pb.dim = (p ^ (n + 1)).totient := by
    rw [← pb.finrank, finrank_cyclotomicLayer_padic]
  have hn := Algebra.PowerBasis.norm_gen_eq_coeff_zero_minpoly pb
  rw [IsPrimitiveRoot.subOnePowerBasis_gen, hdim,
    hζ.minpoly_sub_one_eq_cyclotomic_comp (Padic.irreducible_cyclotomic_prime_pow p (n + 1))] at hn
  simpa only [coeff_zero_eq_eval_zero, eval_comp, eval_add, eval_X, eval_one,
    zero_add, eval_one_cyclotomic_prime_pow] using hn

instance cyclotomicValuationSubring_isDiscreteValuationRing (m : ℕ)
    {Γ : Type*} [LinearOrderedCommGroupWithZero Γ]
    (w : Valuation (cyclotomicLayer (K := ℚ_[p]) p m) Γ)
    [(NormedField.valuation (K := ℚ_[p])).HasExtension w] :
    IsDiscreteValuationRing w.valuationSubring :=
  FontaineWintenberger.extensionValuationSubring_isDiscreteValuationRing
    (ℚ_[p]) (cyclotomicLayer (K := ℚ_[p]) p m) w

/-- The actual field norm identity forces a unit normalized norm valuation
for the cyclotomic generator, multiplied by the actual residue degree. -/
theorem cyclotomicLayer_normalizedValuation_pow (n : ℕ)
    {Γ : Type*} [LinearOrderedCommGroupWithZero Γ]
    (w : Valuation (cyclotomicLayer (K := ℚ_[p]) p (n + 1)) Γ)
    [(NormedField.valuation (K := ℚ_[p])).HasExtension w] :
    ((maximalIdeal w.valuationSubring).valuation (cyclotomicLayer (K := ℚ_[p]) p (n + 1))
      (cyclotomicLayerRoot p (n + 1) - 1)) ^
        Module.finrank (𝓀[ℚ_[p]]) (IsLocalRing.ResidueField w.valuationSubring) =
      WithZero.exp (-1 : ℤ) := by
  have hn := FontaineWintenberger.extensionValuationSubring_normalizedValuation_norm
    (ℚ_[p]) (cyclotomicLayer (K := ℚ_[p]) p (n + 1)) w
    (cyclotomicLayerRoot p (n + 1) - 1)
  rw [norm_cyclotomicLayerRoot_sub_one] at hn
  simpa only [map_mul, map_pow, Valuation.map_neg, map_one, one_pow, one_mul,
    padicUnitBall_normalizedValuation_p] using hn.symm

/-- Every actual extension valuation has residue degree one on a positive
cyclotomic layer. -/
theorem cyclotomicLayer_residueDegree (n : ℕ)
    {Γ : Type*} [LinearOrderedCommGroupWithZero Γ]
    (w : Valuation (cyclotomicLayer (K := ℚ_[p]) p (n + 1)) Γ)
    [(NormedField.valuation (K := ℚ_[p])).HasExtension w] :
    Module.finrank (𝓀[ℚ_[p]])
      (IsLocalRing.ResidueField w.valuationSubring) = 1 := by
  have hl := congrArg WithZero.log (cyclotomicLayer_normalizedValuation_pow p n w)
  simp only [WithZero.log_pow, WithZero.log_exp, nsmul_eq_mul] at hl
  have hd : (Module.finrank (𝓀[ℚ_[p]])
      (IsLocalRing.ResidueField w.valuationSubring) : ℤ) ∣ (-1 : ℤ) := ⟨_, hl.symm⟩
  have hd' : (Module.finrank (𝓀[ℚ_[p]])
      (IsLocalRing.ResidueField w.valuationSubring) : ℤ) ∣ (1 : ℤ) := by simpa using hd
  exact Nat.dvd_one.mp (Int.natCast_dvd_natCast.mp hd')

/-- The actual normalized extension valuation sends the cyclotomic generator
minus one to its least positive additive valuation. -/
theorem cyclotomicLayer_normalizedValuation_sub_one (n : ℕ)
    {Γ : Type*} [LinearOrderedCommGroupWithZero Γ]
    (w : Valuation (cyclotomicLayer (K := ℚ_[p]) p (n + 1)) Γ)
    [(NormedField.valuation (K := ℚ_[p])).HasExtension w] :
    (maximalIdeal w.valuationSubring).valuation (cyclotomicLayer (K := ℚ_[p]) p (n + 1))
      (cyclotomicLayerRoot p (n + 1) - 1) = WithZero.exp (-1 : ℤ) := by
  simpa only [cyclotomicLayer_residueDegree p n w, pow_one] using
    cyclotomicLayer_normalizedValuation_pow p n w

/-- The cyclotomic generator minus one belongs to the actual chosen integer ring. -/
theorem cyclotomicLayerRoot_sub_one_mem (n : ℕ)
    {Γ : Type*} [LinearOrderedCommGroupWithZero Γ]
    (w : Valuation (cyclotomicLayer (K := ℚ_[p]) p (n + 1)) Γ)
    [(NormedField.valuation (K := ℚ_[p])).HasExtension w] :
    cyclotomicLayerRoot p (n + 1) - 1 ∈ w.valuationSubring := by
  rw [← w.valuationSubring.normalizedValuation_valuationSubring]
  change (maximalIdeal w.valuationSubring).valuation _ _ ≤ 1
  rw [cyclotomicLayer_normalizedValuation_sub_one]
  exact WithZero.exp_le_one_iff.mpr (by norm_num)

/-- The actual cyclotomic uniformizer as an element of the chosen integer ring. -/
def cyclotomicUniformizer (n : ℕ)
    {Γ : Type*} [LinearOrderedCommGroupWithZero Γ]
    (w : Valuation (cyclotomicLayer (K := ℚ_[p]) p (n + 1)) Γ)
    [(NormedField.valuation (K := ℚ_[p])).HasExtension w] : w.valuationSubring :=
  ⟨cyclotomicLayerRoot p (n + 1) - 1, cyclotomicLayerRoot_sub_one_mem p n w⟩

/-- The actual cyclotomic generator minus one is irreducible in the chosen
extension valuation ring. -/
theorem irreducible_cyclotomicUniformizer (n : ℕ)
    {Γ : Type*} [LinearOrderedCommGroupWithZero Γ]
    (w : Valuation (cyclotomicLayer (K := ℚ_[p]) p (n + 1)) Γ)
    [(NormedField.valuation (K := ℚ_[p])).HasExtension w] :
    Irreducible (cyclotomicUniformizer p n w) := by
  obtain ⟨π, hπ.out⟩ := exists_irreducible w.valuationSubring
  have hvπ : (maximalIdeal w.valuationSubring).valuation
      (cyclotomicLayer (K := ℚ_[p]) p (n + 1)) (π : cyclotomicLayer p (n + 1)) =
        WithZero.exp (-1 : ℤ) := by
    change (maximalIdeal w.valuationSubring).valuation _
      (algebraMap w.valuationSubring (cyclotomicLayer (K := ℚ_[p]) p (n + 1)) π) = _
    rw [IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap]
    exact (maximalIdeal w.valuationSubring).intValuation_singleton hπ.out.ne_zero
        hπ.out.maximalIdeal_eq
  obtain ⟨u, hu⟩ := associated_of_valuation_eq (A := w.valuationSubring)
    (π : cyclotomicLayer p (n + 1)) (cyclotomicLayerRoot p (n + 1) - 1)
    (hvπ.trans (cyclotomicLayer_normalizedValuation_sub_one p n w).symm)
  apply Associated.irreducible _ hπ.out
  refine ⟨u, ?_⟩
  apply Subtype.ext
  change (π : cyclotomicLayer p (n + 1)) *
    ((u : w.valuationSubring) : cyclotomicLayer p (n + 1)) = cyclotomicLayerRoot p (n + 1) - 1
  change ((u : w.valuationSubring) : cyclotomicLayer p (n + 1)) *
    (π : cyclotomicLayer p (n + 1)) = cyclotomicLayerRoot p (n + 1) - 1 at hu
  exact (mul_comm _ _).trans hu

/-- The cyclotomic generator minus one generates the actual maximal ideal. -/
theorem span_cyclotomicUniformizer (n : ℕ)
    {Γ : Type*} [LinearOrderedCommGroupWithZero Γ]
    (w : Valuation (cyclotomicLayer (K := ℚ_[p]) p (n + 1)) Γ)
    [(NormedField.valuation (K := ℚ_[p])).HasExtension w] :
    Ideal.span {cyclotomicUniformizer p n w} = IsLocalRing.maximalIdeal w.valuationSubring :=
  ((irreducible_iff_uniformizer _).mp (irreducible_cyclotomicUniformizer p n w)).symm

/-- The actual ramification index of a positive cyclotomic layer equals its
actual field degree. -/
theorem cyclotomicLayer_ramificationIdx (n : ℕ)
    {Γ : Type*} [LinearOrderedCommGroupWithZero Γ]
    (w : Valuation (cyclotomicLayer (K := ℚ_[p]) p (n + 1)) Γ)
    [(NormedField.valuation (K := ℚ_[p])).HasExtension w] :
    (IsLocalRing.maximalIdeal w.valuationSubring).ramificationIdx 𝒪[ℚ_[p]] =
      Module.finrank (ℚ_[p]) (cyclotomicLayer (K := ℚ_[p]) p (n + 1)) := by
  have h := FontaineWintenberger.extensionValuationSubring_ramificationIdx_mul_residueDegree
    (ℚ_[p]) (cyclotomicLayer (K := ℚ_[p]) p (n + 1)) w
  simpa only [cyclotomicLayer_residueDegree p n w, mul_one] using h

/-- In particular the actual ramification index is the expected totient. -/
theorem cyclotomicLayer_ramificationIdx_eq_totient (n : ℕ)
    {Γ : Type*} [LinearOrderedCommGroupWithZero Γ]
    (w : Valuation (cyclotomicLayer (K := ℚ_[p]) p (n + 1)) Γ)
    [(NormedField.valuation (K := ℚ_[p])).HasExtension w] :
    (IsLocalRing.maximalIdeal w.valuationSubring).ramificationIdx 𝒪[ℚ_[p]] =
      (p ^ (n + 1)).totient := by
  rw [cyclotomicLayer_ramificationIdx, finrank_cyclotomicLayer_padic]

/-- The canonical spectral integer ring of the actual positive cyclotomic
layer has residue degree one over the actual base unit ball. -/
theorem cyclotomicLayer_spectral_residueDegree (n : ℕ) :
    Module.finrank (𝓀[ℚ_[p]])
      (IsLocalRing.ResidueField (FontaineWintenberger.spectralIntegerRing (ℚ_[p])
        (cyclotomicLayer (K := ℚ_[p]) p (n + 1)))) = 1 :=
  cyclotomicLayer_residueDegree p n (FontaineWintenberger.spectralValuation (ℚ_[p])
    (cyclotomicLayer (K := ℚ_[p]) p (n + 1)))

/-- The same actual cyclotomic element is a uniformizer in the canonical
spectral integer ring, including at the first dyadic level. -/
theorem irreducible_cyclotomicUniformizer_spectral (n : ℕ) :
    Irreducible (cyclotomicUniformizer p n (FontaineWintenberger.spectralValuation (ℚ_[p])
      (cyclotomicLayer (K := ℚ_[p]) p (n + 1)))) :=
  irreducible_cyclotomicUniformizer p n (FontaineWintenberger.spectralValuation (ℚ_[p])
    (cyclotomicLayer (K := ℚ_[p]) p (n + 1)))

/-- The canonical spectral cyclotomic extension is actually totally ramified:
its ramification index equals its degree, namely the prime-power totient. -/
theorem cyclotomicLayer_spectral_ramificationIdx (n : ℕ) :
    (IsLocalRing.maximalIdeal (FontaineWintenberger.spectralIntegerRing (ℚ_[p])
      (cyclotomicLayer (K := ℚ_[p]) p (n + 1)))).ramificationIdx 𝒪[ℚ_[p]] =
        (p ^ (n + 1)).totient :=
  cyclotomicLayer_ramificationIdx_eq_totient p n (FontaineWintenberger.spectralValuation (ℚ_[p])
    (cyclotomicLayer (K := ℚ_[p]) p (n + 1)))

end FalseTateExtension

end
