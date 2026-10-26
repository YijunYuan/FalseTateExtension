/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FalseTateExtension.Cyclotomic.Basic
public import FalseTateExtension.Layers.Galois
public import FontaineWintenberger.Ramification.Lower.Basic
public import FontaineWintenberger.Ramification.Norm.Valuation
public import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots

/-!
# Total ramification of the cyclotomic layers over `ℚ_[p]`

Let `ζ = ζ_{p^{n+1}}` be a primitive `p^{n+1}`-th root of unity. Then
`N_{ℚ_[p](ζ)/ℚ_[p]}(ζ - 1) = (-1)^{φ(p^{n+1})} p`, so for every valuation `w` on `ℚ_[p](ζ)`
extending the valuation of `ℚ_[p]` the residue degree is `1`, `ζ - 1` is a uniformizer of the
valuation ring of `w`, and the ramification index is `[ℚ_[p](ζ) : ℚ_[p]] = φ(p^{n+1})`: the
extension `ℚ_[p](ζ_{p^{n+1}})/ℚ_[p]` is totally ramified. The same statements hold for the
spectral integer ring of `ℚ_[p](ζ)`.

## Main results

* `norm_zetaCyc_sub_one`: `N(ζ_{p^{n+1}} - 1) = (-1)^{φ(p^{n+1})} p`
* `cyclotomicLayer_residueDegree_eq_one`: the residue degree of `ℚ_[p](ζ_{p^{n+1}})/ℚ_[p]` is `1`
* `cyclotomicUniformizer`, `irreducible_cyclotomicUniformizer`: `ζ_{p^{n+1}} - 1` is a uniformizer
* `cyclotomicLayer_ramificationIdx_eq_totient`: the ramification index is `φ(p^{n+1})`
* `cyclotomicLayer_spectral_ramificationIdx`: the same for the spectral integer ring

## References

* [J.-P. Serre, *Local Fields*](https://doi.org/10.1007/978-1-4757-5673-9), Chapter IV, §4,
  Proposition 17.
-/

@[expose] public section

noncomputable section

open Polynomial IsDiscreteValuationRing
open FontaineWintenberger

namespace FalseTateExtension

variable (p : ℕ) [Fact p.Prime]

/-- `ζ_{p^m}` as an element of `K(ζ_{p^m})`. -/
def zetaCyc {K : Type*} [Field K] [CharZero K] (m : ℕ) : cyclotomicLayer (K := K) p m :=
  ⟨zeta p m, zeta_mem_cyclotomicLayer p m⟩

/-- `ζ_{p^m}` is a primitive `p^m`-th root of unity in `K(ζ_{p^m})`. -/
theorem isPrimitiveRoot_zetaCyc {K : Type*} [Field K] [CharZero K] (m : ℕ) :
    IsPrimitiveRoot (zetaCyc (K := K) p m) (p ^ m) :=
  (isPrimitiveRoot_zeta (K := K) p m).of_map_of_injective
    (f := (cyclotomicLayer (K := K) p m).val) (cyclotomicLayer p m).val.injective

/-- `N_{ℚ_[p](ζ_{p^{n+1}})/ℚ_[p]}(ζ_{p^{n+1}} - 1) = (-1)^{φ(p^{n+1})} p`. -/
theorem norm_zetaCyc_sub_one (n : ℕ) :
    Algebra.norm (ℚ_[p]) (zetaCyc (K := ℚ_[p]) p (n + 1) - 1) =
      (-1 : ℚ_[p]) ^ (p ^ (n + 1)).totient * p := by
  have : NeZero (p ^ (n + 1)) := ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
  let hζ := isPrimitiveRoot_zetaCyc (K := ℚ_[p]) p (n + 1)
  let pb := hζ.subOnePowerBasis (ℚ_[p])
  have hdim : pb.dim = (p ^ (n + 1)).totient := by
    rw [← pb.finrank, finrank_cyclotomicLayer_padic]
  have hn := Algebra.PowerBasis.norm_gen_eq_coeff_zero_minpoly pb
  rw [IsPrimitiveRoot.subOnePowerBasis_gen, hdim,
    hζ.minpoly_sub_one_eq_cyclotomic_comp (Padic.irreducible_cyclotomic_prime_pow p (n + 1))] at hn
  simpa only [coeff_zero_eq_eval_zero, eval_comp, eval_add, eval_X, eval_one,
    zero_add, eval_one_cyclotomic_prime_pow] using hn

/-- The valuation ring of a valuation on `ℚ_[p](ζ_{p^m})` extending the valuation of `ℚ_[p]` is
a discrete valuation ring. -/
instance cyclotomicValuationSubring_isDiscreteValuationRing (m : ℕ)
    {Γ : Type*} [LinearOrderedCommGroupWithZero Γ]
    (w : Valuation (cyclotomicLayer (K := ℚ_[p]) p m) Γ)
    [(NormedField.valuation (K := ℚ_[p])).HasExtension w] :
    IsDiscreteValuationRing w.valuationSubring :=
  FontaineWintenberger.extensionValuationSubring_isDiscreteValuationRing
    (ℚ_[p]) (cyclotomicLayer (K := ℚ_[p]) p m) w

/-- For a valuation `w` on `ℚ_[p](ζ_{p^{n+1}})` extending the valuation of `ℚ_[p]`, with residue
degree `f`, the normalized valuation `v` of `w` satisfies `v(ζ_{p^{n+1}} - 1)^f = exp (-1)`. -/
theorem cyclotomicLayer_normalizedValuation_pow (n : ℕ)
    {Γ : Type*} [LinearOrderedCommGroupWithZero Γ]
    (w : Valuation (cyclotomicLayer (K := ℚ_[p]) p (n + 1)) Γ)
    [(NormedField.valuation (K := ℚ_[p])).HasExtension w] :
    ((maximalIdeal w.valuationSubring).valuation (cyclotomicLayer (K := ℚ_[p]) p (n + 1))
      (zetaCyc (K := ℚ_[p]) p (n + 1) - 1)) ^
        Module.finrank (𝓀[ℚ_[p]]) (IsLocalRing.ResidueField w.valuationSubring) =
      WithZero.exp (-1 : ℤ) := by
  have hn := FontaineWintenberger.extensionValuationSubring_normalizedValuation_norm
    (ℚ_[p]) (cyclotomicLayer (K := ℚ_[p]) p (n + 1)) w
    (zetaCyc (K := ℚ_[p]) p (n + 1) - 1)
  rw [norm_zetaCyc_sub_one] at hn
  simpa only [map_mul, map_pow, Valuation.map_neg, map_one, one_pow, one_mul,
    padicValuationSubring_valuation_p] using hn.symm

/-- Every valuation on `ℚ_[p](ζ_{p^{n+1}})` extending the valuation of `ℚ_[p]` has residue
degree `1`. -/
theorem cyclotomicLayer_residueDegree_eq_one (n : ℕ)
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

/-- For a valuation `w` on `ℚ_[p](ζ_{p^{n+1}})` extending the valuation of `ℚ_[p]`, the
normalized valuation of `ζ_{p^{n+1}} - 1` is `exp (-1)`. -/
theorem cyclotomicLayer_normalizedValuation_sub_one (n : ℕ)
    {Γ : Type*} [LinearOrderedCommGroupWithZero Γ]
    (w : Valuation (cyclotomicLayer (K := ℚ_[p]) p (n + 1)) Γ)
    [(NormedField.valuation (K := ℚ_[p])).HasExtension w] :
    (maximalIdeal w.valuationSubring).valuation (cyclotomicLayer (K := ℚ_[p]) p (n + 1))
      (zetaCyc (K := ℚ_[p]) p (n + 1) - 1) = WithZero.exp (-1 : ℤ) := by
  simpa only [cyclotomicLayer_residueDegree_eq_one p n w, pow_one] using
    cyclotomicLayer_normalizedValuation_pow p n w

/-- `ζ_{p^{n+1}} - 1` lies in the valuation ring of every valuation on `ℚ_[p](ζ_{p^{n+1}})`
extending the valuation of `ℚ_[p]`. -/
theorem zetaCyc_sub_one_mem (n : ℕ)
    {Γ : Type*} [LinearOrderedCommGroupWithZero Γ]
    (w : Valuation (cyclotomicLayer (K := ℚ_[p]) p (n + 1)) Γ)
    [(NormedField.valuation (K := ℚ_[p])).HasExtension w] :
    zetaCyc (K := ℚ_[p]) p (n + 1) - 1 ∈ w.valuationSubring := by
  rw [← w.valuationSubring.normalizedValuation_valuationSubring]
  change (maximalIdeal w.valuationSubring).valuation _ _ ≤ 1
  rw [cyclotomicLayer_normalizedValuation_sub_one]
  exact WithZero.exp_le_one_iff.mpr (by norm_num)

/-- `ζ_{p^{n+1}} - 1` as an element of the valuation ring of a valuation `w` on
`ℚ_[p](ζ_{p^{n+1}})` extending the valuation of `ℚ_[p]`. -/
def cyclotomicUniformizer (n : ℕ)
    {Γ : Type*} [LinearOrderedCommGroupWithZero Γ]
    (w : Valuation (cyclotomicLayer (K := ℚ_[p]) p (n + 1)) Γ)
    [(NormedField.valuation (K := ℚ_[p])).HasExtension w] : w.valuationSubring :=
  ⟨zetaCyc (K := ℚ_[p]) p (n + 1) - 1, zetaCyc_sub_one_mem p n w⟩

/-- `ζ_{p^{n+1}} - 1` is a uniformizer of the valuation ring of every valuation on
`ℚ_[p](ζ_{p^{n+1}})` extending the valuation of `ℚ_[p]`. -/
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
    (π : cyclotomicLayer p (n + 1)) (zetaCyc (K := ℚ_[p]) p (n + 1) - 1)
    (hvπ.trans (cyclotomicLayer_normalizedValuation_sub_one p n w).symm)
  apply Associated.irreducible _ hπ.out
  refine ⟨u, ?_⟩
  apply Subtype.ext
  change (π : cyclotomicLayer p (n + 1)) *
    ((u : w.valuationSubring) : cyclotomicLayer p (n + 1)) = zetaCyc (K := ℚ_[p]) p (n + 1) - 1
  change ((u : w.valuationSubring) : cyclotomicLayer p (n + 1)) *
    (π : cyclotomicLayer p (n + 1)) = zetaCyc (K := ℚ_[p]) p (n + 1) - 1 at hu
  exact (mul_comm _ _).trans hu

/-- The ramification index of `ℚ_[p](ζ_{p^{n+1}})/ℚ_[p]`, for any valuation extending the
valuation of `ℚ_[p]`, equals the degree `[ℚ_[p](ζ_{p^{n+1}}) : ℚ_[p]]`. -/
theorem cyclotomicLayer_ramificationIdx (n : ℕ)
    {Γ : Type*} [LinearOrderedCommGroupWithZero Γ]
    (w : Valuation (cyclotomicLayer (K := ℚ_[p]) p (n + 1)) Γ)
    [(NormedField.valuation (K := ℚ_[p])).HasExtension w] :
    (IsLocalRing.maximalIdeal w.valuationSubring).ramificationIdx 𝒪[ℚ_[p]] =
      Module.finrank (ℚ_[p]) (cyclotomicLayer (K := ℚ_[p]) p (n + 1)) := by
  have h := FontaineWintenberger.extensionValuationSubring_ramificationIdx_mul_residueDegree
    (ℚ_[p]) (cyclotomicLayer (K := ℚ_[p]) p (n + 1)) w
  simpa only [cyclotomicLayer_residueDegree_eq_one p n w, mul_one] using h

/-- The ramification index of `ℚ_[p](ζ_{p^{n+1}})/ℚ_[p]`, for any valuation extending the
valuation of `ℚ_[p]`, is `φ(p^{n+1})`. -/
theorem cyclotomicLayer_ramificationIdx_eq_totient (n : ℕ)
    {Γ : Type*} [LinearOrderedCommGroupWithZero Γ]
    (w : Valuation (cyclotomicLayer (K := ℚ_[p]) p (n + 1)) Γ)
    [(NormedField.valuation (K := ℚ_[p])).HasExtension w] :
    (IsLocalRing.maximalIdeal w.valuationSubring).ramificationIdx 𝒪[ℚ_[p]] =
      (p ^ (n + 1)).totient := by
  rw [cyclotomicLayer_ramificationIdx, finrank_cyclotomicLayer_padic]

/-- The spectral integer ring of `ℚ_[p](ζ_{p^{n+1}})` has residue degree `1` over
`𝒪[ℚ_[p]]`. -/
theorem cyclotomicLayer_spectral_residueDegree_eq_one (n : ℕ) :
    Module.finrank (𝓀[ℚ_[p]])
      (IsLocalRing.ResidueField (FontaineWintenberger.spectralIntegerRing (ℚ_[p])
        (cyclotomicLayer (K := ℚ_[p]) p (n + 1)))) = 1 :=
  cyclotomicLayer_residueDegree_eq_one p n (FontaineWintenberger.spectralValuation (ℚ_[p])
    (cyclotomicLayer (K := ℚ_[p]) p (n + 1)))

/-- `ζ_{p^{n+1}} - 1` is a uniformizer of the spectral integer ring of `ℚ_[p](ζ_{p^{n+1}})`. -/
theorem irreducible_cyclotomicUniformizer_spectral (n : ℕ) :
    Irreducible (cyclotomicUniformizer p n (FontaineWintenberger.spectralValuation (ℚ_[p])
      (cyclotomicLayer (K := ℚ_[p]) p (n + 1)))) :=
  irreducible_cyclotomicUniformizer p n (FontaineWintenberger.spectralValuation (ℚ_[p])
    (cyclotomicLayer (K := ℚ_[p]) p (n + 1)))

/-- `ℚ_[p](ζ_{p^{n+1}})/ℚ_[p]` is totally ramified: the ramification index of the spectral
integer ring of `ℚ_[p](ζ_{p^{n+1}})` over `𝒪[ℚ_[p]]` is `φ(p^{n+1})`. -/
theorem cyclotomicLayer_spectral_ramificationIdx (n : ℕ) :
    (IsLocalRing.maximalIdeal (FontaineWintenberger.spectralIntegerRing (ℚ_[p])
      (cyclotomicLayer (K := ℚ_[p]) p (n + 1)))).ramificationIdx 𝒪[ℚ_[p]] =
        (p ^ (n + 1)).totient :=
  cyclotomicLayer_ramificationIdx_eq_totient p n (FontaineWintenberger.spectralValuation (ℚ_[p])
    (cyclotomicLayer (K := ℚ_[p]) p (n + 1)))

end FalseTateExtension

end
