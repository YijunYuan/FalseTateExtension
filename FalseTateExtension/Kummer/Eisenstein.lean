/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FalseTateExtension.Layers.Basic
public import FalseTateExtension.Cyclotomic.Ramification
public import FontaineWintenberger.Ramification.Norm.Valuation
public import FontaineWintenberger.Ramification.Different.Monogenic
public import FontaineWintenberger.Ramification.Lower.SpectralMaps
public import FontaineWintenberger.Ramification.Different.Subextension
public import FalseTateExtension.Mathlib.RingTheory.Polynomial.EisensteinUniformizer

/-!
# Eisenstein layers of the Kummer extension

Let `K` be a complete discretely valued field with uniformizer `π` and `p` a prime. The
polynomial `X^{p^n} - π` is Eisenstein, so `K(π^{1/p^n})/K` has degree `p^n` and
`N(π^{1/p^n}) = ± π`. Hence `K(π^{1/p^n})/K` is totally ramified: its residue degree is `1`,
`π^{1/p^n}` is a uniformizer, and the valuation ring is `𝒪_K[π^{1/p^n}]`. The different of
`K(π^{1/p^n})/K` is the derivative `p^n (π^{1/p^n})^{p^n - 1}` of the minimal polynomial, of
valuation `p^n n v_K(p) + p^n - 1`; each step `K(π^{1/p^n}) ⊆ K(π^{1/p^{n+1}})` has degree `p`,
ramification index `p` and different exponent `p^{n+1} v_K(p) + p - 1`. Over a `p`-adic base,
`v_K(p)` is the absolute ramification index `e_K`.

## Main results

* `finrank_radicalLayer`: `[K(π^{1/p^n}) : K] = p^n`.
* `radicalLayer_residueDegree`, `radicalLayer_ramificationIdx`: `K(π^{1/p^n})/K` is totally
  ramified of degree `p^n`.
* `irreducible_radicalUniformizer`, `adjoin_radicalUniformizer_eq_top`: `π^{1/p^n}` is a
  uniformizer generating the valuation ring over `𝒪_K`.
* `radicalLayer_different_order_toNat`: the different exponent of `K(π^{1/p^n})/K` is
  `p^n n v_K(p) + p^n - 1`.
* `radicalLayer_step_ramificationIdx`, `radicalLayer_step_different_order`: each step has
  ramification index `p` and different exponent `p^{n+1} v_K(p) + p - 1`.
* `addVal_p_toNat_eq_padic_ramificationIdx`: `v_K(p) = e_K` over `ℚ_p`.

## References

* Serre, *Local Fields*, Chapter I §6, Chapter III §6.
* Wintenberger, *Le corps des normes de certaines extensions infinies de corps locaux;
  applications*, §1.2.3.
-/

@[expose] public section

noncomputable section

open Polynomial IsDiscreteValuationRing
open FontaineWintenberger

namespace FalseTateExtension

/-- The absolute ramification index `e_K = v_K(p)` of `K`, as a natural number. -/
abbrev absoluteRamificationIdx (p : ℕ) (K : Type*) [NontriviallyNormedField K]
    [IsCompleteDiscreteValuedField K] : ℕ :=
  (addVal 𝒪[K] (p : 𝒪[K])).toNat

section Layers

variable {K : Type*} [Field K] (p : ℕ) [Fact p.Prime]

/-- `π^{1/p^n}` as an element of `K(π^{1/p^n})`. -/
def radicalLayerRoot (π : K) (n : ℕ) : radicalLayer p π n :=
  ⟨radical p π n, radical_mem_radicalLayer p π n⟩

/-- `(π^{1/p^n})^{p^n} = π` in `K(π^{1/p^n})`. -/
theorem radicalLayerRoot_pow (π : K) (n : ℕ) :
    radicalLayerRoot p π n ^ (p ^ n) = algebraMap K (radicalLayer p π n) π := by
  apply Subtype.ext
  exact radical_pow p π n

end Layers

section EisensteinLayers

variable {K : Type*} [NontriviallyNormedField K] [IsCompleteDiscreteValuedField K]
variable (p : ℕ) [Fact p.Prime]


/-- `[K(π^{1/p^n}) : K] = p^n` for a uniformizer `π`. -/
theorem finrank_radicalLayer (π : 𝒪[K]) [hπ : Fact (Irreducible π)] (n : ℕ) :
    Module.finrank K (radicalLayer p (π : K) n) = p ^ n := by
  have hp : 0 < p ^ n := pow_pos (Fact.out : p.Prime).pos n
  change Module.finrank K (IntermediateField.adjoin K {radical p (π : K) n}) = _
  rw [IntermediateField.adjoin.finrank (Algebra.IsIntegral.isIntegral _),
    minpoly_eq_X_pow_sub_C_of_pow_eq_of_irreducible hπ.out hp K _ (radical_pow p (π : K) n),
    natDegree_X_pow_sub_C]

/-- The minimal polynomial of `π^{1/p^n}` over `K` is `X^{p^n} - π`. -/
theorem minpoly_radicalLayerRoot (π : 𝒪[K]) [hπ : Fact (Irreducible π)] (n : ℕ) :
    minpoly K (radicalLayerRoot p (π : K) n) = X ^ (p ^ n) - C (π : K) :=
  minpoly_eq_X_pow_sub_C_of_pow_eq_of_irreducible hπ.out (pow_pos (Fact.out : p.Prime).pos n) K _
    (radicalLayerRoot_pow p (π : K) n)

/-- `N_{K(π^{1/p^n})/K}(π^{1/p^n}) = (-1)^{p^n + 1} π`. -/
theorem norm_radicalLayerRoot (π : 𝒪[K]) [hπ : Fact (Irreducible π)] (n : ℕ) :
    Algebra.norm K (radicalLayerRoot p (π : K) n) = (-1 : K) ^ (p ^ n + 1) * π := by
  let pb : PowerBasis K (radicalLayer p (π : K) n) := IntermediateField.adjoin.powerBasis
    (show IsIntegral K (radical p (π : K) n) from Algebra.IsIntegral.isIntegral _)
  have hgen : pb.gen = radicalLayerRoot p (π : K) n := rfl
  have hdim : pb.dim = p ^ n := by rw [← pb.finrank, finrank_radicalLayer p π]
  have hn := Algebra.PowerBasis.norm_gen_eq_coeff_zero_minpoly pb
  have hc : (X ^ (p ^ n) - C (π : K) : K[X]).coeff 0 = -(π : K) := by
    simp [coeff_sub, coeff_X_pow, coeff_C, (pow_pos (Fact.out : p.Prime).pos n).ne]
  rw [hgen, hdim, minpoly_radicalLayerRoot p π, hc] at hn
  simpa only [pow_succ, mul_neg, mul_neg_one, mul_one, neg_mul] using hn

/-- `[K(π^{1/p^{n+1}}) : K(π^{1/p^n})] = p`. -/
theorem radicalLayer_step_finrank (π : 𝒪[K]) [hπ : Fact (Irreducible π)] (n : ℕ) :
    letI : Algebra (radicalLayer p (π : K) n) (radicalLayer p (π : K) (n + 1)) :=
      (IntermediateField.inclusion (radicalLayer_le_succ p (π : K) n)).toRingHom.toAlgebra
    Module.finrank (radicalLayer p (π : K) n) (radicalLayer p (π : K) (n + 1)) = p := by
  let F₀ := radicalLayer p (π : K) n
  let F₁ := radicalLayer p (π : K) (n + 1)
  let : Algebra F₀ F₁ :=
    (IntermediateField.inclusion (radicalLayer_le_succ p (π : K) n)).toRingHom.toAlgebra
  have : IsScalarTower K F₀ F₁ := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hd := Module.finrank_mul_finrank K F₀ F₁
  rw [finrank_radicalLayer p π n, finrank_radicalLayer p π (n + 1), pow_succ] at hd
  exact Nat.eq_of_mul_eq_mul_left (pow_pos (Fact.out : p.Prime).pos n) hd

end EisensteinLayers

section ValuedLayers

variable {K : Type*} [NontriviallyNormedField K]
    [FontaineWintenberger.IsCompleteDiscreteValuedField K]
variable (p : ℕ) [Fact p.Prime]


variable [CharZero K]

/-- For a valuation `w` of `K(π^{1/p^n})` extending that of `K`, with residue degree `f`, the
normalized valuation `v_w` satisfies `f · v_w(π^{1/p^n}) = 1`. -/
theorem radicalLayer_normalizedValuation_pow (π : 𝒪[K]) [hπ : Fact (Irreducible π)] (n : ℕ)
    {Γ : Type*} [LinearOrderedCommGroupWithZero Γ]
    (w : Valuation (radicalLayer p (π : K) n) Γ)
    [(NormedField.valuation (K := K)).HasExtension w] :
    letI := FontaineWintenberger.extensionValuationSubring_isDiscreteValuationRing
      K (radicalLayer p (π : K) n) w
    ((maximalIdeal w.valuationSubring).valuation (radicalLayer p (π : K) n)
      (radicalLayerRoot p (π : K) n)) ^
        Module.finrank (𝓀[K]) (IsLocalRing.ResidueField w.valuationSubring) =
      WithZero.exp (-1 : ℤ) := by
  have := FontaineWintenberger.extensionValuationSubring_isDiscreteValuationRing
    K (radicalLayer p (π : K) n) w
  have hn := FontaineWintenberger.extensionValuationSubring_normalizedValuation_norm
    K (radicalLayer p (π : K) n) w (radicalLayerRoot p (π : K) n)
  rw [norm_radicalLayerRoot p π] at hn
  have hπv : (maximalIdeal 𝒪[K]).valuation K (π : K) = WithZero.exp (-1 : ℤ) := by
    change (maximalIdeal 𝒪[K]).valuation K (algebraMap 𝒪[K] K π) = _
    rw [IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap]
    exact (maximalIdeal 𝒪[K]).intValuation_singleton hπ.out.ne_zero hπ.out.maximalIdeal_eq
  simpa only [map_mul, map_pow, Valuation.map_neg, map_one, one_pow, one_mul, hπv] using hn.symm

/-- `K(π^{1/p^n})/K` has residue degree `1`. -/
theorem radicalLayer_residueDegree (π : 𝒪[K]) [hπ : Fact (Irreducible π)] (n : ℕ)
    {Γ : Type*} [LinearOrderedCommGroupWithZero Γ]
    (w : Valuation (radicalLayer p (π : K) n) Γ)
    [(NormedField.valuation (K := K)).HasExtension w] :
    Module.finrank (𝓀[K])
      (IsLocalRing.ResidueField w.valuationSubring) = 1 := by
  have hl := congrArg WithZero.log (radicalLayer_normalizedValuation_pow p π n w)
  simp only [WithZero.log_pow, WithZero.log_exp, nsmul_eq_mul] at hl
  have hd : (Module.finrank (𝓀[K])
      (IsLocalRing.ResidueField w.valuationSubring) : ℤ) ∣ (-1 : ℤ) := ⟨_, hl.symm⟩
  have hd' : (Module.finrank (𝓀[K])
      (IsLocalRing.ResidueField w.valuationSubring) : ℤ) ∣ (1 : ℤ) := by simpa using hd
  exact Nat.dvd_one.mp (Int.natCast_dvd_natCast.mp hd')

/-- `π^{1/p^n}` has normalized valuation `1` in `K(π^{1/p^n})`. -/
theorem radicalLayer_normalizedValuation_root (π : 𝒪[K]) [hπ : Fact (Irreducible π)] (n : ℕ)
    {Γ : Type*} [LinearOrderedCommGroupWithZero Γ]
    (w : Valuation (radicalLayer p (π : K) n) Γ)
    [(NormedField.valuation (K := K)).HasExtension w] :
    letI := FontaineWintenberger.extensionValuationSubring_isDiscreteValuationRing
      K (radicalLayer p (π : K) n) w
    (maximalIdeal w.valuationSubring).valuation (radicalLayer p (π : K) n)
      (radicalLayerRoot p (π : K) n) = WithZero.exp (-1 : ℤ) := by
  have := FontaineWintenberger.extensionValuationSubring_isDiscreteValuationRing
    K (radicalLayer p (π : K) n) w
  simpa only [radicalLayer_residueDegree p π n w, pow_one] using
    radicalLayer_normalizedValuation_pow p π n w

/-- `π^{1/p^n}` is integral in `K(π^{1/p^n})`. -/
theorem radicalLayerRoot_mem (π : 𝒪[K]) [hπ : Fact (Irreducible π)] (n : ℕ)
    {Γ : Type*} [LinearOrderedCommGroupWithZero Γ]
    (w : Valuation (radicalLayer p (π : K) n) Γ)
    [(NormedField.valuation (K := K)).HasExtension w] :
    radicalLayerRoot p (π : K) n ∈ w.valuationSubring := by
  have := FontaineWintenberger.extensionValuationSubring_isDiscreteValuationRing
    K (radicalLayer p (π : K) n) w
  rw [← w.valuationSubring.normalizedValuation_valuationSubring]
  change (maximalIdeal w.valuationSubring).valuation _ _ ≤ 1
  rw [radicalLayer_normalizedValuation_root p π]
  exact WithZero.exp_le_one_iff.mpr (by norm_num)

/-- `π^{1/p^n}` as an element of the valuation ring of `K(π^{1/p^n})`. -/
def radicalUniformizer (π : 𝒪[K]) [hπ : Fact (Irreducible π)] (n : ℕ)
    {Γ : Type*} [LinearOrderedCommGroupWithZero Γ]
    (w : Valuation (radicalLayer p (π : K) n) Γ)
    [(NormedField.valuation (K := K)).HasExtension w] : w.valuationSubring :=
  ⟨radicalLayerRoot p (π : K) n, radicalLayerRoot_mem p π n w⟩

/-- `π^{1/p^n}` is a uniformizer of `K(π^{1/p^n})`. -/
theorem irreducible_radicalUniformizer (π : 𝒪[K]) [hπ : Fact (Irreducible π)] (n : ℕ)
    {Γ : Type*} [LinearOrderedCommGroupWithZero Γ]
    (w : Valuation (radicalLayer p (π : K) n) Γ)
    [(NormedField.valuation (K := K)).HasExtension w] :
    Irreducible (radicalUniformizer p π n w) := by
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
    (hvϖ.trans (radicalLayer_normalizedValuation_root p π n w).symm)
  apply Associated.irreducible _ hϖ
  refine ⟨u, ?_⟩
  apply Subtype.ext
  change (ϖ : radicalLayer p (π : K) n) *
    ((u : w.valuationSubring) : radicalLayer p (π : K) n) = radicalLayerRoot p (π : K) n
  change ((u : w.valuationSubring) : radicalLayer p (π : K) n) *
    (ϖ : radicalLayer p (π : K) n) = radicalLayerRoot p (π : K) n at hu
  exact (mul_comm _ _).trans hu

/-- `K(π^{1/p^n})/K` has ramification index `p^n`. -/
theorem radicalLayer_ramificationIdx (π : 𝒪[K]) [hπ : Fact (Irreducible π)] (n : ℕ)
    {Γ : Type*} [LinearOrderedCommGroupWithZero Γ]
    (w : Valuation (radicalLayer p (π : K) n) Γ)
    [(NormedField.valuation (K := K)).HasExtension w] :
    (IsLocalRing.maximalIdeal w.valuationSubring).ramificationIdx 𝒪[K] = p ^ n := by
  have hd := FontaineWintenberger.extensionValuationSubring_ramificationIdx_mul_residueDegree
    K (radicalLayer p (π : K) n) w
  simpa only [radicalLayer_residueDegree p π n w, mul_one, finrank_radicalLayer p π n] using hd

/-- The valuation ring of `K(π^{1/p^n})` is `𝒪_K[π^{1/p^n}]`. -/
theorem adjoin_radicalUniformizer_eq_top (π : 𝒪[K]) [hπ : Fact (Irreducible π)] (n : ℕ)
    {Γ : Type*} [LinearOrderedCommGroupWithZero Γ]
    (w : Valuation (radicalLayer p (π : K) n) Γ)
    [(NormedField.valuation (K := K)).HasExtension w] :
    Algebra.adjoin 𝒪[K] {radicalUniformizer p π n w} = ⊤ := by
  have he : (IsLocalRing.maximalIdeal w.valuationSubring).ramificationIdx 𝒪[K] =
      Module.finrank K (radicalLayer p (π : K) n) := by
    rw [radicalLayer_ramificationIdx p π n w, finrank_radicalLayer p π n]
  exact FontaineWintenberger.extensionValuationSubring_adjoin_uniformizer_eq_top
    K (radicalLayer p (π : K) n) w he (irreducible_radicalUniformizer p π n w)

/-- The minimal polynomial of `π^{1/p^n}` over `𝒪_K` is `X^{p^n} - π`. -/
theorem minpoly_radicalUniformizer (π : 𝒪[K]) [hπ : Fact (Irreducible π)] (n : ℕ)
    {Γ : Type*} [LinearOrderedCommGroupWithZero Γ]
    (w : Valuation (radicalLayer p (π : K) n) Γ)
    [(NormedField.valuation (K := K)).HasExtension w] :
    minpoly 𝒪[K] (radicalUniformizer p π n w) = X ^ (p ^ n) - C π := by
  have : IsScalarTower 𝒪[K] w.valuationSubring (radicalLayer p (π : K) n) :=
    Valuation.HasExtension.instIsScalarTower_valuationSubring' (NormedField.valuation (K := K)) w
  have hi : IsIntegral 𝒪[K] (radicalUniformizer p π n w) := Algebra.IsIntegral.isIntegral _
  have hfield := minpoly.isIntegrallyClosed_eq_field_fractions
    (K := K) (L := radicalLayer p (π : K) n) hi
  apply Polynomial.map_injective (algebraMap 𝒪[K] K) (IsFractionRing.injective 𝒪[K] K)
  rw [← hfield, Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C]
  exact minpoly_radicalLayerRoot p π n

/-- The different of `K(π^{1/p^n})/K` has valuation `p^n v_K(p^n) + p^n - 1`, the valuation
of the derivative `p^n (π^{1/p^n})^{p^n - 1}` of the minimal polynomial. -/
theorem radicalLayer_different_order (π : 𝒪[K]) [hπ : Fact (Irreducible π)] (n : ℕ)
    {Γ : Type*} [LinearOrderedCommGroupWithZero Γ]
    (w : Valuation (radicalLayer p (π : K) n) Γ)
    [(NormedField.valuation (K := K)).HasExtension w] :
    letI := FontaineWintenberger.extensionValuationSubring_isDiscreteValuationRing
      K (radicalLayer p (π : K) n) w
    emultiplicity (IsLocalRing.maximalIdeal w.valuationSubring)
        (differentIdeal 𝒪[K] w.valuationSubring) =
      ((p ^ n : ℕ) : ℕ∞) * addVal 𝒪[K] ((p ^ n : ℕ) : 𝒪[K]) + ((p ^ n - 1 : ℕ) : ℕ∞) := by
  have := FontaineWintenberger.extensionValuationSubring_isDiscreteValuationRing
    K (radicalLayer p (π : K) n) w
  have : IsScalarTower 𝒪[K] w.valuationSubring (radicalLayer p (π : K) n) :=
    Valuation.HasExtension.instIsScalarTower_valuationSubring' (NormedField.valuation (K := K)) w
  rw [FontaineWintenberger.differentIdeal_eq_span_derivative_of_adjoin_eq_top
      𝒪[K] w.valuationSubring K (radicalLayer p (π : K) n)
      (adjoin_radicalUniformizer_eq_top p π n w),
    minpoly_radicalUniformizer p π n w, FontaineWintenberger.maximalIdeal_emultiplicity_span]
  simp only [derivative_sub, derivative_X_pow, derivative_C, sub_zero,
    map_mul, aeval_C, map_pow, aeval_X, addVal_mul]
  rw [FontaineWintenberger.addVal_algebraMap, radicalLayer_ramificationIdx p π n w,
    (irreducible_radicalUniformizer p π n w).addVal_pow]

/-- The different exponent of `K(π^{1/p^n})/K` is `p^n n v_K(p) + p^n - 1`. -/
theorem radicalLayer_different_order_toNat (π : 𝒪[K]) [hπ : Fact (Irreducible π)] (n : ℕ)
    {Γ : Type*} [LinearOrderedCommGroupWithZero Γ]
    (w : Valuation (radicalLayer p (π : K) n) Γ)
    [(NormedField.valuation (K := K)).HasExtension w] :
    letI := FontaineWintenberger.extensionValuationSubring_isDiscreteValuationRing
      K (radicalLayer p (π : K) n) w
    (emultiplicity (IsLocalRing.maximalIdeal w.valuationSubring)
      (differentIdeal 𝒪[K] w.valuationSubring)).toNat =
        p ^ n * n * (addVal 𝒪[K] (p : 𝒪[K])).toNat + (p ^ n - 1) := by
  have := FontaineWintenberger.extensionValuationSubring_isDiscreteValuationRing
    K (radicalLayer p (π : K) n) w
  have hv : addVal 𝒪[K] ((p ^ n : ℕ) : 𝒪[K]) = (n : ℕ∞) * addVal 𝒪[K] (p : 𝒪[K]) := by
    rw [Nat.cast_pow, addVal_pow, nsmul_eq_mul]
  have hp0 : (p : 𝒪[K]) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hf : addVal 𝒪[K] (p : 𝒪[K]) ≠ ⊤ := addVal_eq_top_iff.not.mpr hp0
  obtain ⟨e, he⟩ := ENat.ne_top_iff_exists.mp hf
  have hd := radicalLayer_different_order p π n w
  rw [hv, ← he, ← Nat.cast_mul, ← Nat.cast_mul, ← Nat.cast_add] at hd
  have hd' := congrArg ENat.toNat hd
  simpa only [← he, ENat.toNat_natCast, mul_assoc] using hd'

section Relative

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

variable (π : 𝒪[K])
    [hπ : Fact (Irreducible π)] (n : ℕ)

local notation "F₀" => radicalLayer (K := K) p (π : K) n
-- `(1 : ℕ)` makes the index elaborate eagerly. A bare `n + 1` leaves a postponed `OfNat ℕ 1`
-- metavariable in the index, so instance goals on the integer-ring tower below contain a
-- metavariable, bypass the instance cache and unfold `radicalLayer` at every unification.
local notation "F₁" => radicalLayer (K := K) p (π : K) (n + (1 : ℕ))
local notation "O₀" => FontaineWintenberger.spectralIntegerRing K F₀
local notation "O₁" => FontaineWintenberger.spectralIntegerRing K F₁

/-- The algebra structure of `K(π^{1/p^{n+1}})` over `K(π^{1/p^n})`. -/
local instance radicalStepAlgebra : Algebra F₀ F₁ :=
  (IntermediateField.inclusion (radicalLayer_le_succ p (π : K) n)).toRingHom.toAlgebra

/-- `K ⊆ K(π^{1/p^n}) ⊆ K(π^{1/p^{n+1}})` is a tower. -/
local instance radicalStepScalarTower : IsScalarTower K F₀ F₁ :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

/-- The spectral valuation of `K(π^{1/p^{n+1}})` extends that of `K(π^{1/p^n})`. -/
local instance radicalStepHasExtension :
    (FontaineWintenberger.spectralValuation K F₀).HasExtension
      (FontaineWintenberger.spectralValuation K F₁) :=
  FontaineWintenberger.spectralValuation_hasExtension_tower K (E := F₀) (L := F₁)

/-- `𝒪_K ⊆ 𝒪_{F₀} ⊆ 𝒪_{F₁}` is a tower. -/
local instance radicalStepIntegerScalarTower : IsScalarTower 𝒪[K] O₀ O₁ :=
  Valuation.HasExtension.valuationSubring_isScalarTower (NormedField.valuation (K := K))
    (FontaineWintenberger.spectralValuation K F₀) (FontaineWintenberger.spectralValuation K F₁)

/-- `𝒪_{F₁}` is a finite `𝒪_{F₀}`-module. -/
local instance radicalStepIntegerFinite : Module.Finite O₀ O₁ :=
  Module.Finite.of_restrictScalars_finite 𝒪[K] O₀ O₁

/-- `𝒪_{F₀} ⊆ F₀ ⊆ F₁` is a tower. -/
local instance radicalStepIntegerScalarTower' : IsScalarTower O₀ F₀ F₁ :=
  Valuation.HasExtension.instIsScalarTower_valuationSubring
    (L := F₁) (FontaineWintenberger.spectralValuation K F₀)

/-- `𝒪_{F₀} ⊆ 𝒪_{F₁} ⊆ F₁` is a tower. -/
local instance radicalStepIntegerScalarTower'' : IsScalarTower O₀ O₁ F₁ :=
  Valuation.HasExtension.instIsScalarTower_valuationSubring'
    (FontaineWintenberger.spectralValuation K F₀) (FontaineWintenberger.spectralValuation K F₁)

include hπ


/-- `K(π^{1/p^{n+1}})/K(π^{1/p^n})` has ramification index `p`. -/
theorem radicalLayer_step_ramificationIdx :
    (IsLocalRing.maximalIdeal O₁).ramificationIdx O₀ = p := by
  have he := FontaineWintenberger.local_ramificationIdx_tower 𝒪[K] O₀ O₁
  rw [radicalLayer_ramificationIdx p π n, radicalLayer_ramificationIdx p π (n + 1),
    pow_succ] at he
  exact Nat.eq_of_mul_eq_mul_left (pow_pos (Fact.out : p.Prime).pos n) he.symm

/-- `K(π^{1/p^{n+1}})/K(π^{1/p^n})` has residue degree `1`. -/
theorem radicalLayer_step_residueDegree :
    Module.finrank (IsLocalRing.ResidueField O₀) (IsLocalRing.ResidueField O₁) = 1 := by
  have hd := FontaineWintenberger.local_ramificationIdx_mul_residueDegree_eq_finrank O₀ O₁ F₀ F₁
  rw [radicalLayer_step_ramificationIdx p π n, radicalLayer_step_finrank p π n] at hd
  exact Nat.eq_of_mul_eq_mul_left (Fact.out : p.Prime).pos (by simpa only [mul_one] using hd)

/-- The different exponent of `K(π^{1/p^{n+1}})/K(π^{1/p^n})` is `p^{n+1} v_K(p) + p - 1`. -/
theorem radicalLayer_step_different_order :
    (emultiplicity (IsLocalRing.maximalIdeal O₁) (differentIdeal O₀ O₁)).toNat =
      p ^ (n + 1) * (addVal 𝒪[K] (p : 𝒪[K])).toNat + (p - 1) := by
  have hd := FontaineWintenberger.differentIdeal_order_toNat_tower 𝒪[K] O₀ O₁
  rw [radicalLayer_different_order_toNat p π (n + 1),
    radicalLayer_different_order_toNat p π n, radicalLayer_step_ramificationIdx p π n] at hd
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

variable {K : Type*} [NontriviallyNormedField K] [IsCompleteDiscreteValuedField K]
variable (p : ℕ) [Fact p.Prime]


variable [Algebra (ℚ_[p]) K]
    [(NormedField.valuation (K := ℚ_[p])).HasExtension (NormedField.valuation (K := K))]


/-- `v_K(p)` is the ramification index `e_K` of `K/ℚ_p`, in `ℕ∞`. -/
theorem addVal_p_eq_padic_ramificationIdx :
    addVal 𝒪[K] (p : 𝒪[K]) = ((IsLocalRing.maximalIdeal 𝒪[K]).ramificationIdx 𝒪[ℚ_[p]] : ℕ∞) := by
  have hpπ : Irreducible (p : 𝒪[ℚ_[p]]) := by
    have h := (MulEquiv.irreducible_iff (f := (padicUnitBallEquiv p).symm)).mpr
      PadicInt.irreducible_p
    simpa only [map_natCast] using h
  have h := FontaineWintenberger.addVal_algebraMap 𝒪[ℚ_[p]] 𝒪[K] (p : 𝒪[ℚ_[p]])
  simpa only [map_natCast, addVal_uniformizer hpπ, mul_one] using h

/-- `v_K(p)` is the ramification index `e_K` of `K/ℚ_p`. -/
theorem addVal_p_toNat_eq_padic_ramificationIdx :
    (addVal 𝒪[K] (p : 𝒪[K])).toNat = (IsLocalRing.maximalIdeal 𝒪[K]).ramificationIdx 𝒪[ℚ_[p]] := by
  rw [addVal_p_eq_padic_ramificationIdx p]
  rfl

end PadicBase

end FalseTateExtension
