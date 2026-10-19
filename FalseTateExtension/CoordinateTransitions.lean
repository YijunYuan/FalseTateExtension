/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FalseTateExtension.FiniteCoordinates
public import FalseTateExtension.Mathlib.FieldTheory.RestrictNormal
public import Mathlib.Data.ZMod.Units

/-!
# Transition maps for finite false Tate coordinates

Ordinary finite Galois restriction between the actual diagonal layers is
compatible with reduction of the Kummer and cyclotomic coordinates. Iterated
radical and root-of-unity power relations identify the smaller generators
inside the larger fields.

This proves blueprint `ft:coordinate-transitions`, the compatible-root
transition argument in Liu, Section 5.1, including the zeroth layer.
-/

@[expose] public section

namespace FalseTateExtension

noncomputable section

variable {K : Type*} [Field K] [CharZero K] (p : ℕ) [Fact p.Prime] (π : K)

/-- Galois restriction between diagonal layers `n ≤ m`. -/
def finiteLayerRestriction (hπ : π ≠ 0) {n m : ℕ} (h : n ≤ m) :
    (falseTateLayer p π m m ≃ₐ[K] falseTateLayer p π m m) →*
      (falseTateLayer p π n n ≃ₐ[K] falseTateLayer p π n n) :=
  haveI := falseTateLayer_isGalois p π hπ n
  IntermediateField.restrictNormalHomOfLE (falseTateLayer_mono p π h h)

/-- Restriction commutes with the inclusion of the smaller layer into the larger one. -/
theorem finiteLayerRestriction_commutes (hπ : π ≠ 0) {n m : ℕ} (h : n ≤ m)
    (g : falseTateLayer p π m m ≃ₐ[K] falseTateLayer p π m m)
    (x : falseTateLayer p π n n) :
    IntermediateField.inclusion (falseTateLayer_mono p π h h)
        (finiteLayerRestriction p π hπ h g x) =
      g (IntermediateField.inclusion (falseTateLayer_mono p π h h) x) :=
  haveI := falseTateLayer_isGalois p π hπ n
  IntermediateField.restrictNormalHomOfLE_commutes _ g x

/-- Every automorphism of a smaller diagonal layer extends to a larger one. -/
theorem finiteLayerRestriction_surjective (hπ : π ≠ 0) {n m : ℕ} (h : n ≤ m) :
    Function.Surjective (finiteLayerRestriction p π hπ h) :=
  haveI := falseTateLayer_isGalois p π hπ n
  haveI := falseTateLayer_isGalois p π hπ m
  IntermediateField.restrictNormalHomOfLE_surjective _

@[simp]
theorem finiteLayerRestriction_refl (hπ : π ≠ 0) (n : ℕ) :
    finiteLayerRestriction p π hπ (le_refl n) = MonoidHom.id _ :=
  haveI := falseTateLayer_isGalois p π hπ n
  IntermediateField.restrictNormalHomOfLE_refl

/-- Restriction is transitive in the layers. -/
theorem finiteLayerRestriction_comp (hπ : π ≠ 0) {n m l : ℕ}
    (hnm : n ≤ m) (hml : m ≤ l) :
    (finiteLayerRestriction p π hπ hnm).comp (finiteLayerRestriction p π hπ hml) =
      finiteLayerRestriction p π hπ (hnm.trans hml) :=
  haveI := falseTateLayer_isGalois p π hπ n
  haveI := falseTateLayer_isGalois p π hπ m
  IntermediateField.restrictNormalHomOfLE_comp _ _

omit [CharZero K] in
/-- Iterating compatibility expresses a smaller radical as a power of a
larger one. -/
theorem radical_add_pow (n k : ℕ) : radical p π (n + k) ^ (p ^ k) = radical p π n := by
  induction k with
  | zero => simp
  | succ k ih =>
      change radical p π (n + k + 1) ^ (p ^ (k + 1)) = radical p π n
      rw [pow_succ', pow_mul, radical_succ_pow, ih]

omit [CharZero K] in
theorem radical_pow_sub {n m : ℕ} (h : n ≤ m) :
    radical p π m ^ (p ^ (m - n)) = radical p π n := by
  have he : n + (m - n) = m := by omega
  simpa only [he] using radical_add_pow p π n (m - n)

/-- Iterated compatibility of the chosen roots of unity. -/
theorem rootOfUnity_add_pow (n k : ℕ) :
    rootOfUnity (K := K) p (n + k) ^ (p ^ k) = rootOfUnity p n := by
  induction k with
  | zero => simp
  | succ k ih =>
      change rootOfUnity (K := K) p (n + k + 1) ^ (p ^ (k + 1)) = rootOfUnity p n
      rw [pow_succ', pow_mul, rootOfUnity_succ_pow, ih]

theorem rootOfUnity_pow_sub {n m : ℕ} (h : n ≤ m) :
    rootOfUnity (K := K) p m ^ (p ^ (m - n)) = rootOfUnity p n := by
  have he : n + (m - n) = m := by omega
  simpa only [he] using rootOfUnity_add_pow (K := K) p n (m - n)

theorem inclusion_layerRadical {n m : ℕ} (h : n ≤ m) :
    IntermediateField.inclusion (falseTateLayer_mono p π h h) (layerRadical p π n) =
      layerRadical p π m ^ (p ^ (m - n)) := by
  apply Subtype.ext
  exact (radical_pow_sub p π h).symm

theorem inclusion_layerRootOfUnity {n m : ℕ} (h : n ≤ m) :
    IntermediateField.inclusion (falseTateLayer_mono p π h h) (layerRootOfUnity p π n) =
      layerRootOfUnity p π m ^ (p ^ (m - n)) := by
  apply Subtype.ext
  exact (rootOfUnity_pow_sub (K := K) p h).symm

/-- Before reducing the exponent, restriction evaluates on the smaller
radical using the Kummer coordinate of the larger layer. -/
theorem finiteLayerRestriction_radical (hπ : π ≠ 0) {n m : ℕ} (h : n ≤ m)
    (g : falseTateLayer p π m m ≃ₐ[K] falseTateLayer p π m m) :
    finiteLayerRestriction p π hπ h g (layerRadical p π n) =
      layerRootOfUnity p π n ^ (finiteKummerExponent p π m hπ g).val *
        layerRadical p π n := by
  apply (show Function.Injective (IntermediateField.inclusion (falseTateLayer_mono p π h h))
    from (IntermediateField.inclusion (falseTateLayer_mono p π h h)).injective)
  rw [finiteLayerRestriction_commutes p π hπ h, map_mul, map_pow,
    inclusion_layerRootOfUnity p π h, inclusion_layerRadical p π h, map_pow,
    finiteKummerExponent_spec p π m hπ g, mul_pow]
  congr 1
  rw [← pow_mul, Nat.mul_comm, pow_mul]

/-- Restriction evaluates on the smaller primitive root using the larger
finite cyclotomic character. -/
theorem finiteLayerRestriction_rootOfUnity (hπ : π ≠ 0) {n m : ℕ} (h : n ≤ m)
    (g : falseTateLayer p π m m ≃ₐ[K] falseTateLayer p π m m) :
    finiteLayerRestriction p π hπ h g (layerRootOfUnity p π n) =
      layerRootOfUnity p π n ^
        (finiteCyclotomicCharacter p π m g : ZMod (p ^ m)).val := by
  apply (show Function.Injective (IntermediateField.inclusion (falseTateLayer_mono p π h h))
    from (IntermediateField.inclusion (falseTateLayer_mono p π h h)).injective)
  rw [finiteLayerRestriction_commutes p π hπ h, map_pow, inclusion_layerRootOfUnity p π h, map_pow,
    finiteCyclotomicCharacter_spec p π m g]
  rw [← pow_mul, Nat.mul_comm, pow_mul]

/-- A power of the smaller primitive root depends only on reduction of an
exponent from the larger residue ring. No nontriviality of `ZMod 1` is needed. -/
theorem layerRootOfUnity_pow_reduction {n m : ℕ} (h : n ≤ m) (a : ZMod (p ^ m)) :
    layerRootOfUnity p π n ^
        (ZMod.castHom (pow_dvd_pow p h) (ZMod (p ^ n)) a).val =
      layerRootOfUnity p π n ^ a.val := by
  have : NeZero (p ^ n) := ⟨pow_ne_zero n (Fact.out : p.Prime).ne_zero⟩
  have : NeZero (p ^ m) := ⟨pow_ne_zero m (Fact.out : p.Prime).ne_zero⟩
  have hz : ((ZMod.castHom (pow_dvd_pow p h) (ZMod (p ^ n)) a).val : ZMod (p ^ n)) =
      (a.val : ZMod (p ^ n)) := by
    rw [ZMod.natCast_zmod_val, ZMod.castHom_apply, ZMod.cast_eq_val]
  have hm := (ZMod.natCast_eq_natCast_iff ..).mp hz
  have hu : layerRootUnit p π n ^
        (ZMod.castHom (pow_dvd_pow p h) (ZMod (p ^ n)) a).val =
      layerRootUnit p π n ^ a.val := by
    apply pow_eq_pow_iff_modEq.mpr
    simpa only [← (isPrimitiveRoot_layerRootUnit p π n).eq_orderOf] using hm
  simpa only [Units.val_pow_eq_pow_val, coe_layerRootUnit] using congrArg Units.val hu

/-- The finite Kummer exponents are compatible under the actual finite Galois
restriction and canonical residue-ring reduction. -/
theorem finiteKummerExponent_restrict (hπ : π ≠ 0) {n m : ℕ} (h : n ≤ m)
    (g : falseTateLayer p π m m ≃ₐ[K] falseTateLayer p π m m) :
    finiteKummerExponent p π n hπ (finiteLayerRestriction p π hπ h g) =
      ZMod.castHom (pow_dvd_pow p h) (ZMod (p ^ n))
        (finiteKummerExponent p π m hπ g) := by
  apply finiteKummerExponent_unique p π n hπ
  rw [finiteLayerRestriction_radical]
  exact congrArg (· * layerRadical p π n)
    (layerRootOfUnity_pow_reduction p π h (finiteKummerExponent p π m hπ g)).symm

/-- The finite cyclotomic characters are compatible with canonical reduction
on units. This includes transitions to the zeroth layer. -/
theorem finiteCyclotomicCharacter_restrict (hπ : π ≠ 0) {n m : ℕ} (h : n ≤ m)
    (g : falseTateLayer p π m m ≃ₐ[K] falseTateLayer p π m m) :
    finiteCyclotomicCharacter p π n (finiteLayerRestriction p π hπ h g) =
      ZMod.unitsMap (pow_dvd_pow p h) (finiteCyclotomicCharacter p π m g) := by
  apply finiteCyclotomicCharacter_unique p π n
  rw [finiteLayerRestriction_rootOfUnity]
  exact (layerRootOfUnity_pow_reduction p π h
    (finiteCyclotomicCharacter p π m g : ZMod (p ^ m))).symm

end

end FalseTateExtension
