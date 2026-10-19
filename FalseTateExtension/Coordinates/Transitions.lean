/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FalseTateExtension.Coordinates.Finite
public import FalseTateExtension.Mathlib.FieldTheory.RestrictNormal
public import Mathlib.Data.ZMod.Units

/-!
# Compatibility of the coordinates under restriction

Let `K` be a field of characteristic zero, `p` a prime, `π ∈ K` nonzero and
`L_n = K(π^{1/p^n}, ζ_{p^n})`. For `n ≤ m`, restriction `Gal(L_m/K) → Gal(L_n/K)` is a
surjective homomorphism, and the cyclotomic character and Kummer exponent of the restriction
are the reductions modulo `p^n` of those of the automorphism of `L_m`:
`χ_n(g|_{L_n}) = χ_m(g) mod p^n` and `b_n(g|_{L_n}) = b_m(g) mod p^n`. This rests on the
relations `(π^{1/p^m})^{p^{m-n}} = π^{1/p^n}` and `ζ_{p^m}^{p^{m-n}} = ζ_{p^n}`.

## Main results

* `finiteLayerRestriction`: the restriction homomorphism `Gal(L_m/K) → Gal(L_n/K)`.
* `finiteLayerRestriction_surjective`, `finiteLayerRestriction_comp`: it is surjective and
  transitive in the layers.
* `radical_pow_sub`, `rootOfUnity_pow_sub`: `(π^{1/p^m})^{p^{m-n}} = π^{1/p^n}` and
  `ζ_{p^m}^{p^{m-n}} = ζ_{p^n}`.
* `finiteKummerExponent_restrict`: `b_n(g|_{L_n}) = b_m(g) mod p^n`.
* `finiteCyclotomicCharacter_restrict`: `χ_n(g|_{L_n}) = χ_m(g) mod p^n`.

## References

* Liu, *On lattices in semi-stable representations: a proof of a conjecture of Breuil*, §5.1.
-/

@[expose] public section

namespace FalseTateExtension

noncomputable section

variable {K : Type*} [Field K] [CharZero K] (p : ℕ) [Fact p.Prime] (π : K)

/-- Restriction `Gal(L_m/K) → Gal(L_n/K)` between diagonal layers, for `n ≤ m`. -/
def finiteLayerRestriction [hπ : NeZero π] {n m : ℕ} (h : n ≤ m) :
    (falseTateLayer p π m m ≃ₐ[K] falseTateLayer p π m m) →*
      (falseTateLayer p π n n ≃ₐ[K] falseTateLayer p π n n) :=
  haveI := falseTateLayer_isGalois p π n
  IntermediateField.restrictNormalHomOfLE (falseTateLayer_mono p π h h)

/-- `g|_{L_n}(x) = g(x)` for `x ∈ L_n ⊆ L_m`. -/
theorem finiteLayerRestriction_commutes [hπ : NeZero π] {n m : ℕ} (h : n ≤ m)
    (g : falseTateLayer p π m m ≃ₐ[K] falseTateLayer p π m m)
    (x : falseTateLayer p π n n) :
    IntermediateField.inclusion (falseTateLayer_mono p π h h)
        (finiteLayerRestriction p π h g x) =
      g (IntermediateField.inclusion (falseTateLayer_mono p π h h) x) :=
  haveI := falseTateLayer_isGalois p π n
  IntermediateField.restrictNormalHomOfLE_commutes _ g x

/-- Restriction `Gal(L_m/K) → Gal(L_n/K)` is surjective. -/
theorem finiteLayerRestriction_surjective [hπ : NeZero π] {n m : ℕ} (h : n ≤ m) :
    Function.Surjective (finiteLayerRestriction p π h) :=
  haveI := falseTateLayer_isGalois p π n
  haveI := falseTateLayer_isGalois p π m
  IntermediateField.restrictNormalHomOfLE_surjective _

/-- Restriction from `L_n` to itself is the identity. -/
@[simp]
theorem finiteLayerRestriction_refl [hπ : NeZero π] (n : ℕ) :
    finiteLayerRestriction p π (le_refl n) = MonoidHom.id _ :=
  haveI := falseTateLayer_isGalois p π n
  IntermediateField.restrictNormalHomOfLE_refl

/-- Restricting from `L_l` to `L_m` and then to `L_n` is restricting from `L_l` to `L_n`. -/
theorem finiteLayerRestriction_comp [hπ : NeZero π] {n m l : ℕ}
    (hnm : n ≤ m) (hml : m ≤ l) :
    (finiteLayerRestriction p π hnm).comp (finiteLayerRestriction p π hml) =
      finiteLayerRestriction p π (hnm.trans hml) :=
  haveI := falseTateLayer_isGalois p π n
  haveI := falseTateLayer_isGalois p π m
  IntermediateField.restrictNormalHomOfLE_comp _ _

omit [CharZero K] in
/-- `(π^{1/p^{n+k}})^{p^k} = π^{1/p^n}`. -/
theorem radical_add_pow (n k : ℕ) : radical p π (n + k) ^ (p ^ k) = radical p π n := by
  induction k with
  | zero => simp
  | succ k ih =>
      change radical p π (n + k + 1) ^ (p ^ (k + 1)) = radical p π n
      rw [pow_succ', pow_mul, radical_succ_pow, ih]

omit [CharZero K] in
/-- `(π^{1/p^m})^{p^{m-n}} = π^{1/p^n}` for `n ≤ m`. -/
theorem radical_pow_sub {n m : ℕ} (h : n ≤ m) :
    radical p π m ^ (p ^ (m - n)) = radical p π n := by
  have he : n + (m - n) = m := by omega
  simpa only [he] using radical_add_pow p π n (m - n)

/-- `ζ_{p^{n+k}}^{p^k} = ζ_{p^n}`. -/
theorem rootOfUnity_add_pow (n k : ℕ) :
    rootOfUnity (K := K) p (n + k) ^ (p ^ k) = rootOfUnity p n := by
  induction k with
  | zero => simp
  | succ k ih =>
      change rootOfUnity (K := K) p (n + k + 1) ^ (p ^ (k + 1)) = rootOfUnity p n
      rw [pow_succ', pow_mul, rootOfUnity_succ_pow, ih]

/-- `ζ_{p^m}^{p^{m-n}} = ζ_{p^n}` for `n ≤ m`. -/
theorem rootOfUnity_pow_sub {n m : ℕ} (h : n ≤ m) :
    rootOfUnity (K := K) p m ^ (p ^ (m - n)) = rootOfUnity p n := by
  have he : n + (m - n) = m := by omega
  simpa only [he] using rootOfUnity_add_pow (K := K) p n (m - n)

/-- In `L_m`, the element `π^{1/p^n}` of `L_n` is `(π^{1/p^m})^{p^{m-n}}`. -/
theorem inclusion_layerRadical {n m : ℕ} (h : n ≤ m) :
    IntermediateField.inclusion (falseTateLayer_mono p π h h) (layerRadical p π n) =
      layerRadical p π m ^ (p ^ (m - n)) := by
  apply Subtype.ext
  exact (radical_pow_sub p π h).symm

/-- In `L_m`, the element `ζ_{p^n}` of `L_n` is `ζ_{p^m}^{p^{m-n}}`. -/
theorem inclusion_layerRootOfUnity {n m : ℕ} (h : n ≤ m) :
    IntermediateField.inclusion (falseTateLayer_mono p π h h) (layerRootOfUnity p π n) =
      layerRootOfUnity p π m ^ (p ^ (m - n)) := by
  apply Subtype.ext
  exact (rootOfUnity_pow_sub (K := K) p h).symm

/-- `g|_{L_n}(π^{1/p^n}) = ζ_{p^n}^{b_m(g)} π^{1/p^n}` for `g ∈ Gal(L_m/K)`. -/
theorem finiteLayerRestriction_radical [hπ : NeZero π] {n m : ℕ} (h : n ≤ m)
    (g : falseTateLayer p π m m ≃ₐ[K] falseTateLayer p π m m) :
    finiteLayerRestriction p π h g (layerRadical p π n) =
      layerRootOfUnity p π n ^ (finiteKummerExponent p π m g).val *
        layerRadical p π n := by
  apply (show Function.Injective (IntermediateField.inclusion (falseTateLayer_mono p π h h))
    from (IntermediateField.inclusion (falseTateLayer_mono p π h h)).injective)
  rw [finiteLayerRestriction_commutes p π h, map_mul, map_pow,
    inclusion_layerRootOfUnity p π h, inclusion_layerRadical p π h, map_pow,
    finiteKummerExponent_spec p π m g, mul_pow]
  congr 1
  rw [← pow_mul, Nat.mul_comm, pow_mul]

/-- `g|_{L_n}(ζ_{p^n}) = ζ_{p^n}^{χ_m(g)}` for `g ∈ Gal(L_m/K)`. -/
theorem finiteLayerRestriction_rootOfUnity [hπ : NeZero π] {n m : ℕ} (h : n ≤ m)
    (g : falseTateLayer p π m m ≃ₐ[K] falseTateLayer p π m m) :
    finiteLayerRestriction p π h g (layerRootOfUnity p π n) =
      layerRootOfUnity p π n ^
        (finiteCyclotomicCharacter p π m g : ZMod (p ^ m)).val := by
  apply (show Function.Injective (IntermediateField.inclusion (falseTateLayer_mono p π h h))
    from (IntermediateField.inclusion (falseTateLayer_mono p π h h)).injective)
  rw [finiteLayerRestriction_commutes p π h, map_pow, inclusion_layerRootOfUnity p π h, map_pow,
    finiteCyclotomicCharacter_spec p π m g]
  rw [← pow_mul, Nat.mul_comm, pow_mul]

/-- `ζ_{p^n}^{a mod p^n} = ζ_{p^n}^a` for `a ∈ ℤ/p^m`, `n ≤ m`. -/
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

/-- `b_n(g|_{L_n}) = b_m(g) mod p^n` for `g ∈ Gal(L_m/K)`. -/
theorem finiteKummerExponent_restrict [hπ : NeZero π] {n m : ℕ} (h : n ≤ m)
    (g : falseTateLayer p π m m ≃ₐ[K] falseTateLayer p π m m) :
    finiteKummerExponent p π n (finiteLayerRestriction p π h g) =
      ZMod.castHom (pow_dvd_pow p h) (ZMod (p ^ n))
        (finiteKummerExponent p π m g) := by
  apply finiteKummerExponent_unique p π n
  rw [finiteLayerRestriction_radical]
  exact congrArg (· * layerRadical p π n)
    (layerRootOfUnity_pow_reduction p π h (finiteKummerExponent p π m g)).symm

/-- `χ_n(g|_{L_n}) = χ_m(g) mod p^n` for `g ∈ Gal(L_m/K)`. -/
theorem finiteCyclotomicCharacter_restrict [hπ : NeZero π] {n m : ℕ} (h : n ≤ m)
    (g : falseTateLayer p π m m ≃ₐ[K] falseTateLayer p π m m) :
    finiteCyclotomicCharacter p π n (finiteLayerRestriction p π h g) =
      ZMod.unitsMap (pow_dvd_pow p h) (finiteCyclotomicCharacter p π m g) := by
  apply finiteCyclotomicCharacter_unique p π n
  rw [finiteLayerRestriction_rootOfUnity]
  exact (layerRootOfUnity_pow_reduction p π h
    (finiteCyclotomicCharacter p π m g : ZMod (p ^ m))).symm

end

end FalseTateExtension
