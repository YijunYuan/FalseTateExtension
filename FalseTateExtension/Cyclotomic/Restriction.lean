/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FalseTateExtension.Layers.Galois
public import FalseTateExtension.Mathlib.FieldTheory.RestrictNormal
public import Mathlib.FieldTheory.Galois.Profinite

/-!
# Restriction between cyclotomic layers

For a field `K` of characteristic zero, restriction of `K`-automorphisms from `K(ζ_{p^∞})` to
the finite layer `K(ζ_{p^m})`, and from `K(ζ_{p^n})` to `K(ζ_{p^m})` for `m ≤ n`, are surjective
group homomorphisms compatible with the inclusions of the layers; restriction from `K(ζ_{p^∞})`
is continuous for the Krull topology and factors through every intermediate layer.

## Main results

* `cyclotomicRestrictionToLayer`: `Gal(K(ζ_{p^∞})/K) →* Gal(K(ζ_{p^m})/K)`
* `cyclotomicRestrictionBetweenLayers`: `Gal(K(ζ_{p^n})/K) →* Gal(K(ζ_{p^m})/K)` for `m ≤ n`
* `cyclotomicRestrictionToLayer_surjective`, `continuous_cyclotomicRestrictionToLayer`
* `cyclotomicRestrictionToLayer_comp`: restriction to `K(ζ_{p^m})` factors through `K(ζ_{p^n})`
-/

@[expose] public section

noncomputable section

namespace FalseTateExtension

variable {K : Type*} [Field K] [CharZero K] (p : ℕ) [Fact p.Prime]

/-- The restriction homomorphism `Gal(K(ζ_{p^∞})/K) →* Gal(K(ζ_{p^m})/K)`. -/
def cyclotomicRestrictionToLayer (m : ℕ) :
    (cyclotomicExtension (K := K) p ≃ₐ[K] cyclotomicExtension (K := K) p) →*
      (cyclotomicLayer (K := K) p m ≃ₐ[K] cyclotomicLayer (K := K) p m) :=
  IntermediateField.restrictNormalHomOfLE (cyclotomicLayer_le_cyclotomicExtension p m)

/-- The restriction of `g` to `K(ζ_{p^m})` agrees with `g` on `K(ζ_{p^m}) ⊆ K(ζ_{p^∞})`. -/
theorem cyclotomicRestrictionToLayer_commutes (m : ℕ)
    (g : cyclotomicExtension (K := K) p ≃ₐ[K] cyclotomicExtension (K := K) p)
    (x : cyclotomicLayer (K := K) p m) :
    IntermediateField.inclusion (cyclotomicLayer_le_cyclotomicExtension p m)
        (cyclotomicRestrictionToLayer p m g x) =
      g (IntermediateField.inclusion (cyclotomicLayer_le_cyclotomicExtension p m) x) :=
  IntermediateField.restrictNormalHomOfLE_commutes _ g x

/-- Restriction `Gal(K(ζ_{p^∞})/K) → Gal(K(ζ_{p^m})/K)` is surjective. -/
theorem cyclotomicRestrictionToLayer_surjective (m : ℕ) :
    Function.Surjective (cyclotomicRestrictionToLayer (K := K) p m) :=
  IntermediateField.restrictNormalHomOfLE_surjective _

/-- Restriction `Gal(K(ζ_{p^∞})/K) → Gal(K(ζ_{p^m})/K)` is continuous for the Krull topology. -/
theorem continuous_cyclotomicRestrictionToLayer (m : ℕ) :
    Continuous (cyclotomicRestrictionToLayer (K := K) p m) := by
  let i := IntermediateField.inclusion (cyclotomicLayer_le_cyclotomicExtension (K := K) p m)
  let e := i.equivFieldRange
  have : Module.Finite K i.fieldRange := Module.Finite.equiv e.toLinearEquiv
  have : IsGalois K i.fieldRange := IsGalois.of_algEquiv e
  have hc : Continuous (fun g : cyclotomicExtension (K := K) p ≃ₐ[K]
      cyclotomicExtension (K := K) p ↦
      e.symm.autCongr (AlgEquiv.restrictNormalHom i.fieldRange g)) :=
    continuous_of_discreteTopology.comp (InfiniteGalois.restrictNormalHom_continuous i.fieldRange)
  convert hc using 1
  funext g
  apply AlgEquiv.ext
  intro x
  apply (show Function.Injective i from i.injective)
  rw [cyclotomicRestrictionToLayer_commutes]
  change g (i x) = i (e.symm ((g.restrictNormal i.fieldRange) (e x)))
  have he (y : i.fieldRange) : i (e.symm y) = y := by
    change (e (e.symm y) : cyclotomicExtension (K := K) p) = _
    rw [e.apply_symm_apply]
  rw [he]
  exact (AlgEquiv.restrictNormal_commutes g i.fieldRange (e x)).symm

/-- The restriction homomorphism `Gal(K(ζ_{p^n})/K) →* Gal(K(ζ_{p^m})/K)` for `m ≤ n`. -/
def cyclotomicRestrictionBetweenLayers {m n : ℕ} (h : m ≤ n) :
    (cyclotomicLayer (K := K) p n ≃ₐ[K] cyclotomicLayer (K := K) p n) →*
      (cyclotomicLayer (K := K) p m ≃ₐ[K] cyclotomicLayer (K := K) p m) :=
  IntermediateField.restrictNormalHomOfLE (cyclotomicLayer_mono p h)

/-- The restriction of `g` to `K(ζ_{p^m})` agrees with `g` on `K(ζ_{p^m}) ⊆ K(ζ_{p^n})`. -/
theorem cyclotomicRestrictionBetweenLayers_commutes {m n : ℕ} (h : m ≤ n)
    (g : cyclotomicLayer (K := K) p n ≃ₐ[K] cyclotomicLayer (K := K) p n)
    (x : cyclotomicLayer (K := K) p m) :
    IntermediateField.inclusion (cyclotomicLayer_mono p h)
        (cyclotomicRestrictionBetweenLayers p h g x) =
      g (IntermediateField.inclusion (cyclotomicLayer_mono p h) x) :=
  IntermediateField.restrictNormalHomOfLE_commutes _ g x

/-- For `m ≤ n`, restriction from `K(ζ_{p^∞})` to `K(ζ_{p^m})` is restriction to `K(ζ_{p^n})`
followed by restriction to `K(ζ_{p^m})`. -/
theorem cyclotomicRestrictionToLayer_comp {m n : ℕ} (h : m ≤ n) :
    cyclotomicRestrictionToLayer (K := K) p m =
      (cyclotomicRestrictionBetweenLayers p h).comp (cyclotomicRestrictionToLayer p n) :=
  (IntermediateField.restrictNormalHomOfLE_comp (cyclotomicLayer_mono p h)
    (cyclotomicLayer_le_cyclotomicExtension p n)).symm

end FalseTateExtension

end
