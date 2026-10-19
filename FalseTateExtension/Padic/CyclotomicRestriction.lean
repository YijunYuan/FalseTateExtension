/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FalseTateExtension.GaloisLayers
public import FalseTateExtension.Mathlib.FieldTheory.RestrictNormal
public import Mathlib.FieldTheory.Galois.Profinite

/-!
# Restriction between cyclotomic layers

Restriction of `K`-automorphisms from `K(ζ_{p^∞})` to the finite layer `K(ζ_{p^m})`, and between
two finite layers. These are continuous surjections compatible with the inclusions of layers.
-/

@[expose] public section

noncomputable section

namespace FalseTateExtension

variable {K : Type*} [Field K] [CharZero K] (p : ℕ) [Fact p.Prime]

/-- Restriction from `K(ζ_{p^∞})` to the layer `K(ζ_{p^m})`. -/
def cyclotomicRestrictionToLayer (m : ℕ) :
    (cyclotomicExtension (K := K) p ≃ₐ[K] cyclotomicExtension (K := K) p) →*
      (cyclotomicLayer (K := K) p m ≃ₐ[K] cyclotomicLayer (K := K) p m) :=
  IntermediateField.restrictNormalHomOfLE (cyclotomicLayer_le_cyclotomicExtension p m)

theorem cyclotomicRestrictionToLayer_commutes (m : ℕ)
    (g : cyclotomicExtension (K := K) p ≃ₐ[K] cyclotomicExtension (K := K) p)
    (x : cyclotomicLayer (K := K) p m) :
    IntermediateField.inclusion (cyclotomicLayer_le_cyclotomicExtension p m)
        (cyclotomicRestrictionToLayer p m g x) =
      g (IntermediateField.inclusion (cyclotomicLayer_le_cyclotomicExtension p m) x) :=
  IntermediateField.restrictNormalHomOfLE_commutes _ g x

theorem cyclotomicRestrictionToLayer_surjective (m : ℕ) :
    Function.Surjective (cyclotomicRestrictionToLayer (K := K) p m) :=
  IntermediateField.restrictNormalHomOfLE_surjective _

/-- Restriction to a finite layer is continuous for the Krull topologies. -/
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

/-- Restriction from the layer `K(ζ_{p^n})` to `K(ζ_{p^m})`, `m ≤ n`. -/
def cyclotomicRestrictionBetweenLayers {m n : ℕ} (h : m ≤ n) :
    (cyclotomicLayer (K := K) p n ≃ₐ[K] cyclotomicLayer (K := K) p n) →*
      (cyclotomicLayer (K := K) p m ≃ₐ[K] cyclotomicLayer (K := K) p m) :=
  IntermediateField.restrictNormalHomOfLE (cyclotomicLayer_mono p h)

theorem cyclotomicRestrictionBetweenLayers_commutes {m n : ℕ} (h : m ≤ n)
    (g : cyclotomicLayer (K := K) p n ≃ₐ[K] cyclotomicLayer (K := K) p n)
    (x : cyclotomicLayer (K := K) p m) :
    IntermediateField.inclusion (cyclotomicLayer_mono p h)
        (cyclotomicRestrictionBetweenLayers p h g x) =
      g (IntermediateField.inclusion (cyclotomicLayer_mono p h) x) :=
  IntermediateField.restrictNormalHomOfLE_commutes _ g x

theorem cyclotomicRestrictionToLayer_comp {m n : ℕ} (h : m ≤ n) :
    cyclotomicRestrictionToLayer (K := K) p m =
      (cyclotomicRestrictionBetweenLayers p h).comp (cyclotomicRestrictionToLayer p n) :=
  (IntermediateField.restrictNormalHomOfLE_comp (cyclotomicLayer_mono p h)
    (cyclotomicLayer_le_cyclotomicExtension p n)).symm

end FalseTateExtension

end
