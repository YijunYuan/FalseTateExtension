/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FalseTateExtension.Affine.Padic
public import FalseTateExtension.Coordinates.Padic
public import FalseTateExtension.Mathlib.NumberTheory.Padics.Continuity
public import Mathlib.Algebra.Ring.AddAut
public import Mathlib.FieldTheory.Galois.Profinite
public import Mathlib.GroupTheory.SemidirectProduct
public import Mathlib.Topology.Algebra.Group.Units
public import Mathlib.Topology.Homeomorph.TransferInstance
public import Mathlib.Topology.Instances.ZMod

/-!
# The closed embedding of `Gal(K_FT/K)` into `ℤ_[p] ⋊ ℤ_[p]ˣ`

Let `K` be a field of characteristic zero, `π ∈ K` nonzero and `K_FT = K(π^{1/p^∞}, ζ_{p^∞})`.
The Kummer exponent `b : Gal(K_FT/K) → ℤ_[p]` and the cyclotomic character
`χ : Gal(K_FT/K) → ℤ_[p]ˣ` are continuous for the Krull topology, and the cocycle rule
`b(gh) = b(g) + χ(g) b(h)` makes `g ↦ (b(g), χ(g))` a homomorphism
`affineGaloisHom : Gal(K_FT/K) →* ℤ_[p] ⋊ ℤ_[p]ˣ`. It is injective and continuous, hence a
closed embedding of the compact group `Gal(K_FT/K)` into the Hausdorff group `ℤ_[p] ⋊ ℤ_[p]ˣ`.

## Main results

* `continuous_padicKummerExponent`, `continuous_padicCyclotomicCharacter`: `b` and `χ` are
  continuous.
* `affineGaloisHom`: the homomorphism `g ↦ (b(g), χ(g))`.
* `affineGaloisHom_injective`, `continuous_affineGaloisHom`.
* `isClosedEmbedding_affineGaloisHom`: `g ↦ (b(g), χ(g))` is a closed embedding.

## References

* [Tong Liu, *On lattices in semi-stable representations: a proof of a conjecture of
  Breuil*](https://doi.org/10.1112/S0010437X0700317X), §5.1.
-/

@[expose] public section

namespace FalseTateExtension

noncomputable section

variable (p : ℕ) [Fact p.Prime]

variable {K : Type*} [Field K] [CharZero K] (π : K)

/-- Restriction `Gal(K_FT/K) → Gal(K(π^{1/p^n}, ζ_{p^n})/K)` is continuous for the Krull
topology. -/
theorem continuous_infiniteLayerRestriction [hπ : NeZero π] (n : ℕ) :
    Continuous (infiniteLayerRestriction p π n) := by
  let i := IntermediateField.inclusion (falseTateLayer_le_falseTateExtension p π n n)
  let e := i.equivFieldRange
  have := falseTateLayer_isGalois p π n
  have : Module.Finite K i.fieldRange := Module.Finite.equiv e.toLinearEquiv
  have : IsGalois K i.fieldRange := IsGalois.of_algEquiv e
  have hc : Continuous (fun g : falseTateExtension p π ≃ₐ[K] falseTateExtension p π ↦
      e.symm.autCongr (AlgEquiv.restrictNormalHom i.fieldRange g)) :=
    continuous_of_discreteTopology.comp (InfiniteGalois.restrictNormalHom_continuous i.fieldRange)
  convert hc using 1
  funext g
  apply AlgEquiv.ext
  intro x
  apply (show Function.Injective i from i.injective)
  rw [infiniteLayerRestriction_commutes]
  change g (i x) = i (e.symm ((g.restrictNormal i.fieldRange) (e x)))
  have he (y : i.fieldRange) : i (e.symm y) = y := by
    change (e (e.symm y) : falseTateExtension p π) = _
    rw [e.apply_symm_apply]
  rw [he]
  exact (AlgEquiv.restrictNormal_commutes g i.fieldRange (e x)).symm

/-- The Kummer exponent `b : Gal(K_FT/K) → ℤ_[p]` is continuous. -/
theorem continuous_padicKummerExponent [hπ : NeZero π] :
    Continuous (padicKummerExponent p π) := by
  apply PadicInt.continuous_of_toZModPow
  intro n
  simp_rw [padicKummerExponent_toZModPow]
  exact (continuous_of_discreteTopology : Continuous (finiteKummerExponent p π n)).comp
    (continuous_infiniteLayerRestriction p π n)

/-- The cyclotomic character `χ : Gal(K_FT/K) → ℤ_[p]ˣ` is continuous. -/
theorem continuous_padicCyclotomicCharacter : Continuous (padicCyclotomicCharacter p π) :=
  continuous_intermediateFieldCyclotomicCharacter p _

/-- The homomorphism `Gal(K_FT/K) →* ℤ_[p] ⋊ ℤ_[p]ˣ`, `g ↦ (b(g), χ(g))`. -/
def affineGaloisHom [hπ : NeZero π] :
    (falseTateExtension p π ≃ₐ[K] falseTateExtension p π) →* PadicAffineGroup p where
  toFun g := ⟨Multiplicative.ofAdd (padicKummerExponent p π g),
    padicCyclotomicCharacter p π g⟩
  map_one' := by
    apply SemidirectProduct.ext
    · change Multiplicative.ofAdd (padicKummerExponent p π 1) = 1
      have h : padicKummerExponent p π 1 + padicKummerExponent p π 1 =
          padicKummerExponent p π 1 + 0 := by
        simpa using (padicKummerExponent_mul p π 1 1).symm
      rw [add_left_cancel h]
      rfl
    · exact map_one (padicCyclotomicCharacter p π)
  map_mul' g h := by
    apply SemidirectProduct.ext
    · exact congrArg Multiplicative.ofAdd (padicKummerExponent_mul p π g h)
    · exact map_mul (padicCyclotomicCharacter p π) g h

/-- The coordinates of `affineGaloisHom g` are `(b(g), χ(g))`. -/
theorem affineGaloisHom_coordinates [hπ : NeZero π]
    (g : falseTateExtension p π ≃ₐ[K] falseTateExtension p π) :
    padicAffineHomeomorphProd p (affineGaloisHom p π g) =
      (padicKummerExponent p π g, padicCyclotomicCharacter p π g) := rfl

/-- `g ↦ (b(g), χ(g))` is injective on `Gal(K_FT/K)`. -/
theorem affineGaloisHom_injective [hπ : NeZero π] :
    Function.Injective (affineGaloisHom p π) := by
  intro g h heq
  apply padicCoordinates_injective p π
  exact congrArg (padicAffineHomeomorphProd p) heq

/-- `g ↦ (b(g), χ(g))` is continuous on `Gal(K_FT/K)`. -/
theorem continuous_affineGaloisHom [hπ : NeZero π] :
    Continuous (affineGaloisHom p π) := by
  apply continuous_induced_rng.mpr
  exact (continuous_padicKummerExponent p π).prodMk
    (continuous_padicCyclotomicCharacter p π)

/-- `g ↦ (b(g), χ(g))` is a closed embedding `Gal(K_FT/K) → ℤ_[p] ⋊ ℤ_[p]ˣ`. -/
theorem isClosedEmbedding_affineGaloisHom [hπ : NeZero π] :
    Topology.IsClosedEmbedding (affineGaloisHom p π) := by
  have := falseTateExtension_isGalois p π
  exact (continuous_affineGaloisHom p π).isClosedEmbedding
    (affineGaloisHom_injective p π)

end

end FalseTateExtension
