/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FalseTateExtension.Coordinates.Padic
public import FalseTateExtension.Affine.Padic
public import FalseTateExtension.Mathlib.NumberTheory.Padics.Continuity
public import Mathlib.FieldTheory.Galois.Profinite
public import Mathlib.Algebra.Ring.AddAut
public import Mathlib.GroupTheory.SemidirectProduct
public import Mathlib.Topology.Homeomorph.TransferInstance
public import Mathlib.Topology.Algebra.Group.Units
public import Mathlib.Topology.Instances.ZMod

/-!
# The closed affine embedding of the false Tate Galois group

The semidirect product of additive p-adic integers by their units is
given its product topology. The Kummer cocycle and cyclotomic character
define a continuous closed embedding of the Krull Galois group into it.
This proves blueprint `ft:affine-closed-embedding`, the topological part of the
compatible-coordinate realization in Liu, Section 5.1.
-/

@[expose] public section

namespace FalseTateExtension

noncomputable section

variable (p : ℕ) [Fact p.Prime]

variable {K : Type*} [Field K] [CharZero K] (π : K)

/-- Restriction to each diagonal layer is continuous for the
Krull topologies. The intermediate field inside the infinite field is the
image of the inclusion. -/
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

/-- The Kummer coordinate is continuous for the Krull topology. -/
theorem continuous_padicKummerExponent [hπ : NeZero π] :
    Continuous (padicKummerExponent p π) := by
  apply PadicInt.continuous_of_toZModPow
  intro n
  simp_rw [padicKummerExponent_toZModPow]
  exact (continuous_of_discreteTopology : Continuous (finiteKummerExponent p π n)).comp
    (continuous_infiniteLayerRestriction p π n)

/-- The cyclotomic character is continuous for the Krull topology. -/
theorem continuous_padicCyclotomicCharacter : Continuous (padicCyclotomicCharacter p π) :=
  _root_.cyclotomicCharacter.continuous p K (falseTateExtension p π)

/-- The Galois homomorphism into the affine semidirect product. -/
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

/-- The affine homomorphism has the previously constructed coordinates. -/
theorem affineGaloisHom_coordinates [hπ : NeZero π]
    (g : falseTateExtension p π ≃ₐ[K] falseTateExtension p π) :
    padicAffineHomeomorphProd p (affineGaloisHom p π g) =
      (padicKummerExponent p π g, padicCyclotomicCharacter p π g) := rfl

theorem affineGaloisHom_injective [hπ : NeZero π] :
    Function.Injective (affineGaloisHom p π) := by
  intro g h heq
  apply padicCoordinates_injective p π
  exact congrArg (padicAffineHomeomorphProd p) heq

theorem continuous_affineGaloisHom [hπ : NeZero π] :
    Continuous (affineGaloisHom p π) := by
  apply continuous_induced_rng.mpr
  exact (continuous_padicKummerExponent p π).prodMk
    (continuous_padicCyclotomicCharacter p π)

/-- The false Tate Galois group embeds as a closed subgroup of the
Hausdorff topological affine group. -/
theorem isClosedEmbedding_affineGaloisHom [hπ : NeZero π] :
    Topology.IsClosedEmbedding (affineGaloisHom p π) := by
  have := falseTateExtension_isGalois p π
  exact (continuous_affineGaloisHom p π).isClosedEmbedding
    (affineGaloisHom_injective p π)

end

end FalseTateExtension
