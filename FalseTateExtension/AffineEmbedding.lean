/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FalseTateExtension.Coordinates.Padic
public import Mathlib.FieldTheory.Galois.Profinite
public import Mathlib.Algebra.Ring.AddAut
public import Mathlib.GroupTheory.SemidirectProduct
public import Mathlib.Topology.Homeomorph.TransferInstance
public import Mathlib.Topology.Algebra.Group.Units
public import Mathlib.Topology.Instances.ZMod

/-!
# The closed affine embedding of the actual false Tate Galois group

The canonical semidirect product of additive p-adic integers by their units is
given its product topology. The actual Kummer cocycle and cyclotomic character
define a continuous closed embedding of the Krull Galois group into it.
This proves blueprint `ft:affine-closed-embedding`, the topological part of the
compatible-coordinate realization in Liu, Section 5.1.
-/

@[expose] public section

namespace FalseTateExtension

noncomputable section

variable (p : ℕ) [Fact p.Prime]

/-- The usual action of p-adic units on additive p-adic integers, expressed in
the canonical multiplicative type tag for the semidirect product. -/
def padicAffineAction : (ℤ_[p])ˣ →* MulAut (Multiplicative (ℤ_[p])) :=
  (MulAutMultiplicative (ℤ_[p])).symm.toMonoidHom.comp AddAut.mulLeft

/-- The canonical affine semidirect product over the p-adic integers. -/
abbrev PadicAffineGroup :=
  SemidirectProduct (Multiplicative (ℤ_[p])) (ℤ_[p])ˣ (padicAffineAction p)

/-- The ordinary additive and unit coordinates of the canonical semidirect product. -/
def padicAffineEquivProd : PadicAffineGroup p ≃ ℤ_[p] × (ℤ_[p])ˣ :=
  SemidirectProduct.equivProd.trans
    (Equiv.prodCongr Multiplicative.toAdd (Equiv.refl _))

/-- The product topology on the canonical semidirect product. -/
instance padicAffineTopologicalSpace : TopologicalSpace (PadicAffineGroup p) :=
  (padicAffineEquivProd p).topologicalSpace

/-- The product coordinates identify the chosen topology with the product topology. -/
def padicAffineHomeomorphProd : PadicAffineGroup p ≃ₜ ℤ_[p] × (ℤ_[p])ˣ :=
  (padicAffineEquivProd p).homeomorph

instance padicAffineT2Space : T2Space (PadicAffineGroup p) :=
  (padicAffineHomeomorphProd p).symm.t2Space

theorem continuous_padicAffine_left :
    Continuous (fun x : PadicAffineGroup p ↦ x.left.toAdd) :=
  continuous_fst.comp (padicAffineHomeomorphProd p).continuous

theorem continuous_padicAffine_right :
    Continuous (fun x : PadicAffineGroup p ↦ x.right) :=
  continuous_snd.comp (padicAffineHomeomorphProd p).continuous

instance padicAffineIsTopologicalGroup : IsTopologicalGroup (PadicAffineGroup p) where
  continuous_mul := by
    apply continuous_induced_rng.mpr
    change Continuous (fun x : PadicAffineGroup p × PadicAffineGroup p ↦
      (x.1.left.toAdd + (x.1.right : ℤ_[p]) * x.2.left.toAdd, x.1.right * x.2.right))
    exact ((continuous_padicAffine_left p |>.comp continuous_fst).add
      ((Units.continuous_val.comp ((continuous_padicAffine_right p).comp continuous_fst)).mul
        (continuous_padicAffine_left p |>.comp continuous_snd))).prodMk
      ((continuous_padicAffine_right p |>.comp continuous_fst).mul
        (continuous_padicAffine_right p |>.comp continuous_snd))
  continuous_inv := by
    apply continuous_induced_rng.mpr
    change Continuous (fun x : PadicAffineGroup p ↦
      ((x.right⁻¹ : (ℤ_[p])ˣ) * (-x.left.toAdd), x.right⁻¹))
    exact ((Units.continuous_val.comp (continuous_padicAffine_right p).inv).mul
      (continuous_padicAffine_left p).neg).prodMk (continuous_padicAffine_right p).inv

/-- Continuity of every finite residue coordinate suffices for continuity into
the actual p-adic topology. -/
theorem _root_.PadicInt.continuous_of_toZModPow {X : Type*} [TopologicalSpace X]
    (f : X → ℤ_[p])
    (hf : ∀ n, Continuous (fun x ↦ PadicInt.toZModPow n (f x))) : Continuous f := by
  rw [continuous_iff_continuousAt]
  intro x
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨n, hn⟩ := PadicInt.exists_pow_neg_lt p hε
  have he : ∀ᶠ y in nhds x,
      PadicInt.toZModPow n (f y) = PadicInt.toZModPow n (f x) :=
    ((hf n).continuousAt (x := x)).eventually
      (p := fun t ↦ t = PadicInt.toZModPow n (f x)) (by simp)
  filter_upwards [he] with y hy
  apply lt_of_le_of_lt _ hn
  rw [dist_eq_norm, PadicInt.norm_le_pow_iff_mem_span_pow,
    ← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub, hy, sub_self]

variable {K : Type*} [Field K] [CharZero K] (π : K)

/-- Ordinary restriction to each actual diagonal layer is continuous for the
Krull topologies. The intermediate field inside the infinite field is the
actual image of the original inclusion. -/
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

/-- The canonical Kummer coordinate is continuous for the actual Krull topology. -/
theorem continuous_padicKummerExponent [hπ : NeZero π] :
    Continuous (padicKummerExponent p π) := by
  apply PadicInt.continuous_of_toZModPow p
  intro n
  simp_rw [padicKummerExponent_toZModPow]
  exact (continuous_of_discreteTopology : Continuous (finiteKummerExponent p π n)).comp
    (continuous_infiniteLayerRestriction p π n)

/-- The canonical cyclotomic character is continuous for the actual Krull topology. -/
theorem continuous_padicCyclotomicCharacter : Continuous (padicCyclotomicCharacter p π) :=
  _root_.cyclotomicCharacter.continuous p K (falseTateExtension p π)

/-- The actual Galois homomorphism into the canonical affine semidirect product. -/
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

/-- The affine homomorphism has the previously constructed actual coordinates. -/
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

/-- The actual false Tate Galois group embeds as a closed subgroup of the
Hausdorff topological affine group. -/
theorem isClosedEmbedding_affineGaloisHom [hπ : NeZero π] :
    Topology.IsClosedEmbedding (affineGaloisHom p π) := by
  have := falseTateExtension_isGalois p π
  exact (continuous_affineGaloisHom p π).isClosedEmbedding
    (affineGaloisHom_injective p π)

end

end FalseTateExtension
