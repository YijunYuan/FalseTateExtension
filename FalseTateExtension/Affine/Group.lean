/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FalseTateExtension.Mathlib.Topology.Algebra.SemidirectProduct
public import Mathlib.Algebra.Ring.AddAut
public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.Topology.Algebra.Group.Units
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Tactic.Ring

/-!
# The affine group of a commutative ring

For a commutative topological ring `A` and a group `H` with a homomorphism `ι : H →* Aˣ`, the
affine group `AffineGroup A ι = A ⋊ H` is the semidirect product of the additive group of `A`
(written multiplicatively) by `H` acting through multiplication by `ι h`. Its elements are the
maps `x ↦ ι h * x + a`. With the product topology it is a topological group, Hausdorff and
compact when `A` and `H` are.

The library uses `AffineGroup ℤ_[p] (MonoidHom.id ℤ_[p]ˣ)` (the Galois group of `K_FT/K`
embeds into it), `AffineGroup ℤ_[p] H.subtype` for a subgroup `H ≤ ℤ_[p]ˣ`, and
`AffineGroup (ZMod (p ^ n)) _` for the finite layers.

## Main results

* `AffineGroup.commutator_inl`: `⁅g, inl a⁆ = inl ((ι g.right - 1) * a)`.
* `AffineGroup.instIsTopologicalGroup`, `AffineGroup.instCompactSpace`.
-/

@[expose] public section

namespace FalseTateExtension

variable (A : Type*) [CommRing A] {H : Type*} [Group H]

/-- `H` acts on the additive group of `A` by multiplication through `ι`. -/
def affineAction (ι : H →* Aˣ) : H →* MulAut (Multiplicative A) :=
  ((MulAutMultiplicative A).symm.toMonoidHom.comp AddAut.mulLeft).comp ι

@[simp] theorem affineAction_apply (ι : H →* Aˣ) (h : H) (a : A) :
    affineAction A ι h (Multiplicative.ofAdd a) = Multiplicative.ofAdd ((ι h : A) * a) := rfl

/-- The affine group `A ⋊ H`, `H` acting on `A` by multiplication through `ι`. -/
abbrev AffineGroup (ι : H →* Aˣ) : Type _ :=
  Multiplicative A ⋊[affineAction A ι] H

namespace AffineGroup

open scoped commutatorElement

variable {A} (ι : H →* Aˣ)

theorem commutator_inl (g : AffineGroup A ι) (a : A) :
    ⁅g, (SemidirectProduct.inl (Multiplicative.ofAdd a) : AffineGroup A ι)⁆ =
      SemidirectProduct.inl (Multiplicative.ofAdd (((ι g.right : A) - 1) * a)) := by
  apply SemidirectProduct.ext
  · simp only [commutatorElement_def, SemidirectProduct.mul_left,
      SemidirectProduct.mul_right, SemidirectProduct.inv_left, SemidirectProduct.inv_right,
      SemidirectProduct.left_inl, SemidirectProduct.right_inl, mul_one, mul_inv_cancel,
      inv_one, map_one, MulAut.one_apply]
    apply congrArg Multiplicative.ofAdd
    change g.left.toAdd + (ι g.right : A) * a +
      (ι g.right : A) * ((ι g.right⁻¹ : A) * -g.left.toAdd) + -a = _
    rw [map_inv, ← mul_assoc, Units.mul_inv, one_mul]
    ring
  · simp [commutatorElement_def]

section Topology

variable [TopologicalSpace A] [TopologicalSpace H]

/-- The coordinates `AffineGroup A ι ≃ₜ A × H`. -/
def homeomorphProd : AffineGroup A ι ≃ₜ A × H :=
  (SemidirectProduct.homeomorphProd (φ := affineAction A ι)).trans
    (Homeomorph.prodCongr
      { Multiplicative.toAdd with
        continuous_toFun := continuous_toAdd, continuous_invFun := continuous_ofAdd }
      (Homeomorph.refl H))

@[simp] theorem homeomorphProd_apply (x : AffineGroup A ι) :
    homeomorphProd ι x = (x.left.toAdd, x.right) := rfl

theorem continuous_left : Continuous fun x : AffineGroup A ι => x.left.toAdd :=
  continuous_fst.comp (homeomorphProd ι).continuous

theorem continuous_right : Continuous fun x : AffineGroup A ι => x.right :=
  SemidirectProduct.continuous_right

theorem continuous_inl : Continuous fun a : A =>
    (SemidirectProduct.inl (Multiplicative.ofAdd a) : AffineGroup A ι) :=
  SemidirectProduct.continuous_inl.comp continuous_ofAdd

variable [IsTopologicalRing A]

/-- The action is continuous as soon as `h ↦ (ι h : A)` is. -/
theorem continuousAct_of_continuous (hι : Continuous fun h : H => (ι h : A)) :
    SemidirectProduct.ContinuousAct (affineAction A ι) where
  continuous_act := by
    change Continuous fun p : H × Multiplicative A =>
      Multiplicative.ofAdd ((ι p.1 : A) * Multiplicative.toAdd p.2)
    exact continuous_ofAdd.comp ((hι.comp continuous_fst).mul
      (continuous_toAdd.comp continuous_snd))

instance : SemidirectProduct.ContinuousAct (affineAction A (MonoidHom.id Aˣ)) :=
  continuousAct_of_continuous _ Units.continuous_val

instance (S : Subgroup Aˣ) : SemidirectProduct.ContinuousAct (affineAction A S.subtype) :=
  continuousAct_of_continuous _ (Units.continuous_val.comp continuous_subtype_val)

end Topology

end AffineGroup

end FalseTateExtension
