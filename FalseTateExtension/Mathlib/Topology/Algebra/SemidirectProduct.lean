/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import Mathlib.GroupTheory.SemidirectProduct
public import Mathlib.Topology.Algebra.Group.Basic
public import Mathlib.Topology.Homeomorph.Lemmas
public import Mathlib.Topology.Separation.Hausdorff

/-!
# The product topology on a semidirect product

`N ⋊[φ] G` carries the product topology of `N × G`. When the action
`G × N → N`, `(g, n) ↦ φ g n` is continuous (`SemidirectProduct.ContinuousAct φ`) and `N`, `G`
are topological groups, so is `N ⋊[φ] G`.

Upstream candidate: `Mathlib.Topology.Algebra.Group.SemidirectProduct`.
-/

@[expose] public section

namespace SemidirectProduct

variable {N G : Type*} [Group N] [Group G] {φ : G →* MulAut N}
variable [TopologicalSpace N] [TopologicalSpace G]

instance : TopologicalSpace (N ⋊[φ] G) :=
  TopologicalSpace.induced (equivProd : N ⋊[φ] G → N × G) inferInstance

/-- The coordinates `N ⋊[φ] G ≃ₜ N × G`. -/
def homeomorphProd : N ⋊[φ] G ≃ₜ N × G :=
  (equivProd : N ⋊[φ] G ≃ N × G).toHomeomorphOfIsInducing ⟨rfl⟩

/-- The product homeomorphism sends an element to its two coordinates. -/
@[simp] theorem homeomorphProd_apply (x : N ⋊[φ] G) : homeomorphProd x = (x.left, x.right) := rfl

/-- The first coordinate of a semidirect product is continuous. -/
theorem continuous_left : Continuous (left : N ⋊[φ] G → N) :=
  continuous_fst.comp (homeomorphProd (φ := φ)).continuous

/-- The second coordinate of a semidirect product is continuous. -/
theorem continuous_right : Continuous (right : N ⋊[φ] G → G) :=
  continuous_snd.comp (homeomorphProd (φ := φ)).continuous

/-- The inclusion of the first factor into a semidirect product is continuous. -/
theorem continuous_inl : Continuous (inl : N → N ⋊[φ] G) :=
  continuous_induced_rng.mpr (continuous_id.prodMk continuous_const)

/-- The inclusion of the second factor into a semidirect product is continuous. -/
theorem continuous_inr : Continuous (inr : G → N ⋊[φ] G) :=
  continuous_induced_rng.mpr (continuous_const.prodMk continuous_id)

/-- The homomorphism projecting to the second factor is continuous. -/
theorem continuous_rightHom : Continuous (rightHom : N ⋊[φ] G → G) := continuous_right

/-- A semidirect product of Hausdorff groups is Hausdorff in the product topology. -/
instance [T2Space N] [T2Space G] : T2Space (N ⋊[φ] G) :=
  (homeomorphProd (φ := φ)).symm.t2Space

/-- A semidirect product of compact groups is compact in the product topology. -/
instance [CompactSpace N] [CompactSpace G] : CompactSpace (N ⋊[φ] G) :=
  (homeomorphProd (φ := φ)).symm.compactSpace

/-- The action of `G` on `N` defining the semidirect product is jointly continuous. -/
class ContinuousAct (φ : G →* MulAut N) : Prop where
  /-- The action map is continuous jointly in the group element and the point acted on. -/
  continuous_act : Continuous fun p : G × N => φ p.1 p.2

/-- A continuous action makes the semidirect product of topological groups a topological group. -/
instance [IsTopologicalGroup N] [IsTopologicalGroup G] [ContinuousAct φ] :
    IsTopologicalGroup (N ⋊[φ] G) where
  continuous_mul := by
    apply continuous_induced_rng.mpr
    change Continuous fun x : (N ⋊[φ] G) × (N ⋊[φ] G) =>
      (x.1.left * φ x.1.right x.2.left, x.1.right * x.2.right)
    exact ((continuous_left.comp continuous_fst).mul
      (ContinuousAct.continuous_act.comp ((continuous_right.comp continuous_fst).prodMk
        (continuous_left.comp continuous_snd)))).prodMk
      ((continuous_right.comp continuous_fst).mul (continuous_right.comp continuous_snd))
  continuous_inv := by
    apply continuous_induced_rng.mpr
    change Continuous fun x : N ⋊[φ] G => (φ x.right⁻¹ x.left⁻¹, x.right⁻¹)
    exact (ContinuousAct.continuous_act.comp (continuous_right.inv.prodMk
      continuous_left.inv)).prodMk continuous_right.inv

end SemidirectProduct
