/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FalseTateExtension.Coordinates.AffineEmbedding
public import FalseTateExtension.Padic.ClosedAddSubgroup
public import Mathlib.GroupTheory.Commutator.Basic

/-!
# Open normal subgroups from affine commutators

In the p-adic affine group, commutators with translations multiply
their additive coordinate by the difference of the unit coordinate and one.
For a closed subgroup, this identity and finite indices of nonzero scalar
images imply openness of a closed normal subgroup whose projection is open
and contains a nonidentity unit.
This proves blueprint `ft:affine-commutator`.
-/

@[expose] public section

namespace FalseTateExtension

noncomputable section

variable {p : ℕ} [Fact p.Prime]

open scoped commutatorElement

/-- The affine commutator formula holds in the semidirect product. -/
theorem padicAffine_commutator_inl (g : PadicAffineGroup p) (m : ℤ_[p]) :
    ⁅g, (SemidirectProduct.inl (Multiplicative.ofAdd m) : PadicAffineGroup p)⁆ =
      SemidirectProduct.inl (Multiplicative.ofAdd (((g.right : ℤ_[p]) - 1) * m)) :=
  AffineGroup.commutator_inl _ g m

/-- The right-coordinate homomorphism on a closed affine subgroup. -/
def affineProjection (G : ClosedSubgroup (PadicAffineGroup p)) : G →* (ℤ_[p])ˣ :=
  SemidirectProduct.rightHom.comp G.toSubgroup.subtype

theorem continuous_affineProjection (G : ClosedSubgroup (PadicAffineGroup p)) :
    Continuous (affineProjection G) :=
  (continuous_padicAffine_right p).comp continuous_subtype_val

/-- The closed additive translation kernel of a closed affine subgroup. -/
def affineTranslationKernel (G : ClosedSubgroup (PadicAffineGroup p)) :
    ClosedAddSubgroup (ℤ_[p]) where
  toAddSubgroup := Subgroup.toAddSubgroup' (G.toSubgroup.comap SemidirectProduct.inl)
  isClosed' := by
    change IsClosed ((fun a : ℤ_[p] ↦
      (SemidirectProduct.inl (Multiplicative.ofAdd a) : PadicAffineGroup p)) ⁻¹' (G : Set _))
    apply G.isClosed'.preimage
    exact AffineGroup.continuous_inl _

/-- The inclusion of the translation kernel into the affine subgroup. -/
def affineTranslationHom (G : ClosedSubgroup (PadicAffineGroup p)) :
    Multiplicative (affineTranslationKernel G) →* G where
  toFun m := ⟨SemidirectProduct.inl (Multiplicative.ofAdd m.toAdd.val), m.toAdd.property⟩
  map_one' := Subtype.ext rfl
  map_mul' m n := by
    apply Subtype.ext
    exact map_mul SemidirectProduct.inl (Multiplicative.ofAdd m.toAdd.val)
      (Multiplicative.ofAdd n.toAdd.val)

theorem affineTranslationHom_injective (G : ClosedSubgroup (PadicAffineGroup p)) :
    Function.Injective (affineTranslationHom G) := by
  intro m n h
  apply Multiplicative.toAdd.injective
  apply Subtype.ext
  have hh := congrArg (fun x : G ↦ x.val.left.toAdd) h
  change m.toAdd.val = n.toAdd.val at hh
  exact hh

/-- The range of the translation inclusion is precisely the projection kernel. -/
theorem affineTranslationHom_range (G : ClosedSubgroup (PadicAffineGroup p)) :
    (affineTranslationHom G).range = (affineProjection G).ker := by
  ext g
  constructor
  · rintro ⟨m, rfl⟩
    change (affineProjection G) (affineTranslationHom G m) = 1
    rfl
  · intro hg
    have hright : g.val.right = 1 := hg
    have heq : SemidirectProduct.inl g.val.left = g.val :=
      SemidirectProduct.ext rfl hright.symm
    refine ⟨Multiplicative.ofAdd ⟨g.val.left.toAdd, ?_⟩, ?_⟩
    · change SemidirectProduct.inl g.val.left ∈ G
      rw [heq]
      exact g.property
    · apply Subtype.ext
      change SemidirectProduct.inl g.val.left = g.val
      exact heq

/-- The projection image and translation kernel give the index
product, with the natural-number index convention. -/
theorem affineProjection_index (G : ClosedSubgroup (PadicAffineGroup p))
    (I : Subgroup G) [I.Normal] :
    I.index = (I.map (affineProjection G).rangeRestrict).index *
      I.relIndex (affineProjection G).ker := by
  let ρ := (affineProjection G).rangeRestrict
  have hr : ρ.range = ⊤ :=
    ρ.range_eq_top_of_surjective (affineProjection G).rangeRestrict_surjective
  have hj := I.index_map ρ
  rw [hr, Subgroup.index_top, mul_one] at hj
  calc
    I.index = I.relIndex (I ⊔ ρ.ker) * (I ⊔ ρ.ker).index :=
      (Subgroup.relIndex_mul_index (show I ≤ I ⊔ ρ.ker from le_sup_left)).symm
    _ = I.relIndex ρ.ker * (I.map ρ).index := by rw [Subgroup.relIndex_sup_left, hj]
    _ = (I.map ρ).index * I.relIndex ρ.ker := mul_comm _ _
    _ = _ := by simp only [ρ, MonoidHom.ker_rangeRestrict]

/-- The relative kernel index is the index of the intersection pulled
back to the translation group. -/
theorem affineTranslation_index (G : ClosedSubgroup (PadicAffineGroup p)) (I : Subgroup G) :
    I.relIndex (affineProjection G).ker = (I.comap (affineTranslationHom G)).index := by
  rw [Subgroup.index_comap, affineTranslationHom_range]

/-- The index product expressed directly on the additive translation
kernel, with its multiplicative type tag. -/
theorem affineTranslation_index_product (G : ClosedSubgroup (PadicAffineGroup p))
    (I : Subgroup G) [I.Normal] :
    I.index = (I.map (affineProjection G).rangeRestrict).index *
      (I.comap (affineTranslationHom G)).index := by
  rw [affineProjection_index, affineTranslation_index]

/-- The ambient affine formula is the commutator in the closed subgroup. -/
theorem affineTranslation_commutator (G : ClosedSubgroup (PadicAffineGroup p))
    (g : G) (m : affineTranslationKernel G) :
    ⁅g, affineTranslationHom G (Multiplicative.ofAdd m)⁆ =
      affineTranslationHom G (Multiplicative.ofAdd
        ⟨((g.val.right : ℤ_[p]) - 1) * m.val,
          PadicInt.mul_mem_closedAddSubgroup (affineTranslationKernel G) _ _ m.property⟩) := by
  apply Subtype.ext
  change (G.toSubgroup.subtype ⁅g, affineTranslationHom G (Multiplicative.ofAdd m)⁆) = _
  rw [map_commutatorElement]
  exact padicAffine_commutator_inl g.val m.val

end

end FalseTateExtension
