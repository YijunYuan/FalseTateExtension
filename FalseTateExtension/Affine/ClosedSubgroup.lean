/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FalseTateExtension.Affine.Padic
public import FalseTateExtension.Padic.ClosedAddSubgroup
public import Mathlib.GroupTheory.Commutator.Basic

/-!
# Closed subgroups of the `p`-adic affine group

Let `G` be a closed subgroup of `ℤ_[p] ⋊ ℤ_[p]ˣ`. Its unit projection
`ρ = affineProjection G : G →* ℤ_[p]ˣ` is `(a, u) ↦ u`, and its translation kernel
`T(G) = affineTranslationKernel G = {a ∈ ℤ_[p] | (a, 1) ∈ G}` is a closed additive subgroup of
`ℤ_[p]`, which `a ↦ (a, 1)` identifies with `ker ρ`. Commutators with translations satisfy
`⁅g, (a, 1)⁆ = ((u - 1) a, 1)` for `g = (b, u)`. For a normal subgroup `I` of `G` the index
factors as `[G : I] = [ρ(G) : ρ(I)] · [T(G) : T(I)]`, where `T(I) = {a ∈ T(G) | (a, 1) ∈ I}`.

## Main results

* `affineProjection`, `affineTranslationKernel`, `affineTranslationHom`: the unit projection
  `ρ`, the translation kernel `T(G)` and the inclusion `T(G) → G`, `a ↦ (a, 1)`.
* `affineTranslationHom_range`: the image of `T(G)` in `G` is `ker ρ`.
* `affineTranslation_commutator`: `⁅g, (a, 1)⁆ = ((u - 1) a, 1)` in `G`.
* `affineTranslation_index_product`: `[G : I] = [ρ(G) : ρ(I)] · [T(G) : T(I)]` for `I ⊴ G`.

## References

* [Tong Liu, *On lattices in semi-stable representations: a proof of a conjecture of
  Breuil*](https://doi.org/10.1112/S0010437X0700317X), §5.1.
-/

@[expose] public section

namespace FalseTateExtension

noncomputable section

variable {p : ℕ} [Fact p.Prime]

open scoped commutatorElement

/-- In `ℤ_[p] ⋊ ℤ_[p]ˣ`, `⁅g, (m, 1)⁆ = ((u - 1) m, 1)`, where `u` is the unit coordinate
of `g`. -/
theorem padicAffine_commutator_inl (g : PadicAffineGroup p) (m : ℤ_[p]) :
    ⁅g, (SemidirectProduct.inl (Multiplicative.ofAdd m) : PadicAffineGroup p)⁆ =
      SemidirectProduct.inl (Multiplicative.ofAdd (((g.right : ℤ_[p]) - 1) * m)) :=
  AffineGroup.commutator_inl _ g m

/-- The unit projection `G →* ℤ_[p]ˣ`, `(a, u) ↦ u`, of a closed subgroup `G` of
`ℤ_[p] ⋊ ℤ_[p]ˣ`. -/
def affineProjection (G : ClosedSubgroup (PadicAffineGroup p)) : G →* (ℤ_[p])ˣ :=
  SemidirectProduct.rightHom.comp G.toSubgroup.subtype

/-- The unit projection of a closed subgroup of `ℤ_[p] ⋊ ℤ_[p]ˣ` is continuous. -/
theorem continuous_affineProjection (G : ClosedSubgroup (PadicAffineGroup p)) :
    Continuous (affineProjection G) :=
  (continuous_padicAffine_right p).comp continuous_subtype_val

/-- The translation kernel `T(G) = {a ∈ ℤ_[p] | (a, 1) ∈ G}` of a closed subgroup `G` of
`ℤ_[p] ⋊ ℤ_[p]ˣ`, a closed additive subgroup of `ℤ_[p]`. -/
def affineTranslationKernel (G : ClosedSubgroup (PadicAffineGroup p)) :
    ClosedAddSubgroup (ℤ_[p]) where
  toAddSubgroup := Subgroup.toAddSubgroup' (G.toSubgroup.comap SemidirectProduct.inl)
  isClosed' := by
    change IsClosed ((fun a : ℤ_[p] ↦
      (SemidirectProduct.inl (Multiplicative.ofAdd a) : PadicAffineGroup p)) ⁻¹' (G : Set _))
    apply G.isClosed'.preimage
    exact AffineGroup.continuous_inl _

/-- The inclusion `T(G) → G`, `a ↦ (a, 1)`, of the translation kernel, written
multiplicatively. -/
def affineTranslationHom (G : ClosedSubgroup (PadicAffineGroup p)) :
    Multiplicative (affineTranslationKernel G) →* G where
  toFun m := ⟨SemidirectProduct.inl (Multiplicative.ofAdd m.toAdd.val), m.toAdd.property⟩
  map_one' := Subtype.ext rfl
  map_mul' m n := by
    apply Subtype.ext
    exact map_mul SemidirectProduct.inl (Multiplicative.ofAdd m.toAdd.val)
      (Multiplicative.ofAdd n.toAdd.val)

/-- The inclusion `a ↦ (a, 1)` of `T(G)` into `G` is injective. -/
theorem affineTranslationHom_injective (G : ClosedSubgroup (PadicAffineGroup p)) :
    Function.Injective (affineTranslationHom G) := by
  intro m n h
  apply Multiplicative.toAdd.injective
  apply Subtype.ext
  have hh := congrArg (fun x : G ↦ x.val.left.toAdd) h
  change m.toAdd.val = n.toAdd.val at hh
  exact hh

/-- The image of `T(G)` under `a ↦ (a, 1)` is the kernel of the unit projection of `G`. -/
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

/-- For a normal subgroup `I` of `G`, `[G : I] = [ρ(G) : ρ(I)] · [ker ρ : I ∩ ker ρ]`, where
`ρ` is the unit projection. -/
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

/-- `[ker ρ : I ∩ ker ρ] = [T(G) : T(I)]`, where `T(I) = {a ∈ T(G) | (a, 1) ∈ I}`. -/
theorem affineTranslation_index (G : ClosedSubgroup (PadicAffineGroup p)) (I : Subgroup G) :
    I.relIndex (affineProjection G).ker = (I.comap (affineTranslationHom G)).index := by
  rw [Subgroup.index_comap, affineTranslationHom_range]

/-- For a normal subgroup `I` of `G`, `[G : I] = [ρ(G) : ρ(I)] · [T(G) : T(I)]`. -/
theorem affineTranslation_index_product (G : ClosedSubgroup (PadicAffineGroup p))
    (I : Subgroup G) [I.Normal] :
    I.index = (I.map (affineProjection G).rangeRestrict).index *
      (I.comap (affineTranslationHom G)).index := by
  rw [affineProjection_index, affineTranslation_index]

/-- In `G`, `⁅g, (m, 1)⁆ = ((u - 1) m, 1)` for `m ∈ T(G)`, where `u` is the unit coordinate
of `g`. -/
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
