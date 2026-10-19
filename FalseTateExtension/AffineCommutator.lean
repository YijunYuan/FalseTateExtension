/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FalseTateExtension.AffineEmbedding
public import FalseTateExtension.Padic.ClosedAddSubgroup
public import Mathlib.GroupTheory.Commutator.Basic

/-!
# Open normal subgroups from affine commutators

In the actual p-adic affine group, commutators with translations multiply
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

/-- The usual affine commutator formula holds in the canonical semidirect product. -/
theorem padicAffine_commutator_inl (g : PadicAffineGroup p) (m : ℤ_[p]) :
    ⁅g, (SemidirectProduct.inl (Multiplicative.ofAdd m) : PadicAffineGroup p)⁆ =
      SemidirectProduct.inl (Multiplicative.ofAdd (((g.right : ℤ_[p]) - 1) * m)) := by
  apply SemidirectProduct.ext
  · simp only [commutatorElement_def, SemidirectProduct.mul_left,
      SemidirectProduct.mul_right, SemidirectProduct.inv_left, SemidirectProduct.inv_right,
      SemidirectProduct.left_inl, SemidirectProduct.right_inl, mul_one, mul_inv_cancel,
      inv_one, map_one, MulAut.one_apply]
    apply congrArg Multiplicative.ofAdd
    change g.left.toAdd + (g.right : ℤ_[p]) * m +
      (g.right : ℤ_[p]) * ((g.right⁻¹ : (ℤ_[p])ˣ) * -g.left.toAdd) + -m = _
    have hu := congrArg (fun u : (ℤ_[p])ˣ ↦ (u : ℤ_[p]))
      (mul_inv_cancel g.right)
    change (g.right : ℤ_[p]) * (g.right⁻¹ : (ℤ_[p])ˣ) = 1 at hu
    rw [← mul_assoc, hu, one_mul]
    ring
  · simp [commutatorElement_def]

instance padicAffineCompactSpace : CompactSpace (PadicAffineGroup p) :=
  (padicAffineHomeomorphProd p).symm.compactSpace

/-- The actual right-coordinate homomorphism on a closed affine subgroup. -/
def affineProjection (G : ClosedSubgroup (PadicAffineGroup p)) : G →* (ℤ_[p])ˣ :=
  SemidirectProduct.rightHom.comp G.toSubgroup.subtype

theorem continuous_affineProjection (G : ClosedSubgroup (PadicAffineGroup p)) :
    Continuous (affineProjection G) :=
  (continuous_padicAffine_right p).comp continuous_subtype_val

/-- The actual closed additive translation kernel of a closed affine subgroup. -/
def affineTranslationKernel (G : ClosedSubgroup (PadicAffineGroup p)) :
    ClosedAddSubgroup (ℤ_[p]) where
  toAddSubgroup := Subgroup.toAddSubgroup' (G.toSubgroup.comap SemidirectProduct.inl)
  isClosed' := by
    change IsClosed ((fun a : ℤ_[p] ↦
      (SemidirectProduct.inl (Multiplicative.ofAdd a) : PadicAffineGroup p)) ⁻¹' (G : Set _))
    apply G.isClosed'.preimage
    apply continuous_induced_rng.mpr
    exact continuous_id.prodMk continuous_const

/-- The canonical inclusion of the actual translation kernel into the affine subgroup. -/
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

/-- The range of the actual translation inclusion is precisely the projection kernel. -/
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

/-- The actual projection image and translation kernel give the usual index
product, with the ordinary natural-number index convention. -/
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

/-- The relative kernel index is the actual index of the intersection pulled
back to the canonical translation group. -/
theorem affineTranslation_index (G : ClosedSubgroup (PadicAffineGroup p)) (I : Subgroup G) :
    I.relIndex (affineProjection G).ker = (I.comap (affineTranslationHom G)).index := by
  rw [Subgroup.index_comap, affineTranslationHom_range]

/-- The index product expressed directly on the actual additive translation
kernel, with its canonical multiplicative type tag. -/
theorem affineTranslation_index_product (G : ClosedSubgroup (PadicAffineGroup p))
    (I : Subgroup G) [I.Normal] :
    I.index = (I.map (affineProjection G).rangeRestrict).index *
      (I.comap (affineTranslationHom G)).index := by
  rw [affineProjection_index, affineTranslation_index]

/-- The ambient affine formula is the actual commutator in the closed subgroup. -/
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

/-- Every scalar translation arising from an element of `I` is an actual
commutator in `G`, and belongs to both `I` and the translation kernel. -/
theorem affineTranslation_scalar_mem (G : ClosedSubgroup (PadicAffineGroup p))
    (I : Subgroup G) [I.Normal] (g : I) (m : affineTranslationKernel G) :
    affineTranslationHom G (Multiplicative.ofAdd
      ⟨((g.val.val.right : ℤ_[p]) - 1) * m.val,
        PadicInt.mul_mem_closedAddSubgroup (affineTranslationKernel G) _ _ m.property⟩) ∈
      (_root_.commutator G ⊓ I ⊓ (affineProjection G).ker) := by
  rw [← affineTranslation_commutator G g.val m]
  have hm : affineTranslationHom G (Multiplicative.ofAdd m) ∈ (affineProjection G).ker := by
    rw [← affineTranslationHom_range]
    exact ⟨_, rfl⟩
  have hcomm := Subgroup.commutator_mem_commutator g.property hm
  have hinf := Subgroup.commutator_le_inf I (affineProjection G).ker hcomm
  have hall : ⁅g.val, affineTranslationHom G (Multiplicative.ofAdd m)⁆ ∈
      _root_.commutator G := Subgroup.commutator_mem_commutator (by trivial) (by trivial)
  exact ⟨⟨hall, hinf.1⟩, hinf.2⟩

/-- The actual scalar image `(h-1)M` lies simultaneously in the commutator
subgroup, in `I`, and in the translation kernel. -/
theorem affineTranslation_scalar_image_le (G : ClosedSubgroup (PadicAffineGroup p))
    (I : Subgroup G) [I.Normal] (g : I) :
    (((affineTranslationKernel G).toAddSubgroup.map
      (AddMonoidHom.mulLeft ((g.val.val.right : ℤ_[p]) - 1))).addSubgroupOf
        (affineTranslationKernel G).toAddSubgroup).toSubgroup.map (affineTranslationHom G) ≤
      _root_.commutator G ⊓ I ⊓ (affineProjection G).ker := by
  rintro y ⟨x, hx, rfl⟩
  change x.toAdd.val ∈ (affineTranslationKernel G).toAddSubgroup.map
    (AddMonoidHom.mulLeft ((g.val.val.right : ℤ_[p]) - 1)) at hx
  obtain ⟨m, hm, hval⟩ := hx
  have hs := affineTranslation_scalar_mem G I g (⟨m, hm⟩ : affineTranslationKernel G)
  have he : Multiplicative.ofAdd
      (⟨((g.val.val.right : ℤ_[p]) - 1) * m,
        PadicInt.mul_mem_closedAddSubgroup (affineTranslationKernel G) _ _ hm⟩ :
          affineTranslationKernel G) = x := by
    apply Multiplicative.toAdd.injective
    apply Subtype.ext
    exact hval
  rw [← he]
  exact hs

/-- A nonidentity unit coordinate in `I` makes its intersection with the
actual translation kernel have finite index in that kernel. -/
theorem affineProjection_kernel_finiteRelIndex
    (G : ClosedSubgroup (PadicAffineGroup p)) (I : Subgroup G) [I.Normal]
    (g : I) (hg : g.val.val.right ≠ 1) : I.IsFiniteRelIndex (affineProjection G).ker := by
  let M := affineTranslationKernel G
  let a : ℤ_[p] := (g.val.val.right : ℤ_[p]) - 1
  have ha : a ≠ 0 := by
    intro ha
    apply hg
    apply Units.ext
    exact sub_eq_zero.mp ha
  let S : AddSubgroup M :=
    (M.toAddSubgroup.map (AddMonoidHom.mulLeft a)).addSubgroupOf M.toAddSubgroup
  have hfinite := PadicInt.closedAddSubgroup_map_mulLeft_finiteRelIndex M a ha
  have : S.FiniteIndex := AddSubgroup.isFiniteRelIndex_iff_finiteIndex.mp hfinite
  have : S.toSubgroup.FiniteIndex := (AddSubgroup.finiteIndex_toSubgroup_iff S).mpr inferInstance
  have hle : S.toSubgroup ≤ I.comap (affineTranslationHom G) := by
    intro x hx
    exact (affineTranslation_scalar_image_le G I g ⟨x, hx, rfl⟩).1.2
  have : (I.comap (affineTranslationHom G)).FiniteIndex := Subgroup.finiteIndex_of_le hle
  have hrel : (I.comap (affineTranslationHom G)).IsFiniteRelIndex ⊤ :=
    Subgroup.isFiniteRelIndex_top_iff.mpr inferInstance
  have hr := Subgroup.isFiniteRelIndex_comap_iff.mp hrel
  rw [Subgroup.map_top, affineTranslationHom_range] at hr
  exact hr

/-- An open projection containing a nonidentity unit makes the actual normal
subgroup have finite index, by the actual index product. -/
theorem affineProjection_finiteIndex
    (G : ClosedSubgroup (PadicAffineGroup p)) (I : Subgroup G) [I.Normal]
    (hJ : IsOpen (I.map (affineProjection G).rangeRestrict : Set (affineProjection G).range))
    (h : (affineProjection G).range)
    (hh : h ∈ I.map (affineProjection G).rangeRestrict) (hne : h.val ≠ 1) : I.FiniteIndex := by
  have : CompactSpace (affineProjection G).range :=
    Function.Surjective.compactSpace
      ((continuous_affineProjection G).subtype_mk _) (affineProjection G).rangeRestrict_surjective
  have := Subgroup.quotient_finite_of_isOpen (I.map (affineProjection G).rangeRestrict) hJ
  have : (I.map (affineProjection G).rangeRestrict).FiniteIndex :=
    Subgroup.finiteIndex_of_finite_quotient
  obtain ⟨g, hg, hproj⟩ := hh
  have hgn : (g : PadicAffineGroup p).right ≠ 1 := by
    intro heq
    apply hne
    have hp := congrArg Subtype.val hproj
    change g.val.right = h.val at hp
    exact hp.symm.trans heq
  have := affineProjection_kernel_finiteRelIndex G I ⟨g, hg⟩ hgn
  constructor
  rw [affineProjection_index]
  exact mul_ne_zero Subgroup.FiniteIndex.index_ne_zero Subgroup.relIndex_ne_zero

/-- A closed normal subgroup of an actual closed p-adic affine group is open
if its actual projection is open and contains a nonidentity unit. -/
theorem isOpen_of_affineProjection
    (G : ClosedSubgroup (PadicAffineGroup p)) (I : Subgroup G) [I.Normal]
    (hI : IsClosed (I : Set G))
    (hJ : IsOpen (I.map (affineProjection G).rangeRestrict : Set (affineProjection G).range))
    (h : (affineProjection G).range)
    (hh : h ∈ I.map (affineProjection G).rangeRestrict) (hne : h.val ≠ 1) :
    IsOpen (I : Set G) := by
  have : IsTopologicalGroup G := inferInstanceAs (IsTopologicalGroup G.toSubgroup)
  have := affineProjection_finiteIndex G I hJ h hh hne
  exact Subgroup.isOpen_of_isClosed_of_finiteIndex I hI

end

end FalseTateExtension
