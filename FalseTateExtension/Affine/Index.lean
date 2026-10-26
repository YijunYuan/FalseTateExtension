/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FalseTateExtension.Affine.ClosedSubgroup
public import Mathlib.Algebra.Group.Pointwise.Set.Card
public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.Topology.Algebra.Group.Pointwise

/-!
# Uniform index bounds in closed subgroups of the `p`-adic affine group

Let `G` be a closed subgroup of `ℤ_[p] ⋊ ℤ_[p]ˣ` with unit projection `ρ : G → ℤ_[p]ˣ`,
`(a, u) ↦ u`, translation kernel `T(G) = {a | (a, 1) ∈ G}` and pure units
`P(G) = {(0, u) ∈ G}`; for a subgroup `I` of `G` write `T(I) = {a | (a, 1) ∈ I}`. If `ρ(G)` is
infinite and `T(G) ≠ 0`, there are constants `C, D > 0` such that every closed normal subgroup
`I` of `G` with `[G : P(G) I] < ∞` and `[ρ(G) : ρ(I)] < ∞` is open and satisfies

`[G : P(G) I] · [ρ(G) : ρ(I)] ≤ D · [G : I]`  and  `[G : I] ≤ C · [G : P(G) I] · [ρ(G) : ρ(I)]`.

The upper bound comes from the commutator formula `⁅(0, u), (a, 1)⁆ = ((u - 1) a, 1)`: for a pure
unit `(0, u) ∈ G` with `u ≠ 1`, `(u - 1) T(P(G) I) ⊆ T(I)`, so `[T(G) : T(I)]` is at most
`[ℤ_[p] : (u - 1) ℤ_[p]] · [G : P(G) I]`. Applied to the image of `Gal(K_FT/K)`, these bounds
compare the ramification indices of `K_FT/K` with those of `K_Kum/K` and `K_cyc/K`
(`FalseTate/StrictAPF`).

## Main results

* `affinePureUnits`: the pure units `P(G) = {(0, u) ∈ G}`.
* `affineTranslationStabilizer`, `affineTranslationStabilizer_eq_sup`: the subgroup
  `{(a, u) ∈ G | a ∈ T(G)}`, equal to `ker ρ · P(G)`.
* `exists_affinePureUnit_ne_one`: if `ρ(G)` is infinite and `T(G) ≠ 0`, `G` contains a pure
  unit `(0, u)` with `u ≠ 1`.
* `affinePureUnit_kernel_index_bound`:
  `[T(G) : T(I)] ≤ [ℤ_[p] : (u - 1) ℤ_[p]] · [G : P(G) I]` for such a `u`.
* `index_sup_le_index_sup_mul_relIndex`: `[Γ : S I] ≤ [Γ : S M] · [M : I ∩ M]` in any group.
* `affineIndex_comparison`: the two-sided comparison of `[G : I]` with
  `[G : P(G) I] · [ρ(G) : ρ(I)]`.
* `affineProjection_index_of_translationKernel_eq_bot`: if `T(G) = 0` then
  `[ρ(G) : ρ(I)] = [G : I]`.

## References

* [Tong Liu, *On lattices in semi-stable representations: a proof of a conjecture of
  Breuil*](https://doi.org/10.1112/S0010437X0700317X), §5.1.
-/

@[expose] public section

noncomputable section

namespace FalseTateExtension

variable {p : ℕ} [Fact p.Prime]

open scoped Pointwise commutatorElement

/-- The pure units `P(G) = {(0, u) ∈ G}` of a closed subgroup `G` of `ℤ_[p] ⋊ ℤ_[p]ˣ`. -/
def affinePureUnits (G : ClosedSubgroup (PadicAffineGroup p)) : Subgroup G :=
  (SemidirectProduct.inr : (ℤ_[p])ˣ →* PadicAffineGroup p).range.comap G.toSubgroup.subtype

/-- `g ∈ P(G)` if and only if the translation coordinate of `g` is `0`. -/
@[simp]
theorem mem_affinePureUnits (G : ClosedSubgroup (PadicAffineGroup p)) (g : G) :
    g ∈ affinePureUnits G ↔ g.val.left = 1 := by
  change (∃ u, SemidirectProduct.inr u = g.val) ↔ g.val.left = 1
  constructor
  · rintro ⟨u, hu⟩
    rw [← hu]
    rfl
  · intro hg
    exact ⟨g.val.right, SemidirectProduct.ext hg.symm rfl⟩

/-- `P(G)` is a closed subgroup of `G`. -/
theorem isClosed_affinePureUnits (G : ClosedSubgroup (PadicAffineGroup p)) :
    IsClosed (affinePureUnits G : Set G) := by
  have hc : Continuous (fun g : G ↦ g.val.left.toAdd) :=
    (continuous_padicAffine_left p).comp continuous_subtype_val
  convert isClosed_eq hc (continuous_const (y := (0 : ℤ_[p]))) using 1
  ext g
  change g ∈ affinePureUnits G ↔ g.val.left.toAdd = 0
  rw [mem_affinePureUnits]
  exact Multiplicative.toAdd.injective.eq_iff.symm

/-- The unit projection `(0, u) ↦ u` is injective on `P(G)`. -/
theorem affineProjection_injective_on_pureUnits
    (G : ClosedSubgroup (PadicAffineGroup p)) :
    Function.Injective ((affineProjection G).comp (affinePureUnits G).subtype) := by
  intro g h heq
  apply Subtype.ext
  apply Subtype.ext
  apply SemidirectProduct.ext
  · exact ((mem_affinePureUnits G g.val).mp g.property).trans
      ((mem_affinePureUnits G h.val).mp h.property).symm
  · exact heq

/-- Any two pure units of `G` commute. -/
theorem affinePureUnits_commute (G : ClosedSubgroup (PadicAffineGroup p))
    (g h : affinePureUnits G) : Commute (g : G) (h : G) := by
  change (g : G) * h = h * g
  apply Subtype.ext
  apply SemidirectProduct.ext
  · change (g.val.val * h.val.val).left = (h.val.val * g.val.val).left
    simp only [SemidirectProduct.mul_left,
      (mem_affinePureUnits G g.val).mp g.property,
      (mem_affinePureUnits G h.val).mp h.property, map_one, mul_one]
  · exact mul_comm _ _

/-- The subgroup `S(G) = {(a, u) ∈ G | a ∈ T(G)}` of `G`, the stabilizer of `0` for the action
of `G` on `ℤ_[p] / T(G)`; it equals `ker ρ · P(G)` (`affineTranslationStabilizer_eq_sup`). -/
def affineTranslationStabilizer (G : ClosedSubgroup (PadicAffineGroup p)) : Subgroup G where
  carrier := {g | g.val.left.toAdd ∈ affineTranslationKernel G}
  one_mem' := (affineTranslationKernel G).zero_mem
  mul_mem' {g h} hg hh := by
    change g.val.left.toAdd + (g.val.right : ℤ_[p]) * h.val.left.toAdd ∈
      affineTranslationKernel G
    exact (affineTranslationKernel G).add_mem hg
      (PadicInt.mul_mem_closedAddSubgroup (affineTranslationKernel G) _ _ hh)
  inv_mem' {g} hg := by
    change (g.val.right⁻¹ : (ℤ_[p])ˣ) * -g.val.left.toAdd ∈ affineTranslationKernel G
    exact PadicInt.mul_mem_closedAddSubgroup (affineTranslationKernel G) _ _
      ((affineTranslationKernel G).neg_mem hg)

/-- `g ∈ S(G)` if and only if the translation coordinate of `g` lies in `T(G)`. -/
@[simp]
theorem mem_affineTranslationStabilizer (G : ClosedSubgroup (PadicAffineGroup p)) (g : G) :
    g ∈ affineTranslationStabilizer G ↔ g.val.left.toAdd ∈ affineTranslationKernel G := Iff.rfl

/-- `S(G) = ker ρ ⊔ P(G)`, where `ρ` is the unit projection of `G`. -/
theorem affineTranslationStabilizer_eq_sup (G : ClosedSubgroup (PadicAffineGroup p)) :
    affineTranslationStabilizer G = (affineProjection G).ker ⊔ affinePureUnits G := by
  apply le_antisymm
  · intro g hg
    have ht : (SemidirectProduct.inl g.val.left : PadicAffineGroup p) ∈ G := hg
    let t : G := ⟨SemidirectProduct.inl g.val.left, ht⟩
    have htk : t ∈ (affineProjection G).ker := rfl
    have hs : t⁻¹ * g ∈ affinePureUnits G := by
      rw [mem_affinePureUnits]
      change ((SemidirectProduct.inl g.val.left : PadicAffineGroup p)⁻¹ * g.val).left = 1
      simp
    have heq : t * (t⁻¹ * g) = g := by simp
    rw [← heq]
    exact Subgroup.mul_mem_sup htk hs
  · apply sup_le
    · intro g hg
      have hr : g.val.right = 1 := hg
      change (SemidirectProduct.inl g.val.left : PadicAffineGroup p) ∈ G
      have heq : (SemidirectProduct.inl g.val.left : PadicAffineGroup p) = g.val :=
        SemidirectProduct.ext rfl hr.symm
      rw [heq]
      exact g.property
    · intro g hg
      change g.val.left.toAdd ∈ affineTranslationKernel G
      rw [(mem_affinePureUnits G g).mp hg]
      exact (affineTranslationKernel G).zero_mem

/-- `g⁻¹ h ∈ S(G)` if and only if the translation coordinates of `g` and `h` are congruent
modulo `T(G)`. -/
theorem affineTranslationStabilizer_inv_mul_mem_iff
    (G : ClosedSubgroup (PadicAffineGroup p)) (g h : G) :
    g⁻¹ * h ∈ affineTranslationStabilizer G ↔
      h.val.left.toAdd - g.val.left.toAdd ∈ affineTranslationKernel G := by
  have hunit : (g.val.right : ℤ_[p]) * (g.val.right⁻¹ : (ℤ_[p])ˣ) = 1 := by
    exact congrArg (fun u : (ℤ_[p])ˣ ↦ (u : ℤ_[p])) (mul_inv_cancel g.val.right)
  have hcoord : (g⁻¹ * h).val.left.toAdd =
      (g.val.right⁻¹ : (ℤ_[p])ˣ) * (h.val.left.toAdd - g.val.left.toAdd) := by
    change (g.val.right⁻¹ : (ℤ_[p])ˣ) * -g.val.left.toAdd +
      (g.val.right⁻¹ : (ℤ_[p])ˣ) * h.val.left.toAdd = _
    ring
  rw [mem_affineTranslationStabilizer, hcoord]
  constructor
  · intro hm
    have h := PadicInt.mul_mem_closedAddSubgroup (affineTranslationKernel G)
      (g.val.right : ℤ_[p]) _ hm
    simpa only [← mul_assoc, hunit, one_mul] using h
  · exact PadicInt.mul_mem_closedAddSubgroup (affineTranslationKernel G) _ _

/-- The translation coordinate induces an injection `G / S(G) ↪ ℤ_[p] / T(G)`. -/
def affineZeroStabilizerQuotientEmbedding (G : ClosedSubgroup (PadicAffineGroup p)) :
    (G ⧸ affineTranslationStabilizer G) ↪
      (ℤ_[p] ⧸ (affineTranslationKernel G).toAddSubgroup) where
  toFun := Quotient.map' (fun g : G ↦ g.val.left.toAdd) (by
    intro g h hrel
    rw [QuotientGroup.leftRel_apply] at hrel
    rw [QuotientAddGroup.leftRel_apply]
    change -g.val.left.toAdd + h.val.left.toAdd ∈ affineTranslationKernel G
    simpa only [sub_eq_add_neg, add_comm] using
      (affineTranslationStabilizer_inv_mul_mem_iff G g h).mp hrel)
  inj' := by
    intro x y
    refine Quotient.inductionOn₂ x y ?_
    intro g h heq
    apply @Quotient.sound G (QuotientGroup.leftRel (affineTranslationStabilizer G)) g h
    change (QuotientGroup.leftRel (affineTranslationStabilizer G)) g h
    rw [QuotientGroup.leftRel_apply]
    apply (affineTranslationStabilizer_inv_mul_mem_iff G g h).mpr
    have hrel : (QuotientAddGroup.leftRel (affineTranslationKernel G).toAddSubgroup)
        g.val.left.toAdd h.val.left.toAdd := Quotient.exact heq
    rw [QuotientAddGroup.leftRel_apply] at hrel
    change -g.val.left.toAdd + h.val.left.toAdd ∈ affineTranslationKernel G at hrel
    simpa only [sub_eq_add_neg, add_comm] using hrel

/-- If `T(G) ≠ 0`, then `S(G)` has finite index in `G`. -/
theorem affineTranslationStabilizer_finiteIndex (G : ClosedSubgroup (PadicAffineGroup p))
    (hM : (affineTranslationKernel G).toAddSubgroup ≠ ⊥) :
    (affineTranslationStabilizer G).FiniteIndex := by
  have hopen := PadicInt.isOpen_closedAddSubgroup_map_mulLeft
    (affineTranslationKernel G) hM 1 one_ne_zero
  have heq : (affineTranslationKernel G).toAddSubgroup.map
      (AddMonoidHom.mulLeft (1 : ℤ_[p])) = (affineTranslationKernel G).toAddSubgroup := by
    ext x
    simp
  rw [heq] at hopen
  have := AddSubgroup.quotient_finite_of_isOpen (affineTranslationKernel G).toAddSubgroup hopen
  have : Finite (G ⧸ affineTranslationStabilizer G) :=
    Finite.of_injective (affineZeroStabilizerQuotientEmbedding G)
      (affineZeroStabilizerQuotientEmbedding G).injective
  exact Subgroup.finiteIndex_of_finite_quotient

/-- `[ρ(G) : ρ(P(G))] = [G : S(G)]`. -/
theorem affinePureUnits_image_index (G : ClosedSubgroup (PadicAffineGroup p)) :
    ((affinePureUnits G).map (affineProjection G).rangeRestrict).index =
      (affineTranslationStabilizer G).index := by
  let ρ := (affineProjection G).rangeRestrict
  have hr : ρ.range = ⊤ :=
    ρ.range_eq_top_of_surjective (affineProjection G).rangeRestrict_surjective
  have h := (affinePureUnits G).index_map ρ
  rw [hr, Subgroup.index_top, mul_one, MonoidHom.ker_rangeRestrict,
    sup_comm, ← affineTranslationStabilizer_eq_sup] at h
  exact h

/-- If `T(G) ≠ 0`, then `ρ(P(G))` has finite index in `ρ(G)`. -/
theorem affinePureUnits_image_finiteIndex (G : ClosedSubgroup (PadicAffineGroup p))
    (hM : (affineTranslationKernel G).toAddSubgroup ≠ ⊥) :
    ((affinePureUnits G).map (affineProjection G).rangeRestrict).FiniteIndex := by
  have := affineTranslationStabilizer_finiteIndex G hM
  constructor
  rw [affinePureUnits_image_index]
  exact Subgroup.FiniteIndex.index_ne_zero

/-- If `ρ(G)` is infinite and `T(G) ≠ 0`, then `G` contains a pure unit `(0, u)` with
`u ≠ 1`. -/
theorem exists_affinePureUnit_ne_one (G : ClosedSubgroup (PadicAffineGroup p))
    [Infinite (affineProjection G).range]
    (hM : (affineTranslationKernel G).toAddSubgroup ≠ ⊥) :
    ∃ g : affinePureUnits G, g.val.val.right ≠ 1 := by
  have := affinePureUnits_image_finiteIndex G hM
  by_contra! hall
  have himage : (affinePureUnits G).map (affineProjection G).rangeRestrict = ⊥ := by
    apply le_antisymm _ bot_le
    rintro u ⟨g, hg, rfl⟩
    change (affineProjection G).rangeRestrict g = 1
    apply Subtype.ext
    exact hall ⟨g, hg⟩
  have hne := Subgroup.FiniteIndex.index_ne_zero
    (H := (affinePureUnits G).map (affineProjection G).rangeRestrict)
  rw [himage, Subgroup.index_bot, Nat.card_eq_zero_of_infinite] at hne
  exact hne rfl

/-- The translations `T(P) = {a ∈ ℤ_[p] | (a, 1) ∈ P}` of a closed subgroup `P` of `G`, a
closed additive subgroup of `ℤ_[p]`. -/
def affineTranslationIntersection (G : ClosedSubgroup (PadicAffineGroup p))
    (P : Subgroup G) (hP : IsClosed (P : Set G)) : ClosedAddSubgroup (ℤ_[p]) where
  toAddSubgroup := Subgroup.toAddSubgroup'
    ((P.map G.toSubgroup.subtype).comap SemidirectProduct.inl)
  isClosed' := by
    have hc : IsClosed (P.map G.toSubgroup.subtype : Set (PadicAffineGroup p)) :=
      (hP.isCompact.image continuous_subtype_val).isClosed
    change IsClosed ((fun x : ℤ_[p] ↦
      (SemidirectProduct.inl (Multiplicative.ofAdd x) : PadicAffineGroup p)) ⁻¹'
        (P.map G.toSubgroup.subtype : Set (PadicAffineGroup p)))
    apply hc.preimage
    exact AffineGroup.continuous_inl _

/-- `T(P)` is the image in `ℤ_[p]` of the subgroup `{a ∈ T(G) | (a, 1) ∈ P}` of `T(G)`. -/
theorem affineTranslationIntersection_toAddSubgroup
    (G : ClosedSubgroup (PadicAffineGroup p)) (P : Subgroup G) (hP : IsClosed (P : Set G)) :
    (affineTranslationIntersection G P hP).toAddSubgroup =
      (Subgroup.toAddSubgroup' (P.comap (affineTranslationHom G))).map
        (affineTranslationKernel G).toAddSubgroup.subtype := by
  ext x
  constructor
  · rintro ⟨g, hg, hgval⟩
    change g.val = (SemidirectProduct.inl (Multiplicative.ofAdd x) : PadicAffineGroup p) at hgval
    have hm : x ∈ affineTranslationKernel G := by
      change (SemidirectProduct.inl (Multiplicative.ofAdd x) : PadicAffineGroup p) ∈ G
      rw [← hgval]
      exact g.property
    refine ⟨⟨x, hm⟩, ?_, rfl⟩
    change affineTranslationHom G (Multiplicative.ofAdd ⟨x, hm⟩) ∈ P
    have ht : affineTranslationHom G (Multiplicative.ofAdd ⟨x, hm⟩) = g :=
      Subtype.ext hgval.symm
    rw [ht]
    exact hg
  · rintro ⟨m, hm, hmx⟩
    change m.val = x at hmx
    refine ⟨affineTranslationHom G (Multiplicative.ofAdd m), hm, ?_⟩
    change (SemidirectProduct.inl (Multiplicative.ofAdd m.val) : PadicAffineGroup p) =
      SemidirectProduct.inl (Multiplicative.ofAdd x)
    rw [hmx]

/-- The relative index of `T(P)` in `T(Q)` equals that of `{a ∈ T(G) | (a, 1) ∈ P}` in
`{a ∈ T(G) | (a, 1) ∈ Q}`. -/
theorem affineTranslationIntersection_relIndex
    (G : ClosedSubgroup (PadicAffineGroup p)) (P Q : Subgroup G)
    (hP : IsClosed (P : Set G)) (hQ : IsClosed (Q : Set G)) :
    (affineTranslationIntersection G P hP).toAddSubgroup.relIndex
        (affineTranslationIntersection G Q hQ).toAddSubgroup =
      (P.comap (affineTranslationHom G)).relIndex (Q.comap (affineTranslationHom G)) := by
  rw [affineTranslationIntersection_toAddSubgroup,
    affineTranslationIntersection_toAddSubgroup,
    AddSubgroup.relIndex_map_map_of_injective _ _ Subtype.val_injective]
  rfl

/-- For a closed normal subgroup `I` of `G`, the subgroup `P(G) I` is closed. -/
theorem isClosed_affinePureUnits_sup (G : ClosedSubgroup (PadicAffineGroup p))
    (I : Subgroup G) [I.Normal] (hI : IsClosed (I : Set G)) :
    IsClosed ((affinePureUnits G ⊔ I : Subgroup G) : Set G) := by
  have : IsTopologicalGroup G := inferInstanceAs (IsTopologicalGroup G.toSubgroup)
  have heq : ((affinePureUnits G ⊔ I : Subgroup G) : Set G) =
      (affinePureUnits G : Set G) * (I : Set G) := by
    ext g
    simpa only [Set.mem_mul, SetLike.mem_coe] using
      (Subgroup.mem_sup_of_normal_right (s := affinePureUnits G) (t := I) (x := g))
  rw [heq]
  exact hI.mul_left_of_isCompact (isClosed_affinePureUnits G).isCompact

/-- For a pure unit `s₀` of `G`, a normal subgroup `I` and `g ∈ P(G) I`, `⁅s₀, g⁆ ∈ I`. -/
theorem affinePureUnit_commutator_mem (G : ClosedSubgroup (PadicAffineGroup p))
    (I : Subgroup G) [I.Normal] (s₀ : affinePureUnits G) (g : G)
    (hg : g ∈ affinePureUnits G ⊔ I) : ⁅(s₀ : G), g⁆ ∈ I := by
  obtain ⟨s, hs, i, hi, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hg
  let q : G →* G ⧸ I := QuotientGroup.mk' I
  have hiq : q i = 1 := by
    change i ∈ q.ker
    simpa only [q, QuotientGroup.ker_mk'] using hi
  have hcomm : Commute (q s₀.val) (q s) :=
    (affinePureUnits_commute G s₀ ⟨s, hs⟩).map q
  rw [← QuotientGroup.ker_mk' I]
  change q ⁅s₀.val, s * i⁆ = 1
  rw [map_commutatorElement, map_mul, hiq, mul_one, commutatorElement_def, hcomm.eq]
  simp only [mul_assoc, mul_inv_cancel, one_mul]

/-- If `P ≤ Q` then `T(P) ≤ T(Q)`. -/
theorem affineTranslationIntersection_mono
    (G : ClosedSubgroup (PadicAffineGroup p)) (P Q : Subgroup G)
    (hP : IsClosed (P : Set G)) (hQ : IsClosed (Q : Set G)) (hPQ : P ≤ Q) :
    (affineTranslationIntersection G P hP).toAddSubgroup ≤
      (affineTranslationIntersection G Q hQ).toAddSubgroup := by
  rintro x ⟨g, hg, hgval⟩
  exact ⟨g, hPQ hg, hgval⟩

/-- For a pure unit `(0, u) ∈ G` and a closed normal subgroup `I` of `G`,
`(u - 1) · T(P(G) I) ⊆ T(I)`. -/
theorem affinePureUnit_scalar_image_le (G : ClosedSubgroup (PadicAffineGroup p))
    (I : Subgroup G) [I.Normal] (hI : IsClosed (I : Set G)) (s₀ : affinePureUnits G) :
    ((affineTranslationIntersection G (affinePureUnits G ⊔ I)
      (isClosed_affinePureUnits_sup G I hI)).toAddSubgroup.map
        (AddMonoidHom.mulLeft ((s₀.val.val.right : ℤ_[p]) - 1))) ≤
      (affineTranslationIntersection G I hI).toAddSubgroup := by
  rintro y ⟨x, hx, rfl⟩
  obtain ⟨g, hg, hgval⟩ := hx
  change g.val = (SemidirectProduct.inl (Multiplicative.ofAdd x) : PadicAffineGroup p) at hgval
  refine ⟨⁅s₀.val, g⁆, affinePureUnit_commutator_mem G I s₀ g hg, ?_⟩
  change G.toSubgroup.subtype ⁅s₀.val, g⁆ = _
  rw [map_commutatorElement]
  change ⁅s₀.val.val, g.val⁆ = SemidirectProduct.inl
    (Multiplicative.ofAdd (((s₀.val.val.right : ℤ_[p]) - 1) * x))
  rw [hgval]
  exact padicAffine_commutator_inl s₀.val.val x

/-- For a pure unit `(0, u) ∈ G` with `u ≠ 1` and a closed normal subgroup `I` of `G`,
`0 < [T(P(G) I) : T(I)] ≤ [ℤ_[p] : (u - 1) ℤ_[p]]`. -/
theorem affinePureUnit_intersection_relIndex_bound
    (G : ClosedSubgroup (PadicAffineGroup p)) (I : Subgroup G) [I.Normal]
    (hI : IsClosed (I : Set G)) (s₀ : affinePureUnits G) (hs₀ : s₀.val.val.right ≠ 1) :
    0 < (I.comap (affineTranslationHom G)).relIndex
        ((affinePureUnits G ⊔ I).comap (affineTranslationHom G)) ∧
      (I.comap (affineTranslationHom G)).relIndex
        ((affinePureUnits G ⊔ I).comap (affineTranslationHom G)) ≤
          (AddMonoidHom.mulLeft ((s₀.val.val.right : ℤ_[p]) - 1)).range.index := by
  let T := affineTranslationIntersection G (affinePureUnits G ⊔ I)
    (isClosed_affinePureUnits_sup G I hI)
  let Mᵢ := affineTranslationIntersection G I hI
  let a : ℤ_[p] := (s₀.val.val.right : ℤ_[p]) - 1
  let J := T.toAddSubgroup.map (AddMonoidHom.mulLeft a)
  have ha : a ≠ 0 := by
    intro ha
    apply hs₀
    apply Units.ext
    exact sub_eq_zero.mp ha
  have hJM : J ≤ Mᵢ.toAddSubgroup := affinePureUnit_scalar_image_le G I hI s₀
  have hMT : Mᵢ.toAddSubgroup ≤ T.toAddSubgroup :=
    affineTranslationIntersection_mono G I _ hI _ le_sup_right
  have hfinite : J.IsFiniteRelIndex T.toAddSubgroup :=
    PadicInt.closedAddSubgroup_map_mulLeft_finiteRelIndex T a ha
  have hpos : 0 < J.relIndex T.toAddSubgroup := Nat.pos_of_ne_zero AddSubgroup.relIndex_ne_zero
  have hmul := AddSubgroup.relIndex_mul_relIndex J Mᵢ.toAddSubgroup T.toAddSubgroup hJM hMT
  have hindexpos : 0 < Mᵢ.toAddSubgroup.relIndex T.toAddSubgroup := by
    by_contra hzero
    have hz : Mᵢ.toAddSubgroup.relIndex T.toAddSubgroup = 0 := by omega
    rw [hz, mul_zero] at hmul
    exact hpos.ne' hmul.symm
  have hle : Mᵢ.toAddSubgroup.relIndex T.toAddSubgroup ≤ J.relIndex T.toAddSubgroup :=
    Nat.le_of_dvd hpos ⟨J.relIndex Mᵢ.toAddSubgroup, by nlinarith [hmul]⟩
  have hbound := hle.trans (PadicInt.closedAddSubgroup_map_mulLeft_relIndex_le T a ha)
  have heq := affineTranslationIntersection_relIndex G I (affinePureUnits G ⊔ I) hI
    (isClosed_affinePureUnits_sup G I hI)
  change Mᵢ.toAddSubgroup.relIndex T.toAddSubgroup = _ at heq
  rw [heq] at hindexpos hbound
  exact ⟨hindexpos, hbound⟩

/-- For a pure unit `(0, u) ∈ G` with `u ≠ 1` and a closed normal subgroup `I` of `G` with
`[G : P(G) I] < ∞`, `0 < [T(G) : T(I)] ≤ [ℤ_[p] : (u - 1) ℤ_[p]] · [G : P(G) I]`. -/
theorem affinePureUnit_kernel_index_bound
    (G : ClosedSubgroup (PadicAffineGroup p)) (I : Subgroup G) [I.Normal]
    (hI : IsClosed (I : Set G)) (s₀ : affinePureUnits G) (hs₀ : s₀.val.val.right ≠ 1)
    [(affinePureUnits G ⊔ I).FiniteIndex] :
    0 < (I.comap (affineTranslationHom G)).index ∧
      (I.comap (affineTranslationHom G)).index ≤
        (AddMonoidHom.mulLeft ((s₀.val.val.right : ℤ_[p]) - 1)).range.index *
          (affinePureUnits G ⊔ I).index := by
  let P := I.comap (affineTranslationHom G)
  let Q := (affinePureUnits G ⊔ I).comap (affineTranslationHom G)
  have hPQ : P ≤ Q := Subgroup.comap_mono le_sup_right
  have hbound := affinePureUnit_intersection_relIndex_bound G I hI s₀ hs₀
  have hmul := Subgroup.relIndex_mul_index hPQ
  have hQ : Q.FiniteIndex := inferInstance
  have hQpos : 0 < Q.index := Nat.pos_of_ne_zero Subgroup.FiniteIndex.index_ne_zero
  have hQle : Q.index ≤ (affinePureUnits G ⊔ I).index := by
    rw [Subgroup.index_comap]
    simpa only [Subgroup.relIndex_top_right] using
      (Subgroup.relIndex_le_of_le_right (H := affinePureUnits G ⊔ I)
      (K := (affineTranslationHom G).range) (L := ⊤) le_top
      (by simpa only [Subgroup.relIndex_top_right] using
        (Subgroup.FiniteIndex.index_ne_zero (H := affinePureUnits G ⊔ I))))
  constructor
  · change 0 < P.index
    rw [← hmul]
    exact Nat.mul_pos hbound.1 hQpos
  · change P.index ≤ _
    rw [← hmul]
    exact Nat.mul_le_mul hbound.2 hQle

/-- If `ρ(G)` is infinite and `T(G) ≠ 0`, every closed normal subgroup `I` of `G` with
`[G : P(G) I] < ∞` and `[ρ(G) : ρ(I)] < ∞` has finite index in `G`. -/
theorem affineIndex_finiteIndex_of_projectionIndices
    (G : ClosedSubgroup (PadicAffineGroup p)) [Infinite (affineProjection G).range]
    (hM : (affineTranslationKernel G).toAddSubgroup ≠ ⊥)
    (I : Subgroup G) [I.Normal] (hI : IsClosed (I : Set G))
    [(affinePureUnits G ⊔ I).FiniteIndex]
    [(I.map (affineProjection G).rangeRestrict).FiniteIndex] : I.FiniteIndex := by
  obtain ⟨s₀, hs₀⟩ := exists_affinePureUnit_ne_one G hM
  have hbound := affinePureUnit_kernel_index_bound G I hI s₀ hs₀
  constructor
  rw [affineTranslation_index_product]
  exact mul_ne_zero Subgroup.FiniteIndex.index_ne_zero hbound.1.ne'

/-- In a group `Γ`, for subgroups `S`, `M`, `I` with `M` and `I` normal, `[Γ : I] < ∞` and
`[Γ : S M] < ∞`: `[Γ : S I] ≤ [Γ : S M] · [M : I ∩ M]`. -/
theorem index_sup_le_index_sup_mul_relIndex
    {Γ : Type*} [Group Γ] (S M I : Subgroup Γ) [M.Normal] [I.Normal]
    [I.FiniteIndex] [(S ⊔ M).FiniteIndex] :
    (S ⊔ I).index ≤ (S ⊔ M).index * I.relIndex M := by
  let q : Γ →* Γ ⧸ I := QuotientGroup.mk' I
  have hq : Function.Surjective q := QuotientGroup.mk'_surjective I
  have hr : q.range = ⊤ := q.range_eq_top_of_surjective hq
  let V := S.map q
  let N := M.map q
  let W := V ⊔ N
  have : N.Normal := Subgroup.Normal.map (inferInstance : M.Normal) q hq
  have hV : V.index = (S ⊔ I).index := by
    have h := S.index_map q
    simpa only [hr, Subgroup.index_top, mul_one, q, QuotientGroup.ker_mk'] using h
  have hW : W.index ≤ (S ⊔ M).index := by
    have hmap : (S ⊔ M).map q = W := Subgroup.map_sup S M q
    rw [← hmap]
    exact Nat.le_of_dvd (Nat.pos_of_ne_zero Subgroup.FiniteIndex.index_ne_zero)
      ((S ⊔ M).index_map_dvd hq)
  have hN : Nat.card N = I.relIndex M := by
    have hker : (q.comp M.subtype).ker = I.comap M.subtype := by
      change q.ker.comap M.subtype = I.comap M.subtype
      rw [show q.ker = I from QuotientGroup.ker_mk' I]
    have h := Subgroup.index_ker (q.comp M.subtype)
    rw [hker] at h
    simpa only [MonoidHom.range_comp, M.range_subtype,
      Subgroup.relIndex, Subgroup.subgroupOf] using h.symm
  have hprod : Nat.card W ≤ Nat.card V * Nat.card N := by
    have h := Set.natCard_mul_le (s := (V : Set (Γ ⧸ I))) (t := (N : Set (Γ ⧸ I)))
    rw [← Subgroup.mul_normal V N] at h
    exact h
  have hQ : Nat.card (Γ ⧸ I) ≤ (S ⊔ M).index * I.relIndex M * Nat.card V := by
    calc
      _ = W.index * Nat.card W := by rw [mul_comm, W.card_mul_index]
      _ ≤ (S ⊔ M).index * (Nat.card V * Nat.card N) := Nat.mul_le_mul hW hprod
      _ = _ := by rw [hN]; ring
  have hQ' : Nat.card (Γ ⧸ I) = (S ⊔ I).index * Nat.card V := by
    rw [← hV, mul_comm, V.card_mul_index]
  rw [hQ'] at hQ
  by_contra hnot
  have hlt : (S ⊔ M).index * I.relIndex M < (S ⊔ I).index := Nat.lt_of_not_ge hnot
  exact (not_lt_of_ge hQ) (mul_lt_mul_of_pos_right hlt (show 0 < Nat.card V from Nat.card_pos))

/-- If `ρ(G)` is infinite and `T(G) ≠ 0`, there are `C, D > 0` such that every closed normal
subgroup `I` of `G` with `[G : P(G) I] < ∞` and `[ρ(G) : ρ(I)] < ∞` is open of finite index and
satisfies `[G : P(G) I] · [ρ(G) : ρ(I)] ≤ D · [G : I]` and
`[G : I] ≤ C · [G : P(G) I] · [ρ(G) : ρ(I)]`. -/
theorem affineIndex_comparison
    (G : ClosedSubgroup (PadicAffineGroup p)) [Infinite (affineProjection G).range]
    (hM : (affineTranslationKernel G).toAddSubgroup ≠ ⊥) :
    ∃ C D : ℕ, 0 < C ∧ 0 < D ∧ ∀ (I : Subgroup G) [I.Normal],
      IsClosed (I : Set G) → (affinePureUnits G ⊔ I).FiniteIndex →
      (I.map (affineProjection G).rangeRestrict).FiniteIndex →
      I.FiniteIndex ∧ IsOpen (I : Set G) ∧
        (affinePureUnits G ⊔ I).index * (I.map (affineProjection G).rangeRestrict).index ≤
          D * I.index ∧
        I.index ≤ C * (affinePureUnits G ⊔ I).index *
          (I.map (affineProjection G).rangeRestrict).index := by
  obtain ⟨s₀, hs₀⟩ := exists_affinePureUnit_ne_one G hM
  let a : ℤ_[p] := (s₀.val.val.right : ℤ_[p]) - 1
  have ha : a ≠ 0 := by
    intro ha
    apply hs₀
    apply Units.ext
    exact sub_eq_zero.mp ha
  let C := (AddMonoidHom.mulLeft a).range.index
  let D := (affineTranslationStabilizer G).index
  have hDfinite := affineTranslationStabilizer_finiteIndex G hM
  have hD : 0 < D := Nat.pos_of_ne_zero Subgroup.FiniteIndex.index_ne_zero
  refine ⟨C, D, PadicInt.mulLeft_range_index_pos a ha, hD, ?_⟩
  intro I hIn hI hA hB
  have := hA
  have := hB
  have hIfinite := affineIndex_finiteIndex_of_projectionIndices G hM I hI
  have hKfinite : (affinePureUnits G ⊔ (affineProjection G).ker).FiniteIndex := by
    rw [sup_comm, ← affineTranslationStabilizer_eq_sup]
    exact hDfinite
  have hlower := index_sup_le_index_sup_mul_relIndex
    (affinePureUnits G) (affineProjection G).ker I
  rw [sup_comm (affinePureUnits G) (affineProjection G).ker,
    ← affineTranslationStabilizer_eq_sup, affineTranslation_index] at hlower
  have hupper := (affinePureUnit_kernel_index_bound G I hI s₀ hs₀).2
  have : IsTopologicalGroup G := inferInstanceAs (IsTopologicalGroup G.toSubgroup)
  refine ⟨hIfinite, Subgroup.isOpen_of_isClosed_of_finiteIndex I hI, ?_, ?_⟩
  · calc
      _ ≤ (D * (I.comap (affineTranslationHom G)).index) *
          (I.map (affineProjection G).rangeRestrict).index := Nat.mul_le_mul_right _ hlower
      _ = _ := by rw [affineTranslation_index_product]; ring
  · calc
      I.index = (I.map (affineProjection G).rangeRestrict).index *
          (I.comap (affineTranslationHom G)).index := affineTranslation_index_product G I
      _ ≤ (I.map (affineProjection G).rangeRestrict).index *
          (C * (affinePureUnits G ⊔ I).index) := Nat.mul_le_mul_left _ hupper
      _ = _ := by ring

/-- If `T(G) = 0`, the unit projection of `G` has trivial kernel. -/
theorem affineProjection_ker_eq_bot_of_translationKernel_eq_bot
    (G : ClosedSubgroup (PadicAffineGroup p))
    (hM : (affineTranslationKernel G).toAddSubgroup = ⊥) :
    (affineProjection G).ker = ⊥ := by
  apply bot_unique
  intro g hg
  have hr : g.val.right = 1 := hg
  have hm : g.val.left.toAdd ∈ affineTranslationKernel G := by
    apply (mem_affineTranslationStabilizer G g).mp
    rw [affineTranslationStabilizer_eq_sup]
    exact (show (affineProjection G).ker ≤ (affineProjection G).ker ⊔ affinePureUnits G from
      le_sup_left) hg
  have hz : g.val.left.toAdd = 0 := by
    change g.val.left.toAdd ∈ (affineTranslationKernel G).toAddSubgroup at hm
    simpa only [hM, AddSubgroup.mem_bot] using hm
  change g = 1
  apply Subtype.ext
  exact SemidirectProduct.ext (Multiplicative.toAdd.injective hz) hr

/-- If `T(G) = 0`, the unit projection of `G` is injective. -/
theorem affineProjection_injective_of_translationKernel_eq_bot
    (G : ClosedSubgroup (PadicAffineGroup p))
    (hM : (affineTranslationKernel G).toAddSubgroup = ⊥) :
    Function.Injective (affineProjection G) := by
  intro g h heq
  have hker : g⁻¹ * h ∈ (affineProjection G).ker := by
    change affineProjection G (g⁻¹ * h) = 1
    rw [map_mul, map_inv, heq, inv_mul_cancel]
  rw [affineProjection_ker_eq_bot_of_translationKernel_eq_bot G hM] at hker
  exact inv_mul_eq_one.mp hker

/-- If `T(G) = 0`, then `[ρ(G) : ρ(I)] = [G : I]` for every subgroup `I` of `G`. -/
theorem affineProjection_index_of_translationKernel_eq_bot
    (G : ClosedSubgroup (PadicAffineGroup p))
    (hM : (affineTranslationKernel G).toAddSubgroup = ⊥) (I : Subgroup G) :
    (I.map (affineProjection G).rangeRestrict).index = I.index := by
  let ρ := (affineProjection G).rangeRestrict
  have hr : ρ.range = ⊤ :=
    ρ.range_eq_top_of_surjective (affineProjection G).rangeRestrict_surjective
  have h := I.index_map ρ
  rw [hr, Subgroup.index_top, mul_one, MonoidHom.ker_rangeRestrict,
    affineProjection_ker_eq_bot_of_translationKernel_eq_bot G hM, sup_bot_eq] at h
  exact h

end FalseTateExtension
