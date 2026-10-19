/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import Mathlib.FieldTheory.Galois.Infinite
public import Mathlib.FieldTheory.Galois.Profinite
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import Mathlib.Topology.Algebra.ContinuousMonoidHom

/-!
# Consequences of the infinite Galois correspondence

Lemmas on intermediate fields `A ≤ B` of a Galois extension `Ω/F`, formulated through the fixing
subgroup of the inclusion `A →ₐ[F] B` inside `Gal(B/F)`:

* an element of `B` fixed by that subgroup lies in `A`;
* if that subgroup is trivial then `A = B`;
* if two such subgroups generate `Gal(C/F)` then the two fields meet in `F`;
* in a finite cyclic extension, intermediate fields of equal degree coincide.

The Krull topology: restriction of scalars `Gal(Ω/M) → Gal(Ω/F)` is continuous when `Ω/M` is
algebraic, and for `Ω/F` Galois it is a homeomorphic isomorphism onto the subgroup fixing `M`.

Upstream candidate: `Mathlib.FieldTheory.Galois.Infinite`.
-/

@[expose] public section

noncomputable section

namespace IntermediateField

variable {F Ω : Type*} [Field F] [Field Ω] [Algebra F Ω]

/-- An element of `B` fixed by the group fixing the image of `A ≤ B` lies in `A`. -/
theorem mem_of_fixed_by_inclusion {A B : IntermediateField F Ω} [IsGalois F B] (hAB : A ≤ B)
    (x : B) (hf : ∀ g ∈ (inclusion hAB).fieldRange.fixingSubgroup, g x = x) : (x : Ω) ∈ A := by
  let i := inclusion hAB
  have hm : x ∈ fixedField i.fieldRange.fixingSubgroup := by
    rw [mem_fixedField_iff]
    exact hf
  rw [InfiniteGalois.fixedField_fixingSubgroup] at hm
  obtain ⟨y, hy⟩ := hm
  have hy' : (y : Ω) = x := congrArg Subtype.val hy
  exact hy' ▸ y.property

/-- If the group fixing the image of `S ≤ T` in `Gal(T/F)` is trivial, then `T = S`. -/
theorem eq_of_inclusion_fixingSubgroup_eq_bot {S T : IntermediateField F Ω} [IsGalois F T]
    (hST : S ≤ T) (hfix : (inclusion hST).fieldRange.fixingSubgroup = ⊥) : T = S := by
  let i := inclusion hST
  have htop : i.fieldRange = ⊤ := by
    calc
      i.fieldRange = fixedField i.fieldRange.fixingSubgroup :=
        (InfiniteGalois.fixedField_fixingSubgroup i.fieldRange).symm
      _ = fixedField (⊥ : Subgroup (T ≃ₐ[F] T)) := congrArg fixedField hfix
      _ = ⊤ := fixedField_bot
  apply le_antisymm _ hST
  intro x hx
  have hx' : (⟨x, hx⟩ : T) ∈ i.fieldRange := by
    rw [htop]
    trivial
  obtain ⟨y, hy⟩ := hx'
  have hy' : (y : Ω) = x := congrArg Subtype.val hy
  exact hy' ▸ y.property

/-- If the groups fixing the images of `A, B ≤ C` generate `Gal(C/F)`, then `A ⊓ B = ⊥`. -/
theorem inf_eq_bot_of_inclusion_fixingSubgroup_sup_eq_top {A B C : IntermediateField F Ω}
    [IsGalois F C] (hAC : A ≤ C) (hBC : B ≤ C)
    (hsup : (inclusion hAC).fieldRange.fixingSubgroup ⊔
      (inclusion hBC).fieldRange.fixingSubgroup = ⊤) : A ⊓ B = ⊥ := by
  apply le_antisymm _ bot_le
  intro x hx
  let z : C := ⟨x, hAC hx.1⟩
  have hle : (inclusion hAC).fieldRange.fixingSubgroup ⊔
      (inclusion hBC).fieldRange.fixingSubgroup ≤ MulAction.stabilizer (C ≃ₐ[F] C) z := by
    apply sup_le
    · intro g hg
      change g z = z
      exact (mem_fixingSubgroup_iff _ g).mp hg z ⟨⟨x, hx.1⟩, rfl⟩
    · intro g hg
      change g z = z
      exact (mem_fixingSubgroup_iff _ g).mp hg z ⟨⟨x, hx.2⟩, rfl⟩
  have hz : z ∈ (⊥ : IntermediateField F C) := by
    apply (InfiniteGalois.mem_bot_iff_fixed z).mpr
    intro g
    exact hle (by rw [hsup]; trivial)
  obtain ⟨a, ha⟩ := mem_bot.mp hz
  exact mem_bot.mpr ⟨a, congrArg Subtype.val ha⟩

/-- In a finite Galois extension with cyclic group, intermediate fields of the same degree
coincide. -/
theorem eq_of_finrank_eq_of_isCyclic [FiniteDimensional F Ω] [IsGalois F Ω]
    [IsCyclic (Ω ≃ₐ[F] Ω)] (A B : IntermediateField F Ω)
    (h : Module.finrank F A = Module.finrank F B) : A = B := by
  have hfix : A.fixingSubgroup = B.fixingSubgroup := by
    apply IsCyclic.subgroup_eq_iff_index_eq.mpr
    simpa only [← finrank_eq_fixingSubgroup_index] using h
  calc
    A = fixedField A.fixingSubgroup := (InfiniteGalois.fixedField_fixingSubgroup A).symm
    _ = fixedField B.fixingSubgroup := congrArg fixedField hfix
    _ = B := InfiniteGalois.fixedField_fixingSubgroup B

end IntermediateField

namespace AlgEquiv

open scoped Topology
open IntermediateField

variable (F M Ω : Type*) [Field F] [Field M] [Field Ω]
  [Algebra F M] [Algebra F Ω] [Algebra M Ω] [IsScalarTower F M Ω]

/-- Restriction of scalars is continuous for the Krull topologies when `Ω/M` is algebraic. -/
theorem continuous_restrictScalarsHom [Algebra.IsAlgebraic M Ω] :
    Continuous (restrictScalarsHom F (S := M) (A := Ω)) := by
  classical
  apply continuous_of_continuousAt_one (restrictScalarsHom F (S := M) (A := Ω))
  rw [ContinuousAt, map_one]
  refine ((galGroupBasis M Ω).nhds_one_hasBasis.tendsto_iff
    (galGroupBasis F Ω).nhds_one_hasBasis).mpr ?_
  rintro _ ⟨_, ⟨E, hE : FiniteDimensional F E, rfl⟩, rfl⟩
  refine ⟨_, ⟨_, ⟨adjoin M (E : Set Ω), ?_, rfl⟩, rfl⟩, fun σ hσ x ↦ ?_⟩
  · suffices Algebra.EssFiniteType M (adjoin M (E : Set Ω)) by
      apply Algebra.finite_of_essFiniteType_of_isAlgebraic
    have hfin : Algebra.EssFiniteType F E := inferInstance
    rw [essFiniteType_iff] at hfin ⊢
    obtain ⟨s, rfl⟩ := hfin
    exact ⟨s, by rw [adjoin_adjoin_right]⟩
  · exact hσ ⟨x, subset_adjoin _ _ x.property⟩

/-- For `Ω/F` Galois, the subgroup of `Gal(Ω/F)` fixing the image of `M` is `Gal(Ω/M)`, as
topological groups. The embedding `i` is the structure map `M → Ω`. -/
def fixingSubgroupContinuousMulEquiv [IsGalois F Ω] (i : M →ₐ[F] Ω)
    (hi : ∀ x, algebraMap M Ω x = i x) : i.fieldRange.fixingSubgroup ≃ₜ* (Ω ≃ₐ[M] Ω) := by
  let R := i.fieldRange
  let e : R.fixingSubgroup ≃* (Ω ≃ₐ[M] Ω) :=
    { toFun := fun g ↦
        { g.val.toRingEquiv with
          commutes' := fun x ↦ by
            rw [hi]
            exact (IntermediateField.mem_fixingSubgroup_iff R g.val).mp g.property _ ⟨x, rfl⟩ }
      invFun := fun g ↦ ⟨g.restrictScalars F, by
        rw [IntermediateField.mem_fixingSubgroup_iff]
        rintro x ⟨y, rfl⟩
        change g (i y) = i y
        rw [← hi]
        exact g.commutes y⟩
      left_inv := fun g ↦ Subtype.ext (AlgEquiv.ext (fun _ ↦ rfl))
      right_inv := fun g ↦ AlgEquiv.ext (fun _ ↦ rfl)
      map_mul' := fun g h ↦ AlgEquiv.ext (fun _ ↦ rfl) }
  have : IsGalois M Ω := IsGalois.tower_top_of_isGalois F M Ω
  have hc : Continuous e.symm := by
    apply Continuous.subtype_mk
    exact continuous_restrictScalarsHom F M Ω
  exact { e with
    continuous_toFun := hc.continuous_symm_of_equiv_compact_to_t2
    continuous_invFun := hc }

theorem fixingSubgroupContinuousMulEquiv_apply [IsGalois F Ω] (i : M →ₐ[F] Ω)
    (hi : ∀ x, algebraMap M Ω x = i x) (g : i.fieldRange.fixingSubgroup) (x : Ω) :
    fixingSubgroupContinuousMulEquiv F M Ω i hi g x = g.val x := rfl

end AlgEquiv

end
