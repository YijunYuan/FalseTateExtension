/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import Mathlib.GroupTheory.Index
public import Mathlib.NumberTheory.Padics.ProperSpace
public import Mathlib.Topology.Algebra.Group.ClosedSubgroup
public import Mathlib.Topology.Algebra.Ring.Compact

/-!
# Closed additive subgroups of the `p`-adic integers

A closed additive subgroup of `ℤ_[p]` is stable under multiplication by `ℤ_[p]` (density of `ℕ`),
hence is the additive group of an ideal: it is zero or a power of the maximal ideal. For a nonzero
scalar `a`, the image `a • M` of a closed subgroup `M` has finite relative index in `M`.

Upstream candidate: `Mathlib.NumberTheory.Padics.PadicIntegers`.

## Main results

* `PadicInt.closedAddSubgroupIdeal`: the ideal with the same carrier as a closed subgroup.
* `PadicInt.closedAddSubgroup_eq_bot_or_span_pow`: a closed subgroup is `⊥` or `(p ^ s)`.
* `PadicInt.closedAddSubgroup_map_mulLeft_finiteRelIndex`: `a • M` has finite index in `M`.
-/

@[expose] public section

namespace PadicInt

noncomputable section

variable {p : ℕ} [Fact p.Prime]

/-- Closed additive subgroups of `ℤ_[p]` are stable under every `p`-adic scalar. -/
theorem mul_mem_closedAddSubgroup (M : ClosedAddSubgroup (ℤ_[p]))
    (a x : ℤ_[p]) (hx : x ∈ M) : a * x ∈ M := by
  apply (denseRange_natCast (p := p)).induction_on (p := fun b ↦ b * x ∈ M) a
  · exact M.isClosed'.preimage (continuous_id.mul continuous_const)
  · intro n
    change (n : ℤ_[p]) * x ∈ M.toAddSubgroup
    simpa only [nsmul_eq_mul] using M.toAddSubgroup.nsmul_mem hx n

/-- The ideal of `ℤ_[p]` with the same carrier as a closed additive subgroup. -/
def closedAddSubgroupIdeal (M : ClosedAddSubgroup (ℤ_[p])) : Ideal (ℤ_[p]) where
  carrier := M
  zero_mem' := M.zero_mem
  add_mem' := M.add_mem
  smul_mem' a x hx := mul_mem_closedAddSubgroup M a x hx

/-- The ideal associated to a closed additive subgroup has the same elements. -/
@[simp]
theorem mem_closedAddSubgroupIdeal (M : ClosedAddSubgroup (ℤ_[p])) (x : ℤ_[p]) :
    x ∈ closedAddSubgroupIdeal M ↔ x ∈ M := Iff.rfl

/-- The additive subgroup of the associated ideal is the original closed subgroup. -/
theorem closedAddSubgroupIdeal_toAddSubgroup (M : ClosedAddSubgroup (ℤ_[p])) :
    (closedAddSubgroupIdeal M).toAddSubgroup = M.toAddSubgroup := rfl

/-- A closed additive subgroup of `ℤ_[p]` is zero or the additive group of `(p ^ s)`. -/
theorem closedAddSubgroup_eq_bot_or_span_pow (M : ClosedAddSubgroup (ℤ_[p])) :
    M.toAddSubgroup = ⊥ ∨ ∃ s : ℕ,
      M.toAddSubgroup = (Ideal.span {(p : ℤ_[p]) ^ s}).toAddSubgroup := by
  by_cases hM : closedAddSubgroupIdeal M = ⊥
  · exact Or.inl (congrArg (fun I : Ideal (ℤ_[p]) ↦ I.toAddSubgroup) hM)
  · obtain ⟨s, hs⟩ := ideal_eq_span_pow_p hM
    exact Or.inr ⟨s, congrArg (fun I : Ideal (ℤ_[p]) ↦ I.toAddSubgroup) hs⟩

/-- Multiplication by a `p`-adic integer maps a closed additive subgroup into itself. -/
theorem closedAddSubgroup_map_mulLeft_le (M : ClosedAddSubgroup (ℤ_[p])) (a : ℤ_[p]) :
    M.toAddSubgroup.map (AddMonoidHom.mulLeft a) ≤ M.toAddSubgroup := by
  rintro y ⟨x, hx, rfl⟩
  exact mul_mem_closedAddSubgroup M a x hx

/-- Multiplication by a scalar commutes with passing from the associated ideal to its
additive subgroup. -/
theorem closedAddSubgroupIdeal_map_mulLeft_toAddSubgroup
    (M : ClosedAddSubgroup (ℤ_[p])) (a : ℤ_[p]) :
    (Submodule.map (LinearMap.mulLeft (ℤ_[p]) a) (closedAddSubgroupIdeal M)).toAddSubgroup =
      M.toAddSubgroup.map (AddMonoidHom.mulLeft a) := rfl

/-- The image of a nonzero closed subgroup under a nonzero scalar is a nonzero ideal, hence open. -/
theorem isOpen_closedAddSubgroup_map_mulLeft (M : ClosedAddSubgroup (ℤ_[p]))
    (hM : M.toAddSubgroup ≠ ⊥) (a : ℤ_[p]) (ha : a ≠ 0) :
    IsOpen (M.toAddSubgroup.map (AddMonoidHom.mulLeft a) : Set (ℤ_[p])) := by
  let J : Ideal (ℤ_[p]) :=
    Submodule.map (LinearMap.mulLeft (ℤ_[p]) a) (closedAddSubgroupIdeal M)
  have hJ : J ≠ ⊥ := by
    intro hzero
    apply hM
    apply le_antisymm _ bot_le
    intro x hx
    have hax : a * x ∈ J := ⟨x, hx, rfl⟩
    rw [hzero] at hax
    exact (mul_eq_zero.mp hax).resolve_left ha
  rw [← closedAddSubgroupIdeal_map_mulLeft_toAddSubgroup M a]
  exact (IsDiscreteValuationRing.isOpen_iff (I := J)).mpr hJ

/-- For a nonzero scalar `a`, the image `a • M` has finite relative index in `M`. -/
theorem closedAddSubgroup_map_mulLeft_finiteRelIndex
    (M : ClosedAddSubgroup (ℤ_[p])) (a : ℤ_[p]) (ha : a ≠ 0) :
    (M.toAddSubgroup.map (AddMonoidHom.mulLeft a)).IsFiniteRelIndex M.toAddSubgroup := by
  by_cases hM : M.toAddSubgroup = ⊥
  · simp [hM]
  · have hopen := isOpen_closedAddSubgroup_map_mulLeft M hM a ha
    have hrelopen := AddSubgroup.addSubgroupOf_isOpen M.toAddSubgroup
      (M.toAddSubgroup.map (AddMonoidHom.mulLeft a)) hopen
    have : CompactSpace M.toAddSubgroup := isCompact_iff_compactSpace.mp M.isClosed'.isCompact
    have := AddSubgroup.quotient_finite_of_isOpen
      ((M.toAddSubgroup.map (AddMonoidHom.mulLeft a)).addSubgroupOf M.toAddSubgroup) hrelopen
    exact AddSubgroup.isFiniteRelIndex_iff_finiteIndex.mpr
      AddSubgroup.finiteIndex_of_finite_quotient

/-- The image under a nonzero scalar has positive relative index in a closed additive
subgroup of `ℤ_[p]`. -/
theorem closedAddSubgroup_map_mulLeft_relIndex_pos
    (M : ClosedAddSubgroup (ℤ_[p])) (a : ℤ_[p]) (ha : a ≠ 0) :
    0 < (M.toAddSubgroup.map (AddMonoidHom.mulLeft a)).relIndex M.toAddSubgroup := by
  have := closedAddSubgroup_map_mulLeft_finiteRelIndex M a ha
  exact Nat.pos_of_ne_zero AddSubgroup.relIndex_ne_zero

/-- Every scalar image of the zero subgroup has relative index one in that subgroup. -/
theorem closedAddSubgroup_map_mulLeft_relIndex_eq_one_of_eq_bot
    (M : ClosedAddSubgroup (ℤ_[p])) (hM : M.toAddSubgroup = ⊥) (a : ℤ_[p]) :
    (M.toAddSubgroup.map (AddMonoidHom.mulLeft a)).relIndex M.toAddSubgroup = 1 := by
  simp [hM]

end

end PadicInt
