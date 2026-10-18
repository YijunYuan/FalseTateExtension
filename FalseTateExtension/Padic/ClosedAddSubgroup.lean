module

public import Mathlib.NumberTheory.Padics.ProperSpace
public import Mathlib.Topology.Algebra.Group.ClosedSubgroup
public import Mathlib.Topology.Algebra.Ring.Compact
public import Mathlib.GroupTheory.Index

/-!
# Closed additive subgroups of the p-adic integers

Every actual closed additive subgroup is stable under p-adic scalars and is
therefore an ideal with the same carrier. Such a subgroup is zero or a power
of the maximal ideal. Multiplication by a nonzero scalar has an actual image
of finite positive relative index, including index one for the zero subgroup.
This proves blueprint `ft:padic-closed-additive-subgroups`, used in the affine
commutator argument following Liu, Section 5.1.
-/

@[expose] public section

namespace PadicInt

noncomputable section

variable {p : ℕ} [Fact p.Prime]

/-- Closed additive subgroups of the p-adic integers are stable under every
p-adic scalar, by density of the natural integers. -/
theorem mul_mem_closedAddSubgroup (M : ClosedAddSubgroup (PadicInt p))
    (a x : PadicInt p) (hx : x ∈ M) : a * x ∈ M := by
  apply (denseRange_natCast (p := p)).induction_on (p := fun b ↦ b * x ∈ M) a
  · exact M.isClosed'.preimage (continuous_id.mul continuous_const)
  · intro n
    change (n : PadicInt p) * x ∈ M.toAddSubgroup
    simpa only [nsmul_eq_mul] using M.toAddSubgroup.nsmul_mem hx n

/-- The ideal carried by an actual closed additive subgroup, without changing
any of its elements. -/
def closedAddSubgroupIdeal (M : ClosedAddSubgroup (PadicInt p)) : Ideal (PadicInt p) where
  carrier := M
  zero_mem' := M.zero_mem
  add_mem' := M.add_mem
  smul_mem' a x hx := mul_mem_closedAddSubgroup M a x hx

@[simp]
theorem mem_closedAddSubgroupIdeal (M : ClosedAddSubgroup (PadicInt p)) (x : PadicInt p) :
    x ∈ closedAddSubgroupIdeal M ↔ x ∈ M := Iff.rfl

theorem closedAddSubgroupIdeal_toAddSubgroup (M : ClosedAddSubgroup (PadicInt p)) :
    (closedAddSubgroupIdeal M).toAddSubgroup = M.toAddSubgroup := rfl

/-- Every actual closed additive subgroup is zero or the additive group of a
power of the maximal ideal. -/
theorem closedAddSubgroup_eq_bot_or_span_pow (M : ClosedAddSubgroup (PadicInt p)) :
    M.toAddSubgroup = ⊥ ∨ ∃ s : ℕ,
      M.toAddSubgroup = (Ideal.span {(p : PadicInt p) ^ s}).toAddSubgroup := by
  by_cases hM : closedAddSubgroupIdeal M = ⊥
  · exact Or.inl (congrArg (fun I : Ideal (PadicInt p) ↦ I.toAddSubgroup) hM)
  · obtain ⟨s, hs⟩ := ideal_eq_span_pow_p hM
    exact Or.inr ⟨s, congrArg (fun I : Ideal (PadicInt p) ↦ I.toAddSubgroup) hs⟩

/-- The actual additive image under multiplication by any scalar lies in the
original closed subgroup. -/
theorem closedAddSubgroup_map_mulLeft_le (M : ClosedAddSubgroup (PadicInt p)) (a : PadicInt p) :
    M.toAddSubgroup.map (AddMonoidHom.mulLeft a) ≤ M.toAddSubgroup := by
  rintro y ⟨x, hx, rfl⟩
  exact mul_mem_closedAddSubgroup M a x hx

/-- The actual scalar image is also the image of the same-carrier ideal under
the canonical linear multiplication map. -/
theorem closedAddSubgroupIdeal_map_mulLeft_toAddSubgroup
    (M : ClosedAddSubgroup (PadicInt p)) (a : PadicInt p) :
    (Submodule.map (LinearMap.mulLeft (PadicInt p) a) (closedAddSubgroupIdeal M)).toAddSubgroup =
      M.toAddSubgroup.map (AddMonoidHom.mulLeft a) := rfl

/-- The actual image of a nonzero closed subgroup by a nonzero scalar is open
in the p-adic integers, since it is a nonzero ideal. -/
theorem isOpen_closedAddSubgroup_map_mulLeft (M : ClosedAddSubgroup (PadicInt p))
    (hM : M.toAddSubgroup ≠ ⊥) (a : PadicInt p) (ha : a ≠ 0) :
    IsOpen (M.toAddSubgroup.map (AddMonoidHom.mulLeft a) : Set (PadicInt p)) := by
  let J : Ideal (PadicInt p) :=
    Submodule.map (LinearMap.mulLeft (PadicInt p) a) (closedAddSubgroupIdeal M)
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

/-- The actual scalar image has finite relative index, including when the
original closed subgroup is zero. -/
theorem closedAddSubgroup_map_mulLeft_finiteRelIndex
    (M : ClosedAddSubgroup (PadicInt p)) (a : PadicInt p) (ha : a ≠ 0) :
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

/-- The finite relative index is positive; the zero convention for infinite
index does not occur for a nonzero scalar. -/
theorem closedAddSubgroup_map_mulLeft_relIndex_pos
    (M : ClosedAddSubgroup (PadicInt p)) (a : PadicInt p) (ha : a ≠ 0) :
    0 < (M.toAddSubgroup.map (AddMonoidHom.mulLeft a)).relIndex M.toAddSubgroup := by
  have := closedAddSubgroup_map_mulLeft_finiteRelIndex M a ha
  exact Nat.pos_of_ne_zero AddSubgroup.relIndex_ne_zero

/-- For the zero subgroup the actual scalar image has relative index one. -/
theorem closedAddSubgroup_map_mulLeft_relIndex_eq_one_of_eq_bot
    (M : ClosedAddSubgroup (PadicInt p)) (hM : M.toAddSubgroup = ⊥) (a : PadicInt p) :
    (M.toAddSubgroup.map (AddMonoidHom.mulLeft a)).relIndex M.toAddSubgroup = 1 := by
  simp [hM]

end

end PadicInt
