/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FalseTateExtension.Mathlib.NumberTheory.Padics.ClosedAddSubgroup
public import Mathlib.Algebra.Group.Pointwise.Set.Card
public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.Topology.Algebra.Group.Pointwise

/-!
# Scalar multiplication on closed additive subgroups of `ℤ_[p]`

The structure theory of closed additive subgroups of `ℤ_[p]` is in
`Mathlib/NumberTheory/Padics/ClosedAddSubgroup`. This file adds the uniform index bounds for
multiplication by a nonzero scalar `a`: the image of `a` has finite index in `ℤ_[p]`, and the
relative index of `a • M` in `M` is the same for every nonzero closed subgroup `M`.

## Main results

* `PadicInt.closedAddSubgroup_map_mulLeft_relIndex_eq`
* `PadicInt.closedAddSubgroup_map_mulLeft_relIndex_le`
-/

@[expose] public section

namespace PadicInt

variable {p : ℕ} [Fact p.Prime]

/-- The image of multiplication by a nonzero scalar has finite index. -/
theorem mulLeft_range_finiteIndex (a : ℤ_[p]) (ha : a ≠ 0) :
    (AddMonoidHom.mulLeft a).range.FiniteIndex := by
  let M : ClosedAddSubgroup (ℤ_[p]) := ⟨⊤, isClosed_univ⟩
  have h : ((⊤ : AddSubgroup (ℤ_[p])).map (AddMonoidHom.mulLeft a)).IsFiniteRelIndex ⊤ :=
    closedAddSubgroup_map_mulLeft_finiteRelIndex M a ha
  simpa only [AddSubgroup.map_top] using AddSubgroup.isFiniteRelIndex_top_iff.mp h

/-- The uniform scalar-index constant is positive in the index convention. -/
theorem mulLeft_range_index_pos (a : ℤ_[p]) (ha : a ≠ 0) :
    0 < (AddMonoidHom.mulLeft a).range.index := by
  have := mulLeft_range_finiteIndex a ha
  exact Nat.pos_of_ne_zero AddSubgroup.FiniteIndex.index_ne_zero

/-- Multiplication by a scalar has the same relative index on every nonzero
closed additive subgroup of the p-adic integers. -/
theorem closedAddSubgroup_map_mulLeft_relIndex_eq
    (M : ClosedAddSubgroup (ℤ_[p])) (hM : M.toAddSubgroup ≠ ⊥) (a : ℤ_[p]) :
    (M.toAddSubgroup.map (AddMonoidHom.mulLeft a)).relIndex M.toAddSubgroup =
      (AddMonoidHom.mulLeft a).range.index := by
  obtain hzero | ⟨s, hs⟩ := closedAddSubgroup_eq_bot_or_span_pow M
  · exact (hM hzero).elim
  let f : ℤ_[p] →+ ℤ_[p] := AddMonoidHom.mulLeft ((p : ℤ_[p]) ^ s)
  have hp : (p : ℤ_[p]) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hf : Function.Injective f := by
    intro x y h
    exact mul_left_cancel₀ (pow_ne_zero s hp) h
  have htop : (⊤ : AddSubgroup (ℤ_[p])).map f = M.toAddSubgroup := by
    rw [hs]
    ext x
    simp [f, Ideal.mem_span_singleton, dvd_def, eq_comm]
  have hcomm : M.toAddSubgroup.map (AddMonoidHom.mulLeft a) =
      ((⊤ : AddSubgroup (ℤ_[p])).map (AddMonoidHom.mulLeft a)).map f := by
    rw [← htop, AddSubgroup.map_map, AddSubgroup.map_map]
    congr 1
    apply AddMonoidHom.ext
    intro x
    change a * ((p : ℤ_[p]) ^ s * x) = (p : ℤ_[p]) ^ s * (a * x)
    exact mul_left_comm a ((p : ℤ_[p]) ^ s) x
  calc
    _ = (((⊤ : AddSubgroup (ℤ_[p])).map (AddMonoidHom.mulLeft a)).map f).relIndex
        ((⊤ : AddSubgroup (ℤ_[p])).map f) := by rw [hcomm, htop]
    _ = ((⊤ : AddSubgroup (ℤ_[p])).map (AddMonoidHom.mulLeft a)).relIndex ⊤ :=
      AddSubgroup.relIndex_map_map_of_injective _ _ hf
    _ = _ := by rw [AddSubgroup.relIndex_top_right, AddSubgroup.map_top]

/-- A single scalar-index constant bounds every closed additive subgroup,
including the zero subgroup. -/
theorem closedAddSubgroup_map_mulLeft_relIndex_le
    (M : ClosedAddSubgroup (ℤ_[p])) (a : ℤ_[p]) (ha : a ≠ 0) :
    (M.toAddSubgroup.map (AddMonoidHom.mulLeft a)).relIndex M.toAddSubgroup ≤
      (AddMonoidHom.mulLeft a).range.index := by
  by_cases hM : M.toAddSubgroup = ⊥
  · rw [closedAddSubgroup_map_mulLeft_relIndex_eq_one_of_eq_bot M hM]
    exact mulLeft_range_index_pos a ha
  · exact (closedAddSubgroup_map_mulLeft_relIndex_eq M hM a).le

end PadicInt
