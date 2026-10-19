/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic

/-!
# Membership in a directed supremum of intermediate fields

An element lies in the supremum of a directed family of intermediate fields iff it lies in one of
them.

Upstream candidate: `Mathlib.FieldTheory.IntermediateField.Adjoin.Basic`.
-/

@[expose] public section

namespace IntermediateField

variable {K L : Type*} [Field K] [Field L] [Algebra K L]
  {ι : Type*} [Nonempty ι] {t : ι → IntermediateField K L}

theorem mem_iSup_of_directed (dir : Directed (· ≤ ·) t) {x : L} :
    x ∈ iSup t ↔ ∃ i, x ∈ t i := by
  rw [← SetLike.mem_coe, coe_iSup_of_directed dir, Set.mem_iUnion]
  rfl

theorem mem_iSup_of_monotone [Preorder ι] [IsDirectedOrder ι] (hm : Monotone t) {x : L} :
    x ∈ iSup t ↔ ∃ i, x ∈ t i :=
  mem_iSup_of_directed hm.directed_le

end IntermediateField
