/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.FieldTheory.Galois.Infinite

/-!
# Restriction of scalars and fixing subgroups

For a tower `F ⊆ K ⊆ Ω`, the image of `Gal(Ω/K) → Gal(Ω/F)` is the subgroup fixing the image of
`K` in `Ω`; when `Ω/F` is Galois its index is `[K : F]`, with no finiteness assumption on `Ω`.

Upstream candidate: `Mathlib.FieldTheory.Galois.Infinite`.
-/

@[expose] public section

namespace AlgEquiv

variable (F K Ω : Type*) [Field F] [Field K] [Field Ω]
  [Algebra F K] [Algebra K Ω] [Algebra F Ω] [IsScalarTower F K Ω]

/-- The range of restriction of scalars is the subgroup fixing the image of `K`. -/
theorem range_restrictScalarsHom_eq_fixingSubgroup :
    (restrictScalarsHom F (S := K) (A := Ω)).range =
      (IsScalarTower.toAlgHom F K Ω).fieldRange.fixingSubgroup := by
  ext g
  constructor
  · rintro ⟨h, rfl⟩
    rw [IntermediateField.mem_fixingSubgroup_iff]
    rintro x ⟨k, rfl⟩
    exact h.commutes k
  · intro hg
    let h : Ω ≃ₐ[K] Ω :=
      { g.toRingEquiv with
        commutes' := fun k ↦
          (IntermediateField.mem_fixingSubgroup_iff
            (IsScalarTower.toAlgHom F K Ω).fieldRange g).mp hg _ ⟨k, rfl⟩ }
    exact ⟨h, by ext x; rfl⟩

/-- When `Ω/F` is Galois, restriction of scalars has index `[K : F]`. -/
theorem index_range_restrictScalarsHom [IsGalois F Ω] :
    (restrictScalarsHom F (S := K) (A := Ω)).range.index = Module.finrank F K := by
  rw [range_restrictScalarsHom_eq_fixingSubgroup,
    ← IntermediateField.finrank_eq_fixingSubgroup_index]
  exact (IsScalarTower.toAlgHom F K Ω).equivFieldRange.toLinearEquiv.finrank_eq.symm

end AlgEquiv
