/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.FieldTheory.Normal.Defs

/-!
# Restriction of automorphisms between nested intermediate fields

For intermediate fields `E ≤ F` of `L/K` with `E/K` normal, every `K`-automorphism of `F`
restricts to a `K`-automorphism of `E`. This is Mathlib's `AlgEquiv.restrictNormalHom` for the
algebra structure `IntermediateField.inclusion hEF`; packaging it once avoids re-installing that
algebra structure at every use.

Upstream candidate: `Mathlib.FieldTheory.Normal`.
-/

@[expose] public section

namespace IntermediateField

variable {K L : Type*} [Field K] [Field L] [Algebra K L] {E F : IntermediateField K L}

/-- The algebra structure on `F` over `E ≤ F` given by the inclusion. Not an instance: `hEF` is
a proof, so it cannot be found by instance search. -/
abbrev algebraOfLE (hEF : E ≤ F) : Algebra E F := (inclusion hEF).toAlgebra

/-- The inclusion algebra of nested intermediate fields is compatible with the base field. -/
theorem isScalarTower_of_le (hEF : E ≤ F) :
    letI := algebraOfLE hEF; IsScalarTower K E F :=
  letI := algebraOfLE hEF
  IsScalarTower.of_algebraMap_eq (congrFun rfl)

/-- Restriction of `K`-automorphisms of `F` to the normal subfield `E ≤ F`. -/
noncomputable def restrictNormalHomOfLE (hEF : E ≤ F) [Normal K E] :
    (F ≃ₐ[K] F) →* (E ≃ₐ[K] E) :=
  letI := algebraOfLE hEF
  haveI := isScalarTower_of_le hEF
  AlgEquiv.restrictNormalHom E

/-- Restriction to a normal intermediate field commutes with its inclusion. -/
theorem restrictNormalHomOfLE_commutes (hEF : E ≤ F) [Normal K E] (g : F ≃ₐ[K] F) (x : E) :
    inclusion hEF (restrictNormalHomOfLE hEF g x) = g (inclusion hEF x) :=
  letI := algebraOfLE hEF
  haveI := isScalarTower_of_le hEF
  AlgEquiv.restrictNormal_commutes g E x

/-- Restriction to a normal intermediate field preserves the action in the ambient field. -/
theorem coe_restrictNormalHomOfLE_apply (hEF : E ≤ F) [Normal K E] (g : F ≃ₐ[K] F) (x : E) :
    (restrictNormalHomOfLE hEF g x : L) = g ⟨x, hEF x.2⟩ :=
  congrArg Subtype.val (restrictNormalHomOfLE_commutes hEF g x)

/-- Every automorphism of a normal intermediate field extends to a larger normal field. -/
theorem restrictNormalHomOfLE_surjective (hEF : E ≤ F) [Normal K E] [Normal K F] :
    Function.Surjective (restrictNormalHomOfLE hEF) :=
  letI := algebraOfLE hEF
  haveI := isScalarTower_of_le hEF
  AlgEquiv.restrictNormalHom_surjective F

/-- Restricting an automorphism to the same field gives the identity homomorphism. -/
@[simp]
theorem restrictNormalHomOfLE_refl [Normal K E] :
    restrictNormalHomOfLE (le_refl E) = MonoidHom.id (E ≃ₐ[K] E) := by
  ext g x
  exact congrArg Subtype.val (restrictNormalHomOfLE_commutes (le_refl E) g x)

/-- Successive restrictions to nested normal intermediate fields compose to restriction. -/
theorem restrictNormalHomOfLE_comp {G : IntermediateField K L} (hEF : E ≤ F) (hFG : F ≤ G)
    [Normal K E] [Normal K F] :
    (restrictNormalHomOfLE hEF).comp (restrictNormalHomOfLE hFG) =
      restrictNormalHomOfLE (hEF.trans hFG) := by
  ext g x
  rw [MonoidHom.comp_apply, coe_restrictNormalHomOfLE_apply, coe_restrictNormalHomOfLE_apply,
    coe_restrictNormalHomOfLE_apply]

end IntermediateField
