/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FalseTateExtension.GaloisStructure
public import FalseTateExtension.Padic.InfiniteCharacter
public import FalseTateExtension.Padic.TameUnits

/-!
# The actual tame false Tate generator

The canonical tame units lift through the original radical fixer.
-/

@[expose] public section

noncomputable section

namespace FalseTateExtension

variable (p : ℕ) [Fact p.Prime]

/-- A chosen canonical tame unit with primitive residue. -/
def tameUnit : (PadicInt p)ˣ :=
  (PadicInt.exists_teichmullerUnit_orderOf (p := p)).choose

theorem orderOf_tameUnit : orderOf (tameUnit p) = p - 1 :=
  (PadicInt.exists_teichmullerUnit_orderOf (p := p)).choose_spec.1

theorem orderOf_tameUnit_residue :
    orderOf (Units.map (PadicInt.toZMod : PadicInt p →+* ZMod p).toMonoidHom
      (tameUnit p)) = p - 1 :=
  (PadicInt.exists_teichmullerUnit_orderOf (p := p)).choose_spec.2

variable {π : (NormedField.valuation (K := Padic p)).valuationSubring}

/-- The actual radical fixer contains the chosen tame generator. -/
def tameGenerator (hp₂ : p ≠ 2) (hπ : Irreducible π) :
    falseTateKummerFixing p (π : Padic p) :=
  (kummerFixingEquivCyclotomicImage p hp₂ hπ).symm
    ⟨tameUnit p, cyclotomicExtensionCharacter_surjective_padic p (tameUnit p)⟩

/-- Its actual cyclotomic character is the chosen unit. -/
@[simp]
theorem padicCyclotomicCharacter_tameGenerator (hp₂ : p ≠ 2) (hπ : Irreducible π) :
    padicCyclotomicCharacter p (π : Padic p) (tameGenerator p hp₂ hπ).val =
      tameUnit p := by
  exact congrArg Subtype.val
    ((kummerFixingEquivCyclotomicImage p hp₂ hπ).apply_symm_apply _)

/-- The actual generator has exact order p-1 in the original Galois group. -/
theorem orderOf_tameGenerator (hp₂ : p ≠ 2) (hπ : Irreducible π) :
    orderOf (tameGenerator p hp₂ hπ).val = p - 1 := by
  let g := tameGenerator p hp₂ hπ
  let e := kummerFixingEquivCyclotomicImage p hp₂ hπ
  calc
    orderOf g.val = orderOf g :=
      orderOf_injective (falseTateKummerFixing p (π : Padic p)).subtype
        Subtype.val_injective g
    _ = orderOf (e g) := (orderOf_injective e.toMonoidHom e.injective g).symm
    _ = orderOf (e g).val :=
      (orderOf_injective (cyclotomicExtensionCharacter (K := Padic p) p).range.subtype
        Subtype.val_injective (e g)).symm
    _ = orderOf (tameUnit p) := congrArg orderOf (padicCyclotomicCharacter_tameGenerator
      p hp₂ hπ)
    _ = p - 1 := orderOf_tameUnit p

/-- The actual generator fixes every element of the original radical field. -/
theorem tameGenerator_fixes_kummerExtension (hp₂ : p ≠ 2) (hπ : Irreducible π)
    (x : kummerExtension p (π : Padic p)) :
    (tameGenerator p hp₂ hπ).val (falseTateKummerInclusion p (π : Padic p) x) =
      falseTateKummerInclusion p (π : Padic p) x :=
  (IntermediateField.mem_fixingSubgroup_iff _ _).mp
    (tameGenerator p hp₂ hπ).property _ ⟨x, rfl⟩

/-- Continuous p-adic powers of the prescribed original Kummer generator. -/
def tauPadicPower (hp₂ : p ≠ 2) (hπ : Irreducible π) (a : PadicInt p) :
    (padicCyclotomicCharacter p (π : Padic p)).ker :=
  (fullKummerKernelMulEquiv p hp₂ hπ).symm (Multiplicative.ofAdd a)

theorem continuous_tauPadicPower (hp₂ : p ≠ 2) (hπ : Irreducible π) :
    Continuous (tauPadicPower p hp₂ hπ) :=
  (fullKummerKernelMulEquiv p hp₂ hπ).symm.continuous.comp continuous_ofAdd

@[simp]
theorem padicKummerExponent_tauPadicPower (hp₂ : p ≠ 2) (hπ : Irreducible π)
    (a : PadicInt p) :
    padicKummerExponent p (π : Padic p) (fun h => hπ.ne_zero (Subtype.ext h))
      (tauPadicPower p hp₂ hπ a).val = a := by
  exact congrArg Multiplicative.toAdd
    ((fullKummerKernelMulEquiv p hp₂ hπ).apply_symm_apply (Multiplicative.ofAdd a))

@[simp]
theorem tauPadicPower_one (hp₂ : p ≠ 2) (hπ : Irreducible π) :
    tauPadicPower p hp₂ hπ 1 = tau p hp₂ hπ := rfl

/-- These continuous powers extend the actual signed integral powers. -/
theorem tauPadicPower_intCast (hp₂ : p ≠ 2) (hπ : Irreducible π) (n : ℤ) :
    tauPadicPower p hp₂ hπ (n : PadicInt p) = tau p hp₂ hπ ^ n := by
  have h := map_zpow (fullKummerKernelMulEquiv p hp₂ hπ).symm
    (Multiplicative.ofAdd (1 : PadicInt p)) n
  simpa only [tauPadicPower, ← tauPadicPower_one, ← ofAdd_zsmul,
    zsmul_one] using h

/-- Conjugation in the original Galois group is the actual continuous
Kummer power specified by the original cyclotomic character. -/
theorem tameGenerator_conj_tau (hp₂ : p ≠ 2) (hπ : Irreducible π) :
    (tameGenerator p hp₂ hπ).val * (tau p hp₂ hπ).val *
      (tameGenerator p hp₂ hπ).val⁻¹ =
    (tauPadicPower p hp₂ hπ
      (padicCyclotomicCharacter p (π : Padic p) (tameGenerator p hp₂ hπ).val :
        PadicInt p)).val := by
  let hπ₀ : (π : Padic p) ≠ 0 := fun h => hπ.ne_zero (Subtype.ext h)
  have hb := (mem_falseTateKummerFixing_iff p (π : Padic p) hπ₀
    (tameGenerator p hp₂ hπ).val).mp (tameGenerator p hp₂ hπ).property
  have hbi := (mem_falseTateKummerFixing_iff p (π : Padic p) hπ₀
    (tameGenerator p hp₂ hπ).val⁻¹).mp
      ((falseTateKummerFixing p (π : Padic p)).inv_mem (tameGenerator p hp₂ hπ).property)
  apply padicCoordinates_injective p (π : Padic p) hπ₀
  apply Prod.ext
  · change padicKummerExponent p (π : Padic p) hπ₀ _ =
      padicKummerExponent p (π : Padic p) hπ₀ _
    rw [padicKummerExponent_mul, padicKummerExponent_mul, hb, hbi,
      padicKummerExponent_tau, padicKummerExponent_tauPadicPower]
    simp only [zero_add, mul_one, mul_zero, add_zero]
  · change padicCyclotomicCharacter p (π : Padic p) _ =
      padicCyclotomicCharacter p (π : Padic p) _
    rw [map_mul, map_mul, map_inv, (tau p hp₂ hπ).property,
      (tauPadicPower p hp₂ hπ _).property, mul_one, mul_inv_cancel]

/-- The original tame generator has primitive finite residue character. -/
theorem orderOf_tameGenerator_residueCharacter (hp₂ : p ≠ 2) (hπ : Irreducible π) :
    orderOf (Units.map (PadicInt.toZMod : PadicInt p →+* ZMod p).toMonoidHom
      (padicCyclotomicCharacter p (π : Padic p) (tameGenerator p hp₂ hπ).val)) = p - 1 := by
  rw [padicCyclotomicCharacter_tameGenerator]
  exact orderOf_tameUnit_residue p

/-- The original radical inclusion supplies the relative scalar structure. -/
local instance tameRelativeAlgebra :
    Algebra (kummerExtension p (π : Padic p)) (falseTateExtension p (π : Padic p)) :=
  RingHom.toAlgebra (Subsemiring.inclusion
    (kummerExtension_le_falseTateExtension p (π : Padic p)))

local instance tameRelativeScalarTower :
    IsScalarTower (Padic p) (kummerExtension p (π : Padic p))
      (falseTateExtension p (π : Padic p)) :=
  IsScalarTower.of_algebraMap_eq (congrFun rfl)

/-- The same tame automorphism in the original relative Galois group. -/
def relativeTameGenerator (hp₂ : p ≠ 2) (hπ : Irreducible π) :
    falseTateExtension p (π : Padic p) ≃ₐ[kummerExtension p (π : Padic p)]
      falseTateExtension p (π : Padic p) :=
  { (tameGenerator p hp₂ hπ).val.toRingEquiv with
    commutes' := tameGenerator_fixes_kummerExtension p hp₂ hπ }

/-- Restricting scalars recovers exactly the original tame generator. -/
theorem relativeTameGenerator_restrictScalars (hp₂ : p ≠ 2) (hπ : Irreducible π) :
    (relativeTameGenerator p hp₂ hπ).restrictScalars (Padic p) =
      (tameGenerator p hp₂ hπ).val := by
  apply AlgEquiv.ext
  intro x
  rfl

theorem orderOf_relativeTameGenerator (hp₂ : p ≠ 2) (hπ : Irreducible π) :
    orderOf (relativeTameGenerator p hp₂ hπ) = p - 1 := by
  let f := AlgEquiv.restrictScalarsHom (Padic p) (S := kummerExtension p (π : Padic p))
    (A := falseTateExtension p (π : Padic p))
  have hf : Function.Injective f := by
    intro g h heq
    apply AlgEquiv.ext
    intro x
    exact congrArg (fun k : falseTateExtension p (π : Padic p) ≃ₐ[Padic p]
      falseTateExtension p (π : Padic p) => k x) heq
  have h := orderOf_injective f hf (relativeTameGenerator p hp₂ hπ)
  change orderOf ((relativeTameGenerator p hp₂ hπ).restrictScalars (Padic p)) = _ at h
  rw [relativeTameGenerator_restrictScalars, orderOf_tameGenerator] at h
  exact h.symm

end FalseTateExtension
