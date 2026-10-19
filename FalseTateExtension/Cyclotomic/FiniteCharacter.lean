/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FalseTateExtension.Cyclotomic.Ramification
public import Mathlib.NumberTheory.Cyclotomic.Gal
public import Mathlib.NumberTheory.Cyclotomic.CyclotomicCharacter

/-!
# The finite cyclotomic character over `ℚ_[p]`

The action on `ζ_{p^m}` defines the character `Gal(ℚ_[p](ζ_{p^m})/ℚ_[p]) →* (ZMod (p^m))ˣ`. It is
Mathlib's `IsCyclotomicExtension.autEquivPow`, hence bijective, since `Φ_{p^m}` is irreducible over
`ℚ_[p]`. All levels, including zero, and all primes, including two, are covered.
-/

@[expose] public section

noncomputable section

namespace FalseTateExtension

variable (p : ℕ) [Fact p.Prime] (m : ℕ)

local instance : NeZero (p ^ m) := ⟨pow_ne_zero m (Fact.out : p.Prime).ne_zero⟩

/-- The finite rational cyclotomic character, defined by its action on
the primitive root in the cyclotomic layer. -/
def cyclotomicLayerCharacter :
    (cyclotomicLayer (K := ℚ_[p]) p m ≃ₐ[ℚ_[p]] cyclotomicLayer (K := ℚ_[p]) p m) →*
      (ZMod (p ^ m))ˣ :=
  (isPrimitiveRoot_cyclotomicLayerRoot p m).autToPow (ℚ_[p])

/-- The defining action of the finite character. -/
theorem cyclotomicLayerCharacter_spec
    (g : cyclotomicLayer (K := ℚ_[p]) p m ≃ₐ[ℚ_[p]] cyclotomicLayer (K := ℚ_[p]) p m) :
    g (cyclotomicLayerRoot p m) = cyclotomicLayerRoot p m ^
      (cyclotomicLayerCharacter p m g : ZMod (p ^ m)).val :=
  ((isPrimitiveRoot_cyclotomicLayerRoot p m).autToPow_spec (ℚ_[p]) g).symm

/-- The action on the primitive root uniquely specifies the unit. -/
theorem cyclotomicLayerCharacter_unique
    (g : cyclotomicLayer (K := ℚ_[p]) p m ≃ₐ[ℚ_[p]] cyclotomicLayer (K := ℚ_[p]) p m)
    (u : (ZMod (p ^ m))ˣ)
    (hu : g (cyclotomicLayerRoot p m) = cyclotomicLayerRoot p m ^ (u : ZMod (p ^ m)).val) :
    cyclotomicLayerCharacter p m g = u := by
  apply Units.ext
  apply ZMod.val_injective
  exact (isPrimitiveRoot_cyclotomicLayerRoot p m).pow_inj (ZMod.val_lt _) (ZMod.val_lt _)
    ((cyclotomicLayerCharacter_spec p m g).symm.trans hu)

/-- Faithfulness follows because the primitive root generates the
cyclotomic field. -/
theorem cyclotomicLayerCharacter_injective : Function.Injective (cyclotomicLayerCharacter p m) :=
  (isPrimitiveRoot_cyclotomicLayerRoot p m).autToPow_injective (ℚ_[p])

/-- The finite character is Mathlib's `IsCyclotomicExtension.autEquivPow`. -/
theorem cyclotomicLayerCharacter_eq_autEquivPow
    (g : cyclotomicLayer (K := ℚ_[p]) p m ≃ₐ[ℚ_[p]] cyclotomicLayer (K := ℚ_[p]) p m) :
    cyclotomicLayerCharacter p m g = IsCyclotomicExtension.autEquivPow
      (cyclotomicLayer (K := ℚ_[p]) p m) (Padic.irreducible_cyclotomic_prime_pow p m) g := by
  change (isPrimitiveRoot_cyclotomicLayerRoot p m).autToPow ℚ_[p] g =
    (IsCyclotomicExtension.zeta_spec (p ^ m) ℚ_[p] _).autToPow ℚ_[p] g
  rw [(isPrimitiveRoot_cyclotomicLayerRoot p m).autToPow_eq_modularCyclotomicCharacter (p ^ m)
    ℚ_[p], (IsCyclotomicExtension.zeta_spec (p ^ m) ℚ_[p] _).autToPow_eq_modularCyclotomicCharacter
    (p ^ m) ℚ_[p]]

theorem cyclotomicLayerCharacter_surjective :
    Function.Surjective (cyclotomicLayerCharacter p m) := fun u ↦
  ⟨(IsCyclotomicExtension.autEquivPow _ (Padic.irreducible_cyclotomic_prime_pow p m)).symm u,
    by rw [cyclotomicLayerCharacter_eq_autEquivPow, MulEquiv.apply_symm_apply]⟩

/-- `Gal(ℚ_[p](ζ_{p^m})/ℚ_[p])` has order `φ(p^m)`. -/
theorem card_cyclotomicLayer_galois :
    Nat.card (cyclotomicLayer (K := ℚ_[p]) p m ≃ₐ[ℚ_[p]] cyclotomicLayer (K := ℚ_[p]) p m) =
      (p ^ m).totient := by
  rw [IsGalois.card_aut_eq_finrank, finrank_cyclotomicLayer_padic]

end FalseTateExtension

end
