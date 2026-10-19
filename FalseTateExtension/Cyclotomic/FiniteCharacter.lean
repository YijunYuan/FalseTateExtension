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

The action on `ζ_{p^m}` defines the cyclotomic character
`χ_m : Gal(ℚ_[p](ζ_{p^m})/ℚ_[p]) →* (ℤ/p^m)ˣ`, `g(ζ_{p^m}) = ζ_{p^m}^{χ_m(g)}`. It is an
isomorphism, since `Φ_{p^m}` is irreducible over `ℚ_[p]`, and `Gal(ℚ_[p](ζ_{p^m})/ℚ_[p])` has
order `φ(p^m)`.

## Main results

* `cyclotomicLayerCharacter`: the character `χ_m`, with `cyclotomicLayerCharacter_spec`
* `cyclotomicLayerCharacter_injective`, `cyclotomicLayerCharacter_surjective`: `χ_m` is bijective
* `cyclotomicLayerCharacter_eq_autEquivPow`: `χ_m` is Mathlib's `IsCyclotomicExtension.autEquivPow`
* `card_cyclotomicLayer_galois`: `|Gal(ℚ_[p](ζ_{p^m})/ℚ_[p])| = φ(p^m)`

## References

* Serre, *Local Fields*, Chapter IV, §4, Proposition 17.
-/

@[expose] public section

noncomputable section

namespace FalseTateExtension

variable (p : ℕ) [Fact p.Prime] (m : ℕ)

local instance : NeZero (p ^ m) := ⟨pow_ne_zero m (Fact.out : p.Prime).ne_zero⟩

/-- The cyclotomic character `χ_m : Gal(ℚ_[p](ζ_{p^m})/ℚ_[p]) →* (ℤ/p^m)ˣ`, determined by
`g(ζ_{p^m}) = ζ_{p^m}^{χ_m(g)}`. -/
def cyclotomicLayerCharacter :
    (cyclotomicLayer (K := ℚ_[p]) p m ≃ₐ[ℚ_[p]] cyclotomicLayer (K := ℚ_[p]) p m) →*
      (ZMod (p ^ m))ˣ :=
  (isPrimitiveRoot_cyclotomicLayerRoot p m).autToPow (ℚ_[p])

/-- `g(ζ_{p^m}) = ζ_{p^m}^{χ_m(g)}`. -/
theorem cyclotomicLayerCharacter_spec
    (g : cyclotomicLayer (K := ℚ_[p]) p m ≃ₐ[ℚ_[p]] cyclotomicLayer (K := ℚ_[p]) p m) :
    g (cyclotomicLayerRoot p m) = cyclotomicLayerRoot p m ^
      (cyclotomicLayerCharacter p m g : ZMod (p ^ m)).val :=
  ((isPrimitiveRoot_cyclotomicLayerRoot p m).autToPow_spec (ℚ_[p]) g).symm

/-- If `g(ζ_{p^m}) = ζ_{p^m}^u` for a unit `u` of `ℤ/p^m`, then `χ_m(g) = u`. -/
theorem cyclotomicLayerCharacter_unique
    (g : cyclotomicLayer (K := ℚ_[p]) p m ≃ₐ[ℚ_[p]] cyclotomicLayer (K := ℚ_[p]) p m)
    (u : (ZMod (p ^ m))ˣ)
    (hu : g (cyclotomicLayerRoot p m) = cyclotomicLayerRoot p m ^ (u : ZMod (p ^ m)).val) :
    cyclotomicLayerCharacter p m g = u := by
  apply Units.ext
  apply ZMod.val_injective
  exact (isPrimitiveRoot_cyclotomicLayerRoot p m).pow_inj (ZMod.val_lt _) (ZMod.val_lt _)
    ((cyclotomicLayerCharacter_spec p m g).symm.trans hu)

/-- The cyclotomic character `χ_m` is injective. -/
theorem cyclotomicLayerCharacter_injective : Function.Injective (cyclotomicLayerCharacter p m) :=
  (isPrimitiveRoot_cyclotomicLayerRoot p m).autToPow_injective (ℚ_[p])

/-- The cyclotomic character `χ_m` agrees with Mathlib's `IsCyclotomicExtension.autEquivPow`. -/
theorem cyclotomicLayerCharacter_eq_autEquivPow
    (g : cyclotomicLayer (K := ℚ_[p]) p m ≃ₐ[ℚ_[p]] cyclotomicLayer (K := ℚ_[p]) p m) :
    cyclotomicLayerCharacter p m g = IsCyclotomicExtension.autEquivPow
      (cyclotomicLayer (K := ℚ_[p]) p m) (Padic.irreducible_cyclotomic_prime_pow p m) g := by
  change (isPrimitiveRoot_cyclotomicLayerRoot p m).autToPow ℚ_[p] g =
    (IsCyclotomicExtension.zeta_spec (p ^ m) ℚ_[p] _).autToPow ℚ_[p] g
  rw [(isPrimitiveRoot_cyclotomicLayerRoot p m).autToPow_eq_modularCyclotomicCharacter (p ^ m)
    ℚ_[p], (IsCyclotomicExtension.zeta_spec (p ^ m) ℚ_[p] _).autToPow_eq_modularCyclotomicCharacter
    (p ^ m) ℚ_[p]]

/-- The cyclotomic character `χ_m` is surjective. -/
theorem cyclotomicLayerCharacter_surjective :
    Function.Surjective (cyclotomicLayerCharacter p m) := fun u ↦
  ⟨(IsCyclotomicExtension.autEquivPow _ (Padic.irreducible_cyclotomic_prime_pow p m)).symm u,
    by rw [cyclotomicLayerCharacter_eq_autEquivPow, MulEquiv.apply_symm_apply]⟩

/-- `|Gal(ℚ_[p](ζ_{p^m})/ℚ_[p])| = φ(p^m)`. -/
theorem card_cyclotomicLayer_galois :
    Nat.card (cyclotomicLayer (K := ℚ_[p]) p m ≃ₐ[ℚ_[p]] cyclotomicLayer (K := ℚ_[p]) p m) =
      (p ^ m).totient := by
  rw [IsGalois.card_aut_eq_finrank, finrank_cyclotomicLayer_padic]

end FalseTateExtension

end
