module

public import FalseTateExtension.Padic.CyclotomicRamification
public import Mathlib.NumberTheory.Cyclotomic.Gal

/-!
# The actual finite rational cyclotomic character

The action on the chosen primitive root defines a faithful character of the
actual cyclotomic Galois group. Its degree and the cardinality of the target
unit group are both the prime-power totient, so the character is an isomorphism.
All levels, including zero, and all primes, including two, are covered.

This proves blueprint `ft:finite-cyclotomic-character` by the generator and
finite-cardinality argument.
-/

@[expose] public section

noncomputable section

namespace FalseTateExtension

variable (p : ℕ) [Fact p.Prime] (m : ℕ)

local instance : NeZero (p ^ m) := ⟨pow_ne_zero m (Fact.out : p.Prime).ne_zero⟩

/-- The actual finite rational cyclotomic character, defined by its action on
the existing chosen primitive root in the actual cyclotomic layer. -/
def cyclotomicLayerCharacter :
    (cyclotomicLayer (K := Padic p) p m ≃ₐ[Padic p] cyclotomicLayer (K := Padic p) p m) →*
      (ZMod (p ^ m))ˣ :=
  (isPrimitiveRoot_cyclotomicLayerRoot p m).autToPow (Padic p)

/-- The defining action of the actual finite character. -/
theorem cyclotomicLayerCharacter_spec
    (g : cyclotomicLayer (K := Padic p) p m ≃ₐ[Padic p] cyclotomicLayer (K := Padic p) p m) :
    g (cyclotomicLayerRoot p m) = cyclotomicLayerRoot p m ^
      (cyclotomicLayerCharacter p m g : ZMod (p ^ m)).val :=
  ((isPrimitiveRoot_cyclotomicLayerRoot p m).autToPow_spec (Padic p) g).symm

/-- The action on the actual primitive root uniquely specifies the unit. -/
theorem cyclotomicLayerCharacter_unique
    (g : cyclotomicLayer (K := Padic p) p m ≃ₐ[Padic p] cyclotomicLayer (K := Padic p) p m)
    (u : (ZMod (p ^ m))ˣ)
    (hu : g (cyclotomicLayerRoot p m) = cyclotomicLayerRoot p m ^ (u : ZMod (p ^ m)).val) :
    cyclotomicLayerCharacter p m g = u := by
  apply Units.ext
  apply ZMod.val_injective
  exact (isPrimitiveRoot_cyclotomicLayerRoot p m).pow_inj (ZMod.val_lt _) (ZMod.val_lt _)
    ((cyclotomicLayerCharacter_spec p m g).symm.trans hu)

/-- Faithfulness follows because the actual primitive root generates the
actual cyclotomic field. -/
theorem cyclotomicLayerCharacter_injective : Function.Injective (cyclotomicLayerCharacter p m) :=
  (isPrimitiveRoot_cyclotomicLayerRoot p m).autToPow_injective (Padic p)

/-- The actual finite cyclotomic Galois group has order equal to its actual
field degree. -/
theorem card_cyclotomicLayer_galois_eq_finrank :
    Nat.card (cyclotomicLayer (K := Padic p) p m ≃ₐ[Padic p] cyclotomicLayer (K := Padic p) p m) =
      Module.finrank (Padic p) (cyclotomicLayer (K := Padic p) p m) :=
  IsGalois.card_aut_eq_finrank (Padic p) (cyclotomicLayer (K := Padic p) p m)

/-- The cardinality is the prime-power totient, including the zeroth level. -/
theorem card_cyclotomicLayer_galois :
    Nat.card (cyclotomicLayer (K := Padic p) p m ≃ₐ[Padic p] cyclotomicLayer (K := Padic p) p m) =
      (p ^ m).totient := by
  rw [card_cyclotomicLayer_galois_eq_finrank, finrank_cyclotomicLayer_padic]

/-- The actual finite target unit group has the same cardinality. -/
theorem card_cyclotomicLayer_character_units : Nat.card (ZMod (p ^ m))ˣ = (p ^ m).totient := by
  rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient]

/-- Injection and the independently computed equal finite cardinalities
make the actual finite cyclotomic character bijective. -/
theorem cyclotomicLayerCharacter_bijective : Function.Bijective (cyclotomicLayerCharacter p m) := by
  let := Fintype.ofFinite
    (cyclotomicLayer (K := Padic p) p m ≃ₐ[Padic p] cyclotomicLayer (K := Padic p) p m)
  apply (Fintype.bijective_iff_injective_and_card _).mpr
  refine ⟨cyclotomicLayerCharacter_injective p m, ?_⟩
  rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card,
    card_cyclotomicLayer_galois, card_cyclotomicLayer_character_units]

theorem cyclotomicLayerCharacter_surjective : Function.Surjective (cyclotomicLayerCharacter p m) :=
  (cyclotomicLayerCharacter_bijective p m).2

/-- The isomorphism is the actual character on the actual cyclotomic Galois
group, rather than an identification through an auxiliary splitting field. -/
def cyclotomicLayerGaloisEquivUnits :
    (cyclotomicLayer (K := Padic p) p m ≃ₐ[Padic p] cyclotomicLayer (K := Padic p) p m) ≃*
      (ZMod (p ^ m))ˣ :=
  MulEquiv.ofBijective (cyclotomicLayerCharacter p m) (cyclotomicLayerCharacter_bijective p m)

@[simp]
theorem cyclotomicLayerGaloisEquivUnits_apply
    (g : cyclotomicLayer (K := Padic p) p m ≃ₐ[Padic p] cyclotomicLayer (K := Padic p) p m) :
    cyclotomicLayerGaloisEquivUnits p m g = cyclotomicLayerCharacter p m g := rfl

/-- The forward isomorphism evaluates by the action on the original root. -/
theorem cyclotomicLayerGaloisEquivUnits_spec
    (g : cyclotomicLayer (K := Padic p) p m ≃ₐ[Padic p] cyclotomicLayer (K := Padic p) p m) :
    g (cyclotomicLayerRoot p m) = cyclotomicLayerRoot p m ^
      (cyclotomicLayerGaloisEquivUnits p m g : ZMod (p ^ m)).val :=
  cyclotomicLayerCharacter_spec p m g

/-- Every unit is realized by the automorphism obtained from this actual
isomorphism, with its specified action on the chosen primitive root. -/
theorem cyclotomicLayerGaloisEquivUnits_symm_spec (u : (ZMod (p ^ m))ˣ) :
    (cyclotomicLayerGaloisEquivUnits p m).symm u (cyclotomicLayerRoot p m) =
      cyclotomicLayerRoot p m ^ (u : ZMod (p ^ m)).val := by
  have h := cyclotomicLayerCharacter_spec p m ((cyclotomicLayerGaloisEquivUnits p m).symm u)
  change (cyclotomicLayerGaloisEquivUnits p m).symm u (cyclotomicLayerRoot p m) =
    cyclotomicLayerRoot p m ^
      (cyclotomicLayerGaloisEquivUnits p m ((cyclotomicLayerGaloisEquivUnits p m).symm u) :
        ZMod (p ^ m)).val at h
  simpa only [MulEquiv.apply_symm_apply] using h

end FalseTateExtension

end
