/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import Mathlib.NumberTheory.Cyclotomic.CyclotomicCharacter

/-!
# Naturality of the `p`-adic cyclotomic character

If `i : E →+* E'` intertwines automorphisms `g` of `E` and `g'` of `E'`, then `g` and `g'` have the
same `p`-adic cyclotomic character.

Upstream candidate: `Mathlib.NumberTheory.Cyclotomic.CyclotomicCharacter`.
-/

@[expose] public section

/-- The cyclotomic character is natural for field embeddings intertwining automorphisms. -/
theorem cyclotomicCharacter_eq_of_intertwines (p : ℕ) [Fact p.Prime]
    {E E' : Type*} [Field E] [Field E']
    [∀ n, HasEnoughRootsOfUnity E (p ^ n)] [∀ n, HasEnoughRootsOfUnity E' (p ^ n)]
    (i : E →+* E') (g : E ≃+* E) (g' : E' ≃+* E')
    (hi : ∀ x, i (g x) = g' (i x)) :
    cyclotomicCharacter E p g = cyclotomicCharacter E' p g' := by
  apply Units.ext
  apply PadicInt.ext_of_toZModPow.mp
  intro n
  have : NeZero (p ^ n) := ⟨pow_ne_zero n (Fact.out : p.Prime).ne_zero⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_isPrimitiveRoot E (p ^ n)
  have hζ' := hζ.map_of_injective i.injective
  apply ZMod.val_injective
  apply hζ'.pow_inj (ZMod.val_lt _) (ZMod.val_lt _)
  calc
    _ = i (ζ ^ (PadicInt.toZModPow n (cyclotomicCharacter E p g : ℤ_[p])).val) :=
      (map_pow i _ _).symm
    _ = i (g ζ) := congrArg i (cyclotomicCharacter.spec p g ζ hζ.pow_eq_one).symm
    _ = g' (i ζ) := hi ζ
    _ = _ := cyclotomicCharacter.spec p g' (i ζ) hζ'.pow_eq_one
