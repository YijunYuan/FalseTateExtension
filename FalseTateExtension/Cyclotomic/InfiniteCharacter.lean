/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FalseTateExtension.Cyclotomic.FiniteCharacter
public import FalseTateExtension.Coordinates.CyclotomicImage
public import FalseTateExtension.Cyclotomic.Restriction

/-!
# The cyclotomic character of `ℚ_[p](ζ_{p^∞})/ℚ_[p]`

The cyclotomic character `χ : Gal(ℚ_[p](ζ_{p^∞})/ℚ_[p]) → ℤ_[p]ˣ`
(`cyclotomicExtensionCharacter`) reduces modulo `p^m` to the character `χ_m` of the finite layer
`ℚ_[p](ζ_{p^m})`; it is surjective, and it is an isomorphism of topological groups
`Gal(ℚ_[p](ζ_{p^∞})/ℚ_[p]) ≃ₜ* ℤ_[p]ˣ`. The extensions `ℚ_[p](ζ_{p^∞})/ℚ_[p]` and
`ℚ_[p](π^{1/p^∞}, ζ_{p^∞})/ℚ_[p]` have infinite degree.

## Main results

* `cyclotomicLayerCharacter_restrict`: `χ_m(g|_{ℚ_[p](ζ_{p^m})}) = χ(g) mod p^m`
* `cyclotomicExtensionCharacter_surjective_padic`: `χ` is surjective
* `cyclotomicExtensionGaloisEquivUnits`: `Gal(ℚ_[p](ζ_{p^∞})/ℚ_[p]) ≃ₜ* ℤ_[p]ˣ`
* `not_finiteDimensional_cyclotomicExtension_padic`: `[ℚ_[p](ζ_{p^∞}) : ℚ_[p]] = ∞`
* `not_finiteDimensional_falseTateExtension_padic`: `[ℚ_[p](π^{1/p^∞}, ζ_{p^∞}) : ℚ_[p]] = ∞`

## References

* Serre, *Local Fields*, Chapter IV, §4, Proposition 17.
* Liu, *On lattices in semi-stable representations*, §5.1.
-/

@[expose] public section

noncomputable section

namespace FalseTateExtension

variable (p : ℕ) [Fact p.Prime]

/-- For `g ∈ Gal(ℚ_[p](ζ_{p^∞})/ℚ_[p])`, the finite character `χ_m` of the restriction of `g`
to `ℚ_[p](ζ_{p^m})` is the reduction modulo `p^m` of `χ(g) ∈ ℤ_[p]ˣ`. -/
theorem cyclotomicLayerCharacter_restrict (m : ℕ)
    (g : cyclotomicExtension (K := ℚ_[p]) p ≃ₐ[ℚ_[p]] cyclotomicExtension (K := ℚ_[p]) p) :
    cyclotomicLayerCharacter p m (cyclotomicRestrictionToLayer p m g) =
      Units.map (PadicInt.toZModPow m).toMonoidHom (cyclotomicExtensionCharacter p g) := by
  apply cyclotomicLayerCharacter_unique p m
  let i := IntermediateField.inclusion (cyclotomicLayer_le_cyclotomicExtension (K := ℚ_[p]) p m)
  apply i.injective
  rw [map_pow]
  change i (cyclotomicRestrictionToLayer p m g (zetaCyc (K := ℚ_[p]) p m)) =
    zetaCycExt p m ^
      (PadicInt.toZModPow m (cyclotomicExtensionCharacter p g : ℤ_[p])).val
  rw [cyclotomicRestrictionToLayer_commutes]
  exact cyclotomicExtensionCharacter_spec p m g

/-- The set of `g ∈ Gal(ℚ_[p](ζ_{p^∞})/ℚ_[p])` with `χ(g) ≡ u (mod p^m)`. -/
def cyclotomicCharacterFiber (u : (ℤ_[p])ˣ) (m : ℕ) :
    Set (cyclotomicExtension (K := ℚ_[p]) p ≃ₐ[ℚ_[p]] cyclotomicExtension (K := ℚ_[p]) p) :=
  {g | PadicInt.toZModPow m (cyclotomicExtensionCharacter p g : ℤ_[p]) =
    PadicInt.toZModPow m (u : ℤ_[p])}

/-- The set of `g` with `χ(g) ≡ u (mod p^m)` is closed in the Krull topology. -/
theorem isClosed_cyclotomicCharacterFiber (u : (ℤ_[p])ˣ) (m : ℕ) :
    IsClosed (cyclotomicCharacterFiber p u m) := by
  have hc : Continuous (fun g ↦
      (cyclotomicLayerCharacter p m (cyclotomicRestrictionToLayer p m g) : ZMod (p ^ m))) :=
    (Units.continuous_val.comp (continuous_of_discreteTopology :
      Continuous (cyclotomicLayerCharacter (K := ℚ_[p]) p m))).comp
      (continuous_cyclotomicRestrictionToLayer p m)
  have he : (fun g ↦ (cyclotomicLayerCharacter (K := ℚ_[p]) p m
      (cyclotomicRestrictionToLayer p m g) : ZMod (p ^ m))) =
      (fun g ↦ PadicInt.toZModPow m (cyclotomicExtensionCharacter p g : ℤ_[p])) := by
    funext g
    exact congrArg Units.val (cyclotomicLayerCharacter_restrict p m g)
  rw [he] at hc
  exact isClosed_eq hc continuous_const

/-- For every `u ∈ ℤ_[p]ˣ` and every `m` there is a `g` with `χ(g) ≡ u (mod p^m)`. -/
theorem cyclotomicCharacterFiber_nonempty (u : (ℤ_[p])ˣ) (m : ℕ) :
    (cyclotomicCharacterFiber p u m).Nonempty := by
  obtain ⟨h, hh⟩ := cyclotomicLayerCharacter_surjective p m
    (Units.map (PadicInt.toZModPow m).toMonoidHom u)
  obtain ⟨g, rfl⟩ := cyclotomicRestrictionToLayer_surjective p m h
  refine ⟨g, ?_⟩
  change PadicInt.toZModPow m (cyclotomicExtensionCharacter p g : ℤ_[p]) = _
  rw [cyclotomicLayerCharacter_restrict p m g] at hh
  exact congrArg Units.val hh

/-- If `χ(g) ≡ u (mod p^{m+1})` then `χ(g) ≡ u (mod p^m)`. -/
theorem cyclotomicCharacterFiber_succ_subset (u : (ℤ_[p])ˣ) (m : ℕ) :
    cyclotomicCharacterFiber p u (m + 1) ⊆ cyclotomicCharacterFiber p u m := by
  intro g hg
  let f := ZMod.castHom (pow_dvd_pow p (Nat.le_succ m)) (ZMod (p ^ m))
  have hf (x : ℤ_[p]) : f (PadicInt.toZModPow (m + 1) x) = PadicInt.toZModPow m x :=
    congrArg (fun h : ℤ_[p] →+* ZMod (p ^ m) ↦ h x)
      (PadicInt.zmod_cast_comp_toZModPow m (m + 1) (Nat.le_succ m))
  change PadicInt.toZModPow m (cyclotomicExtensionCharacter p g : ℤ_[p]) = _
  exact (hf _).symm.trans ((congrArg f hg).trans (hf _))

/-- The cyclotomic character `χ : Gal(ℚ_[p](ζ_{p^∞})/ℚ_[p]) → ℤ_[p]ˣ` is surjective. -/
theorem cyclotomicExtensionCharacter_surjective_padic :
    Function.Surjective (cyclotomicExtensionCharacter (K := ℚ_[p]) p) := by
  intro u
  obtain ⟨g, hg⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
    (cyclotomicCharacterFiber p u) (cyclotomicCharacterFiber_succ_subset p u)
    (cyclotomicCharacterFiber_nonempty p u)
    ((isClosed_cyclotomicCharacterFiber p u 0).isCompact)
    (isClosed_cyclotomicCharacterFiber p u)
  refine ⟨g, ?_⟩
  apply Units.ext
  apply PadicInt.ext_of_toZModPow.mp
  intro m
  exact Set.mem_iInter.mp hg m

/-- The cyclotomic character is an isomorphism of topological groups
`Gal(ℚ_[p](ζ_{p^∞})/ℚ_[p]) ≃ₜ* ℤ_[p]ˣ`. -/
def cyclotomicExtensionGaloisEquivUnits :
    (cyclotomicExtension (K := ℚ_[p]) p ≃ₐ[ℚ_[p]] cyclotomicExtension (K := ℚ_[p]) p) ≃ₜ*
      (ℤ_[p])ˣ := by
  let e := MulEquiv.ofBijective (cyclotomicExtensionCharacter (K := ℚ_[p]) p)
    ⟨cyclotomicExtensionCharacter_injective p, cyclotomicExtensionCharacter_surjective_padic p⟩
  have hc : Continuous e := continuous_cyclotomicExtensionCharacter p
  have hi : Continuous e.symm :=
    (isClosedEmbedding_cyclotomicExtensionCharacter (K := ℚ_[p]) p).isEmbedding.continuous_iff.mpr
      (by
        change Continuous (fun u ↦ cyclotomicExtensionCharacter p (e.symm u))
        have he : (fun u ↦ cyclotomicExtensionCharacter p (e.symm u)) = id :=
          funext e.apply_symm_apply
        rw [he]
        exact continuous_id)
  exact
    { e with
      continuous_toFun := hc
      continuous_invFun := hi }

/-- The isomorphism `Gal(ℚ_[p](ζ_{p^∞})/ℚ_[p]) ≃ₜ* ℤ_[p]ˣ` is the cyclotomic character. -/
@[simp]
theorem cyclotomicExtensionGaloisEquivUnits_apply
    (g : cyclotomicExtension (K := ℚ_[p]) p ≃ₐ[ℚ_[p]] cyclotomicExtension (K := ℚ_[p]) p) :
    cyclotomicExtensionGaloisEquivUnits p g = cyclotomicExtensionCharacter p g := rfl

/-- The degrees `[ℚ_[p](ζ_{p^m}) : ℚ_[p]]` are unbounded. -/
theorem cyclotomicLayer_padic_degrees_unbounded (N : ℕ) :
    ∃ m, N < Module.finrank (ℚ_[p]) (cyclotomicLayer (K := ℚ_[p]) p m) := by
  refine ⟨N + 1, ?_⟩
  rw [finrank_cyclotomicLayer_padic, Nat.totient_prime_pow_succ (Fact.out : p.Prime)]
  exact (show N < p ^ N from Nat.lt_pow_self (Fact.out : p.Prime).one_lt).trans_le
    (Nat.le_mul_of_pos_right _ (by have := (Fact.out : p.Prime).two_le; omega))

/-- `ℚ_[p](ζ_{p^∞})/ℚ_[p]` is an infinite extension. -/
theorem not_finiteDimensional_cyclotomicExtension_padic :
    ¬FiniteDimensional (ℚ_[p]) (cyclotomicExtension (K := ℚ_[p]) p) := by
  intro h
  let := h
  obtain ⟨m, hm⟩ := cyclotomicLayer_padic_degrees_unbounded p
    (Module.finrank (ℚ_[p]) (cyclotomicExtension (K := ℚ_[p]) p))
  exact (not_lt_of_ge (IntermediateField.finrank_le_of_le_right
    (cyclotomicLayer_le_cyclotomicExtension p m))) hm

/-- `ℚ_[p](π^{1/p^∞}, ζ_{p^∞})/ℚ_[p]` is an infinite extension. -/
theorem not_finiteDimensional_falseTateExtension_padic (π : ℚ_[p]) :
    ¬ Module.Finite (ℚ_[p]) (falseTateExtension p π) := by
  intro h
  let := h
  obtain ⟨m, hm⟩ := cyclotomicLayer_padic_degrees_unbounded p
    (Module.finrank (ℚ_[p]) (falseTateExtension p π))
  exact (not_lt_of_ge (IntermediateField.finrank_le_of_le_right
    ((show cyclotomicLayer p m ≤ falseTateLayer p π m m from le_sup_right).trans
      (falseTateLayer_le_falseTateExtension p π m m)))) hm

end FalseTateExtension
