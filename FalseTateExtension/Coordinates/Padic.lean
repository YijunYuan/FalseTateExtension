/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FalseTateExtension.Coordinates.Transitions
public import Mathlib.NumberTheory.Cyclotomic.CyclotomicCharacter

/-!
# The cyclotomic character and Kummer exponent of `Gal(K_FT/K)`

Let `K` be a field of characteristic zero, `p` a prime, `π ∈ K` nonzero, and
`K_FT = ⋃_n K(π^{1/p^n}, ζ_{p^n})`. Restriction to the diagonal layers gives surjective
homomorphisms `Gal(K_FT/K) → Gal(K(π^{1/p^n}, ζ_{p^n})/K)` which are jointly injective.
The finite coordinates of these restrictions are compatible, and their limits are the
cyclotomic character `χ : Gal(K_FT/K) → ℤ_p^×`, with `g(ζ_{p^n}) = ζ_{p^n}^{χ(g)}`, and the
Kummer exponent `b : Gal(K_FT/K) → ℤ_p`, with `g(π^{1/p^n}) = ζ_{p^n}^{b(g)} π^{1/p^n}` for
every `n`. The exponent satisfies the cocycle rule `b(gh) = b(g) + χ(g) b(h)`, and
`g ↦ (b(g), χ(g))` is injective.

## Main results

* `infiniteLayerRestriction`, `infiniteLayerRestriction_surjective`,
  `infiniteLayerRestriction_jointly_injective`: restriction to the diagonal layers.
* `padicCyclotomicCharacter`, `padicCyclotomicCharacter_toZModPow`: the character `χ` and its
  reductions `χ mod p^n = χ_n`.
* `padicKummerExponent`, `padicKummerExponent_toZModPow`: the exponent `b` and its reductions
  `b mod p^n = b_n`.
* `padicKummerExponent_mul`: the cocycle rule `b(gh) = b(g) + χ(g) b(h)`.
* `padicCoordinates_injective`: `g ↦ (b(g), χ(g))` is injective.

## References

* Liu, *On lattices in semi-stable representations: a proof of a conjecture of Breuil*, §5.1,
  Lemma 5.1.2.
-/

@[expose] public section

namespace FalseTateExtension

noncomputable section

variable {K : Type*} [Field K] [CharZero K] (p : ℕ) [Fact p.Prime] (π : K)

/-- Restriction `Gal(K_FT/K) → Gal(K(π^{1/p^n}, ζ_{p^n})/K)`. -/
def infiniteLayerRestriction [hπ : NeZero π] (n : ℕ) :
    (falseTateExtension p π ≃ₐ[K] falseTateExtension p π) →*
      (falseTateLayer p π n n ≃ₐ[K] falseTateLayer p π n n) :=
  haveI := falseTateLayer_isGalois p π n
  IntermediateField.restrictNormalHomOfLE (falseTateLayer_le_falseTateExtension p π n n)

/-- `g|_{L_n}(x) = g(x)` for `x` in the diagonal layer `L_n ⊆ K_FT`. -/
theorem infiniteLayerRestriction_commutes [hπ : NeZero π] (n : ℕ)
    (g : falseTateExtension p π ≃ₐ[K] falseTateExtension p π)
    (x : falseTateLayer p π n n) :
    IntermediateField.inclusion (falseTateLayer_le_falseTateExtension p π n n)
        (infiniteLayerRestriction p π n g x) =
      g (IntermediateField.inclusion (falseTateLayer_le_falseTateExtension p π n n) x) :=
  haveI := falseTateLayer_isGalois p π n
  IntermediateField.restrictNormalHomOfLE_commutes _ g x

/-- Restriction `Gal(K_FT/K) → Gal(K(π^{1/p^n}, ζ_{p^n})/K)` is surjective. -/
theorem infiniteLayerRestriction_surjective [hπ : NeZero π] (n : ℕ) :
    Function.Surjective (infiniteLayerRestriction p π n) :=
  haveI := falseTateLayer_isGalois p π n
  haveI := falseTateExtension_isGalois p π
  IntermediateField.restrictNormalHomOfLE_surjective _

/-- Restricting from `K_FT` to `L_m` and then to `L_n` is restricting from `K_FT` to `L_n`. -/
theorem infiniteLayerRestriction_comp [hπ : NeZero π] {n m : ℕ} (h : n ≤ m) :
    (finiteLayerRestriction p π h).comp (infiniteLayerRestriction p π m) =
      infiniteLayerRestriction p π n :=
  haveI := falseTateLayer_isGalois p π n
  haveI := falseTateLayer_isGalois p π m
  IntermediateField.restrictNormalHomOfLE_comp _ _

/-- Two automorphisms of `K_FT` with the same restriction to every diagonal layer are equal. -/
theorem infiniteLayerRestriction_jointly_injective [hπ : NeZero π]
    {g h : falseTateExtension p π ≃ₐ[K] falseTateExtension p π}
    (heq : ∀ n, infiniteLayerRestriction p π n g = infiniteLayerRestriction p π n h) :
    g = h := by
  apply AlgEquiv.ext
  intro x
  obtain ⟨n, hn⟩ := (mem_falseTateExtension_iff_diagonal p π (x : AlgebraicClosure K)).mp x.property
  let xn : falseTateLayer p π n n := ⟨x, hn⟩
  have hx : IntermediateField.inclusion (falseTateLayer_le_falseTateExtension p π n n) xn = x :=
    Subtype.ext rfl
  rw [← hx, ← infiniteLayerRestriction_commutes p π n g,
    ← infiniteLayerRestriction_commutes p π n h, heq n]

/-- `ζ_{p^n}` as an element of `K_FT`. -/
def zetaExt (n : ℕ) : falseTateExtension p π :=
  IntermediateField.inclusion (falseTateLayer_le_falseTateExtension p π n n)
    (zetaLayer p π n)

/-- `zetaExt p π n` is `ζ_{p^n}` in the algebraic closure. -/
@[simp]
theorem coe_zetaExt (n : ℕ) :
    (zetaExt p π n : AlgebraicClosure K) = zeta p n := rfl

/-- `ζ_{p^n}` is a primitive `p^n`-th root of unity in `K_FT`. -/
theorem isPrimitiveRoot_zetaExt (n : ℕ) :
    IsPrimitiveRoot (zetaExt p π n) (p ^ n) :=
  (isPrimitiveRoot_zetaLayer p π n).map_of_injective
    (f := IntermediateField.inclusion (falseTateLayer_le_falseTateExtension p π n n))
    (IntermediateField.inclusion (falseTateLayer_le_falseTateExtension p π n n)).injective

/-- `K_FT` contains a primitive `p^n`-th root of unity for every `n`. -/
instance falseTateExtension_hasEnoughRootsOfUnity (n : ℕ) :
    HasEnoughRootsOfUnity (falseTateExtension p π) (p ^ n) :=
  ⟨⟨zetaExt p π n, isPrimitiveRoot_zetaExt p π n⟩,
    rootsOfUnity.isCyclic _ _⟩

/-- The cyclotomic character `Gal(L/K) →* ℤ_[p]ˣ` of an intermediate field `L` of the algebraic
closure, `g(ζ) = ζ^{χ(g)}` for every `p`-power root of unity `ζ ∈ L`. -/
def intermediateFieldCyclotomicCharacter (L : IntermediateField K (AlgebraicClosure K)) :
    (L ≃ₐ[K] L) →* (ℤ_[p])ˣ :=
  (_root_.cyclotomicCharacter L p).comp (MulSemiringAction.toRingAut (L ≃ₐ[K] L) L)

omit [CharZero K] in
/-- The cyclotomic character is continuous for the Krull topology. -/
theorem continuous_intermediateFieldCyclotomicCharacter
    (L : IntermediateField K (AlgebraicClosure K)) :
    Continuous (intermediateFieldCyclotomicCharacter p L) :=
  _root_.cyclotomicCharacter.continuous p K L

/-- The cyclotomic character `χ : Gal(K_FT/K) → ℤ_p^×`, given by `g(ζ) = ζ^{χ(g)}` for every
`p`-power root of unity `ζ`. -/
abbrev padicCyclotomicCharacter :
    (falseTateExtension p π ≃ₐ[K] falseTateExtension p π) →* (ℤ_[p])ˣ :=
  intermediateFieldCyclotomicCharacter p (falseTateExtension p π)

/-- `χ(g) mod p^n = χ_n(g|_{L_n})`. -/
theorem padicCyclotomicCharacter_toZModPow [hπ : NeZero π] (n : ℕ)
    (g : falseTateExtension p π ≃ₐ[K] falseTateExtension p π) :
    Units.map (PadicInt.toZModPow n).toMonoidHom (padicCyclotomicCharacter p π g) =
      finiteCyclotomicCharacter p π n (infiniteLayerRestriction p π n g) := by
  symm
  apply finiteCyclotomicCharacter_unique p π n
  apply (show Function.Injective
    (IntermediateField.inclusion (falseTateLayer_le_falseTateExtension p π n n)) from
    (IntermediateField.inclusion (falseTateLayer_le_falseTateExtension p π n n)).injective)
  rw [infiniteLayerRestriction_commutes, map_pow]
  exact _root_.cyclotomicCharacter.spec p g.toRingEquiv (zetaExt p π n)
    (isPrimitiveRoot_zetaExt p π n).pow_eq_one

/-- The integer in `[0, p^n)` representing `b_n(g|_{L_n}) ∈ ℤ/p^n`. -/
def kummerRepresentative [hπ : NeZero π]
    (g : falseTateExtension p π ≃ₐ[K] falseTateExtension p π) (n : ℕ) : ℤ :=
  (finiteKummerExponent p π n (infiniteLayerRestriction p π n g)).val

/-- The representatives of `b_{n+1}(g|_{L_{n+1}})` and `b_n(g|_{L_n})` are congruent modulo
`p^n`. -/
theorem kummerRepresentative_step [hπ : NeZero π]
    (g : falseTateExtension p π ≃ₐ[K] falseTateExtension p π) (n : ℕ) :
    (p : ℤ) ^ n ∣ kummerRepresentative p π g (n + 1) - kummerRepresentative p π g n := by
  have : NeZero (p ^ n) := ⟨pow_ne_zero n (Fact.out : p.Prime).ne_zero⟩
  have : NeZero (p ^ (n + 1)) := ⟨pow_ne_zero (n + 1) (Fact.out : p.Prime).ne_zero⟩
  have hr := congrArg (fun r ↦ r g) (infiniteLayerRestriction_comp p π (Nat.le_succ n))
  change finiteLayerRestriction p π (Nat.le_succ n)
      (infiniteLayerRestriction p π (n + 1) g) = infiniteLayerRestriction p π n g at hr
  have hc := finiteKummerExponent_restrict p π (Nat.le_succ n)
    (infiniteLayerRestriction p π (n + 1) g)
  rw [hr, ZMod.castHom_apply, ZMod.cast_eq_val] at hc
  have he : (kummerRepresentative p π g n : ZMod (p ^ n)) =
      (kummerRepresentative p π g (n + 1) : ZMod (p ^ n)) := by
    simpa only [kummerRepresentative, Int.cast_natCast, ZMod.natCast_zmod_val] using hc
  have hd := (ZMod.intCast_eq_intCast_iff_dvd_sub ..).mp he
  simpa only [Nat.cast_pow] using hd

/-- The Kummer exponent `b : Gal(K_FT/K) → ℤ_p`, the `p`-adic limit of the exponents
`b_n(g|_{L_n})`; it satisfies `g(π^{1/p^n}) = ζ_{p^n}^{b(g)} π^{1/p^n}` for every `n`. -/
def padicKummerExponent [hπ : NeZero π]
    (g : falseTateExtension p π ≃ₐ[K] falseTateExtension p π) : ℤ_[p] :=
  PadicInt.ofIntSeq (kummerRepresentative p π g)
    (PadicInt.isCauSeq_padicNorm_of_pow_dvd_sub (kummerRepresentative p π g) p
      (kummerRepresentative_step p π g))

/-- `b(g) mod p^n = b_n(g|_{L_n})`. -/
theorem padicKummerExponent_toZModPow [hπ : NeZero π]
    (g : falseTateExtension p π ≃ₐ[K] falseTateExtension p π) (n : ℕ) :
    PadicInt.toZModPow n (padicKummerExponent p π g) =
      finiteKummerExponent p π n (infiniteLayerRestriction p π n g) := by
  have : NeZero (p ^ n) := ⟨pow_ne_zero n (Fact.out : p.Prime).ne_zero⟩
  rw [padicKummerExponent, PadicInt.toZModPow_ofIntSeq_of_pow_dvd_sub
    (kummerRepresentative p π g) p (kummerRepresentative_step p π g) n]
  simp only [kummerRepresentative, Int.cast_natCast, ZMod.natCast_zmod_val]

/-- If `a ∈ ℤ_p` satisfies `a mod p^n = b_n(g|_{L_n})` for every `n`, then `b(g) = a`. -/
theorem padicKummerExponent_unique [hπ : NeZero π]
    (g : falseTateExtension p π ≃ₐ[K] falseTateExtension p π) (a : ℤ_[p])
    (ha : ∀ n, PadicInt.toZModPow n a =
      finiteKummerExponent p π n (infiniteLayerRestriction p π n g)) :
    padicKummerExponent p π g = a := by
  apply PadicInt.ext_of_toZModPow.mp
  intro n
  rw [padicKummerExponent_toZModPow, ha n]

/-- The cocycle rule `b(gh) = b(g) + χ(g) b(h)`. -/
theorem padicKummerExponent_mul [hπ : NeZero π]
    (g h : falseTateExtension p π ≃ₐ[K] falseTateExtension p π) :
    padicKummerExponent p π (g * h) = padicKummerExponent p π g +
      (padicCyclotomicCharacter p π g : ℤ_[p]) * padicKummerExponent p π h := by
  apply PadicInt.ext_of_toZModPow.mp
  intro n
  have hχ := congrArg Units.val (padicCyclotomicCharacter_toZModPow p π n g)
  change PadicInt.toZModPow n (padicCyclotomicCharacter p π g : ℤ_[p]) =
    (finiteCyclotomicCharacter p π n (infiniteLayerRestriction p π n g) : ZMod (p ^ n)) at hχ
  simp only [map_add, map_mul, padicKummerExponent_toZModPow, hχ]
  exact finiteKummerExponent_mul p π n
    (infiniteLayerRestriction p π n g) (infiniteLayerRestriction p π n h)

/-- The coordinates `g ↦ (b(g), χ(g)) ∈ ℤ_[p] × ℤ_[p]ˣ` of `g ∈ Gal(K_FT/K)`. -/
abbrev padicCoordinates [hπ : NeZero π]
    (g : falseTateExtension p π ≃ₐ[K] falseTateExtension p π) :
    ℤ_[p] × (ℤ_[p])ˣ :=
  (padicKummerExponent p π g, padicCyclotomicCharacter p π g)

/-- `g ↦ (b(g), χ(g))` is injective on `Gal(K_FT/K)`. -/
theorem padicCoordinates_injective [hπ : NeZero π] :
    Function.Injective (padicCoordinates p π) := by
  intro g h heq
  have hb := congrArg Prod.fst heq
  have hχ := congrArg Prod.snd heq
  change padicKummerExponent p π g = padicKummerExponent p π h at hb
  change padicCyclotomicCharacter p π g = padicCyclotomicCharacter p π h at hχ
  apply infiniteLayerRestriction_jointly_injective p π
  intro n
  apply finiteCoordinates_injective p π n
  apply Prod.ext
  · simpa only [padicKummerExponent_toZModPow] using congrArg (PadicInt.toZModPow n) hb
  · simpa only [padicCyclotomicCharacter_toZModPow p π n] using
      congrArg (Units.map (PadicInt.toZModPow n).toMonoidHom) hχ

end

end FalseTateExtension
