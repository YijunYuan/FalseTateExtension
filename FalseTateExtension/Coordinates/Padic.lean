/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FalseTateExtension.Coordinates.Transitions
public import Mathlib.NumberTheory.Cyclotomic.CyclotomicCharacter

/-!
# Actual p-adic cyclotomic and Kummer coordinates

The infinite false Tate extension contains the chosen primitive roots of unity
at every p-power order. Its usual cyclotomic character and a p-adic Kummer
coordinate recover the previously constructed finite coordinates. The Kummer
coordinate satisfies the cocycle identity, and the two coordinates determine
the automorphism.

This proves blueprint `ft:padic-coordinates`, the compatible-coordinate
construction in Liu, Section 5.1. No topology or semidirect-product assertion
is made here.
-/

@[expose] public section

namespace FalseTateExtension

noncomputable section

variable {K : Type*} [Field K] [CharZero K] (p : ℕ) [Fact p.Prime] (π : K)

/-- Galois restriction from `K_FT` to the diagonal layer `n`. -/
def infiniteLayerRestriction [hπ : NeZero π] (n : ℕ) :
    (falseTateExtension p π ≃ₐ[K] falseTateExtension p π) →*
      (falseTateLayer p π n n ≃ₐ[K] falseTateLayer p π n n) :=
  haveI := falseTateLayer_isGalois p π n
  IntermediateField.restrictNormalHomOfLE (falseTateLayer_le_falseTateExtension p π n n)

/-- Restriction commutes with the inclusion of the layer into `K_FT`. -/
theorem infiniteLayerRestriction_commutes [hπ : NeZero π] (n : ℕ)
    (g : falseTateExtension p π ≃ₐ[K] falseTateExtension p π)
    (x : falseTateLayer p π n n) :
    IntermediateField.inclusion (falseTateLayer_le_falseTateExtension p π n n)
        (infiniteLayerRestriction p π n g x) =
      g (IntermediateField.inclusion (falseTateLayer_le_falseTateExtension p π n n) x) :=
  haveI := falseTateLayer_isGalois p π n
  IntermediateField.restrictNormalHomOfLE_commutes _ g x

/-- Every automorphism of a diagonal layer extends to `K_FT`. -/
theorem infiniteLayerRestriction_surjective [hπ : NeZero π] (n : ℕ) :
    Function.Surjective (infiniteLayerRestriction p π n) :=
  haveI := falseTateLayer_isGalois p π n
  haveI := falseTateExtension_isGalois p π
  IntermediateField.restrictNormalHomOfLE_surjective _

/-- Restriction to `K_FT` factors through restriction between layers. -/
theorem infiniteLayerRestriction_comp [hπ : NeZero π] {n m : ℕ} (h : n ≤ m) :
    (finiteLayerRestriction p π h).comp (infiniteLayerRestriction p π m) =
      infiniteLayerRestriction p π n :=
  haveI := falseTateLayer_isGalois p π n
  haveI := falseTateLayer_isGalois p π m
  IntermediateField.restrictNormalHomOfLE_comp _ _

/-- All finite restrictions together determine an automorphism, since their
actual diagonal fields exhaust the infinite field. -/
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

/-- The chosen primitive root of unity viewed in the actual infinite field. -/
def extensionRootOfUnity (n : ℕ) : falseTateExtension p π :=
  IntermediateField.inclusion (falseTateLayer_le_falseTateExtension p π n n)
    (layerRootOfUnity p π n)

@[simp]
theorem coe_extensionRootOfUnity (n : ℕ) :
    (extensionRootOfUnity p π n : AlgebraicClosure K) = rootOfUnity p n := rfl

theorem isPrimitiveRoot_extensionRootOfUnity (n : ℕ) :
    IsPrimitiveRoot (extensionRootOfUnity p π n) (p ^ n) :=
  (isPrimitiveRoot_layerRootOfUnity p π n).map_of_injective
    (f := IntermediateField.inclusion (falseTateLayer_le_falseTateExtension p π n n))
    (IntermediateField.inclusion (falseTateLayer_le_falseTateExtension p π n n)).injective

/-- The infinite false Tate field actually contains enough roots at every
p-power order, ruling out the cyclotomic character's missing-roots branch. -/
instance falseTateExtension_hasEnoughRootsOfUnity (n : ℕ) :
    HasEnoughRootsOfUnity (falseTateExtension p π) (p ^ n) :=
  ⟨⟨extensionRootOfUnity p π n, isPrimitiveRoot_extensionRootOfUnity p π n⟩,
    rootsOfUnity.isCyclic _ _⟩

/-- The usual Mathlib cyclotomic character of the actual infinite field,
restricted to its K-algebra automorphisms. -/
def padicCyclotomicCharacter :
    (falseTateExtension p π ≃ₐ[K] falseTateExtension p π) →* (ℤ_[p])ˣ :=
  (_root_.cyclotomicCharacter (falseTateExtension p π) p).comp
    (MulSemiringAction.toRingAut
      (falseTateExtension p π ≃ₐ[K] falseTateExtension p π) (falseTateExtension p π))

/-- Every finite projection of the usual cyclotomic character is the actual
finite cyclotomic coordinate of the corresponding restriction. -/
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
  exact _root_.cyclotomicCharacter.spec p g.toRingEquiv (extensionRootOfUnity p π n)
    (isPrimitiveRoot_extensionRootOfUnity p π n).pow_eq_one

/-- The canonical nonnegative integer representative of a finite Kummer
coordinate of an infinite-field automorphism. -/
def kummerRepresentative [hπ : NeZero π]
    (g : falseTateExtension p π ≃ₐ[K] falseTateExtension p π) (n : ℕ) : ℤ :=
  (finiteKummerExponent p π n (infiniteLayerRestriction p π n g)).val

/-- Successive integer representatives differ by a multiple of p^n, as a
consequence of actual finite restriction compatibility. -/
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

/-- The p-adic Kummer coordinate is the actual limit of the compatible integer
representatives supplied by the finite coordinates. -/
def padicKummerExponent [hπ : NeZero π]
    (g : falseTateExtension p π ≃ₐ[K] falseTateExtension p π) : ℤ_[p] :=
  PadicInt.ofIntSeq (kummerRepresentative p π g)
    (PadicInt.isCauSeq_padicNorm_of_pow_dvd_sub (kummerRepresentative p π g) p
      (kummerRepresentative_step p π g))

/-- Every finite projection of the p-adic Kummer coordinate is the prescribed
Kummer coordinate on the actual finite restriction. -/
theorem padicKummerExponent_toZModPow [hπ : NeZero π]
    (g : falseTateExtension p π ≃ₐ[K] falseTateExtension p π) (n : ℕ) :
    PadicInt.toZModPow n (padicKummerExponent p π g) =
      finiteKummerExponent p π n (infiniteLayerRestriction p π n g) := by
  have : NeZero (p ^ n) := ⟨pow_ne_zero n (Fact.out : p.Prime).ne_zero⟩
  rw [padicKummerExponent, PadicInt.toZModPow_ofIntSeq_of_pow_dvd_sub
    (kummerRepresentative p π g) p (kummerRepresentative_step p π g) n]
  simp only [kummerRepresentative, Int.cast_natCast, ZMod.natCast_zmod_val]

/-- The finite projection formulas uniquely determine the p-adic Kummer
coordinate, hence make it independent of integer representative choices. -/
theorem padicKummerExponent_unique [hπ : NeZero π]
    (g : falseTateExtension p π ≃ₐ[K] falseTateExtension p π) (a : ℤ_[p])
    (ha : ∀ n, PadicInt.toZModPow n a =
      finiteKummerExponent p π n (infiniteLayerRestriction p π n g)) :
    padicKummerExponent p π g = a := by
  apply PadicInt.ext_of_toZModPow.mp
  intro n
  rw [padicKummerExponent_toZModPow, ha n]

/-- The finite cocycles pass to the actual p-adic coordinates through their
proved projections. -/
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

/-- The actual p-adic Kummer and cyclotomic coordinates determine every
automorphism of the infinite false Tate field. -/
theorem padicCoordinates_injective [hπ : NeZero π] :
    Function.Injective (fun g : falseTateExtension p π ≃ₐ[K] falseTateExtension p π ↦
      (padicKummerExponent p π g, padicCyclotomicCharacter p π g)) := by
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
