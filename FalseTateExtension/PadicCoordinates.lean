module

public import FalseTateExtension.CoordinateTransitions
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

/-- Ordinary Galois restriction from the actual infinite false Tate field to
its nth diagonal finite layer. -/
def infiniteLayerRestriction (hπ : π ≠ 0) (n : ℕ) :
    (falseTateExtension p π ≃ₐ[K] falseTateExtension p π) →*
      (falseTateLayer p π n n ≃ₐ[K] falseTateLayer p π n n) := by
  have := falseTateLayer_isGalois p π hπ n
  let : Algebra (falseTateLayer p π n n) (falseTateExtension p π) :=
    RingHom.toAlgebra (Subsemiring.inclusion (falseTateLayer_le_falseTateExtension p π n n))
  let : IsScalarTower K (falseTateLayer p π n n) (falseTateExtension p π) :=
    IsScalarTower.of_algebraMap_eq (congrFun rfl)
  exact AlgEquiv.restrictNormalHom (falseTateLayer p π n n)

/-- Infinite Galois restriction agrees with evaluation under the original
inclusion of the finite layer. -/
theorem infiniteLayerRestriction_commutes (hπ : π ≠ 0) (n : ℕ)
    (g : falseTateExtension p π ≃ₐ[K] falseTateExtension p π)
    (x : falseTateLayer p π n n) :
    IntermediateField.inclusion (falseTateLayer_le_falseTateExtension p π n n)
        (infiniteLayerRestriction p π hπ n g x) =
      g (IntermediateField.inclusion (falseTateLayer_le_falseTateExtension p π n n) x) := by
  have := falseTateLayer_isGalois p π hπ n
  let : Algebra (falseTateLayer p π n n) (falseTateExtension p π) :=
    RingHom.toAlgebra (Subsemiring.inclusion (falseTateLayer_le_falseTateExtension p π n n))
  let : IsScalarTower K (falseTateLayer p π n n) (falseTateExtension p π) :=
    IsScalarTower.of_algebraMap_eq (congrFun rfl)
  exact AlgEquiv.restrictNormal_commutes g (falseTateLayer p π n n) x

/-- Every finite-layer automorphism extends to the actual infinite Galois field. -/
theorem infiniteLayerRestriction_surjective (hπ : π ≠ 0) (n : ℕ) :
    Function.Surjective (infiniteLayerRestriction p π hπ n) := by
  have := falseTateLayer_isGalois p π hπ n
  have := falseTateExtension_isGalois p π hπ
  let : Algebra (falseTateLayer p π n n) (falseTateExtension p π) :=
    RingHom.toAlgebra (Subsemiring.inclusion (falseTateLayer_le_falseTateExtension p π n n))
  let : IsScalarTower K (falseTateLayer p π n n) (falseTateExtension p π) :=
    IsScalarTower.of_algebraMap_eq (congrFun rfl)
  exact AlgEquiv.restrictNormalHom_surjective (falseTateExtension p π)

/-- The actual infinite restriction maps commute with finite transition maps. -/
theorem infiniteLayerRestriction_comp (hπ : π ≠ 0) {n m : ℕ} (h : n ≤ m) :
    (finiteLayerRestriction p π hπ h).comp (infiniteLayerRestriction p π hπ m) =
      infiniteLayerRestriction p π hπ n := by
  apply MonoidHom.ext
  intro g
  apply AlgEquiv.ext
  intro x
  apply (IntermediateField.inclusion (falseTateLayer_le_falseTateExtension p π n n)).injective
  calc
    _ = IntermediateField.inclusion (falseTateLayer_le_falseTateExtension p π m m)
        (IntermediateField.inclusion (falseTateLayer_mono p π h h)
          (finiteLayerRestriction p π hπ h (infiniteLayerRestriction p π hπ m g) x)) := rfl
    _ = IntermediateField.inclusion (falseTateLayer_le_falseTateExtension p π m m)
        (infiniteLayerRestriction p π hπ m g
          (IntermediateField.inclusion (falseTateLayer_mono p π h h) x)) := by
      rw [finiteLayerRestriction_commutes p π hπ h]
    _ = g (IntermediateField.inclusion (falseTateLayer_le_falseTateExtension p π m m)
        (IntermediateField.inclusion (falseTateLayer_mono p π h h) x)) :=
      infiniteLayerRestriction_commutes p π hπ m g _
    _ = _ := (infiniteLayerRestriction_commutes p π hπ n g x).symm

/-- All finite restrictions together determine an automorphism, since their
actual diagonal fields exhaust the infinite field. -/
theorem infiniteLayerRestriction_jointly_injective (hπ : π ≠ 0)
    {g h : falseTateExtension p π ≃ₐ[K] falseTateExtension p π}
    (heq : ∀ n, infiniteLayerRestriction p π hπ n g = infiniteLayerRestriction p π hπ n h) :
    g = h := by
  apply AlgEquiv.ext
  intro x
  obtain ⟨n, hn⟩ := (mem_falseTateExtension_iff_diagonal p π (x : AlgebraicClosure K)).mp x.property
  let xn : falseTateLayer p π n n := ⟨x, hn⟩
  have hx : IntermediateField.inclusion (falseTateLayer_le_falseTateExtension p π n n) xn = x :=
    Subtype.ext rfl
  rw [← hx, ← infiniteLayerRestriction_commutes p π hπ n g,
    ← infiniteLayerRestriction_commutes p π hπ n h, heq n]

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
    (falseTateExtension p π ≃ₐ[K] falseTateExtension p π) →* (PadicInt p)ˣ :=
  (_root_.cyclotomicCharacter (falseTateExtension p π) p).comp
    (MulSemiringAction.toRingAut
      (falseTateExtension p π ≃ₐ[K] falseTateExtension p π) (falseTateExtension p π))

/-- Every finite projection of the usual cyclotomic character is the actual
finite cyclotomic coordinate of the corresponding restriction. -/
theorem padicCyclotomicCharacter_toZModPow (hπ : π ≠ 0) (n : ℕ)
    (g : falseTateExtension p π ≃ₐ[K] falseTateExtension p π) :
    Units.map (PadicInt.toZModPow n).toMonoidHom (padicCyclotomicCharacter p π g) =
      finiteCyclotomicCharacter p π n (infiniteLayerRestriction p π hπ n g) := by
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
def kummerRepresentative (hπ : π ≠ 0)
    (g : falseTateExtension p π ≃ₐ[K] falseTateExtension p π) (n : ℕ) : ℤ :=
  (finiteKummerExponent p π n hπ (infiniteLayerRestriction p π hπ n g)).val

/-- Successive integer representatives differ by a multiple of p^n, as a
consequence of actual finite restriction compatibility. -/
theorem kummerRepresentative_step (hπ : π ≠ 0)
    (g : falseTateExtension p π ≃ₐ[K] falseTateExtension p π) (n : ℕ) :
    (p : ℤ) ^ n ∣ kummerRepresentative p π hπ g (n + 1) - kummerRepresentative p π hπ g n := by
  have : NeZero (p ^ n) := ⟨pow_ne_zero n (Fact.out : p.Prime).ne_zero⟩
  have : NeZero (p ^ (n + 1)) := ⟨pow_ne_zero (n + 1) (Fact.out : p.Prime).ne_zero⟩
  have hr := congrArg (fun r ↦ r g) (infiniteLayerRestriction_comp p π hπ (Nat.le_succ n))
  change finiteLayerRestriction p π hπ (Nat.le_succ n)
      (infiniteLayerRestriction p π hπ (n + 1) g) = infiniteLayerRestriction p π hπ n g at hr
  have hc := finiteKummerExponent_restrict p π hπ (Nat.le_succ n)
    (infiniteLayerRestriction p π hπ (n + 1) g)
  rw [hr, ZMod.castHom_apply, ZMod.cast_eq_val] at hc
  have he : (kummerRepresentative p π hπ g n : ZMod (p ^ n)) =
      (kummerRepresentative p π hπ g (n + 1) : ZMod (p ^ n)) := by
    simpa only [kummerRepresentative, Int.cast_natCast, ZMod.natCast_zmod_val] using hc
  have hd := (ZMod.intCast_eq_intCast_iff_dvd_sub ..).mp he
  simpa only [Nat.cast_pow] using hd

/-- The p-adic Kummer coordinate is the actual limit of the compatible integer
representatives supplied by the finite coordinates. -/
def padicKummerExponent (hπ : π ≠ 0)
    (g : falseTateExtension p π ≃ₐ[K] falseTateExtension p π) : PadicInt p :=
  PadicInt.ofIntSeq (kummerRepresentative p π hπ g)
    (PadicInt.isCauSeq_padicNorm_of_pow_dvd_sub (kummerRepresentative p π hπ g) p
      (kummerRepresentative_step p π hπ g))

/-- Every finite projection of the p-adic Kummer coordinate is the prescribed
Kummer coordinate on the actual finite restriction. -/
theorem padicKummerExponent_toZModPow (hπ : π ≠ 0)
    (g : falseTateExtension p π ≃ₐ[K] falseTateExtension p π) (n : ℕ) :
    PadicInt.toZModPow n (padicKummerExponent p π hπ g) =
      finiteKummerExponent p π n hπ (infiniteLayerRestriction p π hπ n g) := by
  have : NeZero (p ^ n) := ⟨pow_ne_zero n (Fact.out : p.Prime).ne_zero⟩
  rw [padicKummerExponent, PadicInt.toZModPow_ofIntSeq_of_pow_dvd_sub
    (kummerRepresentative p π hπ g) p (kummerRepresentative_step p π hπ g) n]
  simp only [kummerRepresentative, Int.cast_natCast, ZMod.natCast_zmod_val]

/-- The finite projection formulas uniquely determine the p-adic Kummer
coordinate, hence make it independent of integer representative choices. -/
theorem padicKummerExponent_unique (hπ : π ≠ 0)
    (g : falseTateExtension p π ≃ₐ[K] falseTateExtension p π) (a : PadicInt p)
    (ha : ∀ n, PadicInt.toZModPow n a =
      finiteKummerExponent p π n hπ (infiniteLayerRestriction p π hπ n g)) :
    padicKummerExponent p π hπ g = a := by
  apply PadicInt.ext_of_toZModPow.mp
  intro n
  rw [padicKummerExponent_toZModPow, ha n]

/-- The finite cocycles pass to the actual p-adic coordinates through their
proved projections. -/
theorem padicKummerExponent_mul (hπ : π ≠ 0)
    (g h : falseTateExtension p π ≃ₐ[K] falseTateExtension p π) :
    padicKummerExponent p π hπ (g * h) = padicKummerExponent p π hπ g +
      (padicCyclotomicCharacter p π g : PadicInt p) * padicKummerExponent p π hπ h := by
  apply PadicInt.ext_of_toZModPow.mp
  intro n
  have hχ := congrArg Units.val (padicCyclotomicCharacter_toZModPow p π hπ n g)
  change PadicInt.toZModPow n (padicCyclotomicCharacter p π g : PadicInt p) =
    (finiteCyclotomicCharacter p π n (infiniteLayerRestriction p π hπ n g) : ZMod (p ^ n)) at hχ
  simp only [map_add, map_mul, padicKummerExponent_toZModPow, hχ]
  exact finiteKummerExponent_mul p π n hπ
    (infiniteLayerRestriction p π hπ n g) (infiniteLayerRestriction p π hπ n h)

/-- The actual p-adic Kummer and cyclotomic coordinates determine every
automorphism of the infinite false Tate field. -/
theorem padicCoordinates_injective (hπ : π ≠ 0) :
    Function.Injective (fun g : falseTateExtension p π ≃ₐ[K] falseTateExtension p π ↦
      (padicKummerExponent p π hπ g, padicCyclotomicCharacter p π g)) := by
  intro g h heq
  have hb := congrArg Prod.fst heq
  have hχ := congrArg Prod.snd heq
  change padicKummerExponent p π hπ g = padicKummerExponent p π hπ h at hb
  change padicCyclotomicCharacter p π g = padicCyclotomicCharacter p π h at hχ
  apply infiniteLayerRestriction_jointly_injective p π hπ
  intro n
  apply finiteCoordinates_injective p π n hπ
  apply Prod.ext
  · simpa only [padicKummerExponent_toZModPow] using congrArg (PadicInt.toZModPow n) hb
  · simpa only [padicCyclotomicCharacter_toZModPow p π hπ n] using
      congrArg (Units.map (PadicInt.toZModPow n).toMonoidHom) hχ

end

end FalseTateExtension
