/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FalseTateExtension.GaloisStructure
public import FalseTateExtension.Padic.InfiniteCharacter
public import FalseTateExtension.Padic.CyclotomicUpper
public import FontaineWintenberger.Ramification.Lower.Inertia
public import FontaineWintenberger.Ramification.Different.Subextension
public import FontaineWintenberger.Ramification.Upper.ResidueEquiv
public import FontaineWintenberger.APF.Tower.Residue
public import FontaineWintenberger.APF.Tower.TotallyRamified
public import FontaineWintenberger.Ramification.Lower.FiniteResidue
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.Data.ZMod.Units

/-!
# Actual finite affine Galois groups and odd rational total ramification

Finite restriction of the normalized infinite coordinates identifies each
original diagonal field with its full translation group and actual finite
cyclotomic image. Over the rational p-adic base that image is the full unit
group. The actual residue action and affine commutators then prove total
ramification at every odd prime.
-/

@[expose] public section

noncomputable section

namespace FalseTateExtension

open FontaineWintenberger

section FiniteCyclotomicImage

variable {K : Type*} [Field K] [CharZero K] (p : ℕ) [Fact p.Prime] (n : ℕ)

/-- The original chosen primitive root in its finite cyclotomic field over
an arbitrary characteristic-zero base. -/
def cyclotomicLayerRootOver : cyclotomicLayer (K := K) p n :=
  ⟨rootOfUnity p n, rootOfUnity_mem_cyclotomicLayer p n⟩

theorem isPrimitiveRoot_cyclotomicLayerRootOver :
    IsPrimitiveRoot (cyclotomicLayerRootOver (K := K) p n) (p ^ n) :=
  (isPrimitiveRoot_rootOfUnity (K := K) p n).of_map_of_injective
    (f := (cyclotomicLayer (K := K) p n).val) (cyclotomicLayer p n).val.injective

/-- The finite cyclotomic character on the original cyclotomic field over
an arbitrary characteristic-zero base. -/
def cyclotomicLayerCharacterOver :
    (cyclotomicLayer (K := K) p n ≃ₐ[K] cyclotomicLayer (K := K) p n) →*
      (ZMod (p ^ n))ˣ := by
  have : NeZero (p ^ n) := ⟨pow_ne_zero n (Fact.out : p.Prime).ne_zero⟩
  exact (isPrimitiveRoot_cyclotomicLayerRootOver (K := K) p n).autToPow K

theorem cyclotomicLayerCharacterOver_spec
    (g : cyclotomicLayer (K := K) p n ≃ₐ[K] cyclotomicLayer (K := K) p n) :
    g (cyclotomicLayerRootOver p n) = cyclotomicLayerRootOver p n ^
      (cyclotomicLayerCharacterOver p n g : ZMod (p ^ n)).val := by
  have : NeZero (p ^ n) := ⟨pow_ne_zero n (Fact.out : p.Prime).ne_zero⟩
  exact ((isPrimitiveRoot_cyclotomicLayerRootOver (K := K) p n).autToPow_spec K g).symm

theorem cyclotomicLayerCharacterOver_unique
    (g : cyclotomicLayer (K := K) p n ≃ₐ[K] cyclotomicLayer (K := K) p n)
    (u : (ZMod (p ^ n))ˣ)
    (hu : g (cyclotomicLayerRootOver p n) = cyclotomicLayerRootOver p n ^ (u : ZMod (p ^ n)).val) :
    cyclotomicLayerCharacterOver p n g = u := by
  have : NeZero (p ^ n) := ⟨pow_ne_zero n (Fact.out : p.Prime).ne_zero⟩
  apply Units.ext
  apply ZMod.val_injective
  exact (isPrimitiveRoot_cyclotomicLayerRootOver (K := K) p n).pow_inj
    (ZMod.val_lt _) (ZMod.val_lt _) ((cyclotomicLayerCharacterOver_spec p n g).symm.trans hu)

theorem cyclotomicLayerCharacterOver_injective :
    Function.Injective (cyclotomicLayerCharacterOver (K := K) p n) := by
  have : NeZero (p ^ n) := ⟨pow_ne_zero n (Fact.out : p.Prime).ne_zero⟩
  have : IsCyclotomicExtension {p ^ n} K (cyclotomicLayer (K := K) p n) :=
    (isPrimitiveRoot_rootOfUnity (K := K) p n).intermediateField_adjoin_isCyclotomicExtension K
  exact (isPrimitiveRoot_cyclotomicLayerRootOver (K := K) p n).autToPow_injective K

/-- Ordinary restriction from the original cyclotomic union to the original
finite cyclotomic field, over the same base. -/
def cyclotomicLayerRestrictionOver :
    (cyclotomicExtension (K := K) p ≃ₐ[K] cyclotomicExtension (K := K) p) →*
      (cyclotomicLayer (K := K) p n ≃ₐ[K] cyclotomicLayer (K := K) p n) :=
  IntermediateField.restrictNormalHomOfLE (cyclotomicLayer_le_cyclotomicExtension p n)

theorem cyclotomicLayerRestrictionOver_commutes
    (g : cyclotomicExtension (K := K) p ≃ₐ[K] cyclotomicExtension (K := K) p)
    (x : cyclotomicLayer (K := K) p n) :
    IntermediateField.inclusion (cyclotomicLayer_le_cyclotomicExtension p n)
      (cyclotomicLayerRestrictionOver p n g x) =
        g (IntermediateField.inclusion (cyclotomicLayer_le_cyclotomicExtension p n) x) :=
  IntermediateField.restrictNormalHomOfLE_commutes _ g x

theorem cyclotomicLayerRestrictionOver_surjective :
    Function.Surjective (cyclotomicLayerRestrictionOver (K := K) p n) :=
  IntermediateField.restrictNormalHomOfLE_surjective _

/-- Reduction of the original infinite character is precisely the original
finite character of ordinary restriction. -/
theorem cyclotomicLayerCharacterOver_restrict
    (g : cyclotomicExtension (K := K) p ≃ₐ[K] cyclotomicExtension (K := K) p) :
    cyclotomicLayerCharacterOver p n (cyclotomicLayerRestrictionOver p n g) =
      Units.map (PadicInt.toZModPow n).toMonoidHom (cyclotomicExtensionCharacter p g) := by
  apply cyclotomicLayerCharacterOver_unique p n
  let i := IntermediateField.inclusion (cyclotomicLayer_le_cyclotomicExtension (K := K) p n)
  apply (show Function.Injective i from i.injective)
  rw [map_pow, cyclotomicLayerRestrictionOver_commutes]
  exact cyclotomicExtensionCharacter_spec p n g

/-- The actual finite cyclotomic image has the original cyclotomic degree. -/
theorem card_cyclotomicLayerCharacterOver_range :
    Nat.card (cyclotomicLayerCharacterOver (K := K) p n).range =
      Module.finrank K (cyclotomicLayer (K := K) p n) := by
  let f := cyclotomicLayerCharacterOver (K := K) p n
  let e := Equiv.ofBijective f.rangeRestrict
    ⟨fun g h heq => cyclotomicLayerCharacterOver_injective p n (congrArg Subtype.val heq),
      f.rangeRestrict_surjective⟩
  exact (Nat.card_congr e.symm).trans
    (IsGalois.card_aut_eq_finrank K (cyclotomicLayer (K := K) p n))

end FiniteCyclotomicImage

section FiniteAffineCoordinates

variable {K : Type*} [Field K] [CharZero K] (p : ℕ) [Fact p.Prime] (π : K) (n : ℕ)

/-- The original finite cyclotomic inclusion, with the diagonal field kept
as its named codomain. -/
def finiteCyclotomicInclusion :
    cyclotomicLayer (K := K) p n →ₐ[K] falseTateLayer p π n n :=
  IntermediateField.inclusion le_sup_right

/-- The original finite radical inclusion in the same named diagonal field. -/
def finiteRadicalInclusion : radicalLayer p π n →ₐ[K] falseTateLayer p π n n :=
  IntermediateField.inclusion le_sup_left

/-- Ordinary restriction from the original diagonal field to its actual
finite cyclotomic subfield. -/
def diagonalCyclotomicRestriction :
    (falseTateLayer p π n n ≃ₐ[K] falseTateLayer p π n n) →*
      (cyclotomicLayer (K := K) p n ≃ₐ[K] cyclotomicLayer (K := K) p n) :=
  IntermediateField.restrictNormalHomOfLE
    (le_sup_right : cyclotomicLayer p n ≤ falseTateLayer p π n n)

theorem diagonalCyclotomicRestriction_commutes
    (g : falseTateLayer p π n n ≃ₐ[K] falseTateLayer p π n n)
    (x : cyclotomicLayer (K := K) p n) :
    finiteCyclotomicInclusion p π n (diagonalCyclotomicRestriction p π n g x) =
      g (finiteCyclotomicInclusion p π n x) :=
  IntermediateField.restrictNormalHomOfLE_commutes _ g x

/-- The diagonal character is the character on the original cyclotomic
subfield under ordinary restriction. -/
theorem cyclotomicLayerCharacterOver_diagonalRestriction
    (g : falseTateLayer p π n n ≃ₐ[K] falseTateLayer p π n n) :
    cyclotomicLayerCharacterOver p n (diagonalCyclotomicRestriction p π n g) =
      finiteCyclotomicCharacter p π n g := by
  apply cyclotomicLayerCharacterOver_unique p n
  let i := finiteCyclotomicInclusion p π n
  apply (show Function.Injective i from i.injective)
  rw [map_pow, diagonalCyclotomicRestriction_commutes]
  exact finiteCyclotomicCharacter_spec p π n g

/-- The finite affine unit coordinate belongs to the actual finite
cyclotomic character image. -/
theorem finiteCyclotomicCharacter_mem_range
    (g : falseTateLayer p π n n ≃ₐ[K] falseTateLayer p π n n) :
    finiteCyclotomicCharacter p π n g ∈ (cyclotomicLayerCharacterOver (K := K) p n).range :=
  ⟨diagonalCyclotomicRestriction p π n g,
    cyclotomicLayerCharacterOver_diagonalRestriction p π n g⟩

/-- The usual finite affine action, in multiplicative notation for the
additive coordinate of the canonical semidirect product. -/
def finiteAffineAction : (ZMod (p ^ n))ˣ →* MulAut (Multiplicative (ZMod (p ^ n))) :=
  (MulAutMultiplicative (ZMod (p ^ n))).symm.toMonoidHom.comp AddAut.mulLeft

/-- The canonical finite affine group with an actual specified unit image. -/
abbrev FiniteAffineGroup (H : Subgroup (ZMod (p ^ n))ˣ) :=
  SemidirectProduct (Multiplicative (ZMod (p ^ n))) H ((finiteAffineAction p n).comp H.subtype)

/-- The normalized finite action coordinates in the canonical affine group
with the original finite cyclotomic image. -/
def finiteAffineGaloisHom [hπ : NeZero π] :
    (falseTateLayer p π n n ≃ₐ[K] falseTateLayer p π n n) →*
      FiniteAffineGroup p n (cyclotomicLayerCharacterOver (K := K) p n).range where
  toFun g := ⟨Multiplicative.ofAdd (finiteKummerExponent p π n g),
    ⟨finiteCyclotomicCharacter p π n g, finiteCyclotomicCharacter_mem_range p π n g⟩⟩
  map_one' := by
    apply SemidirectProduct.ext
    · change Multiplicative.ofAdd (finiteKummerExponent p π n 1) = 1
      have hb : finiteKummerExponent p π n 1 = 0 :=
        finiteKummerExponent_unique p π n 1 0 (by simp)
      exact congrArg Multiplicative.ofAdd hb
    · apply Subtype.ext
      exact map_one (finiteCyclotomicCharacter p π n)
  map_mul' g h := by
    apply SemidirectProduct.ext
    · exact congrArg Multiplicative.ofAdd (finiteKummerExponent_mul p π n g h)
    · apply Subtype.ext
      exact map_mul (finiteCyclotomicCharacter p π n) g h

theorem finiteAffineGaloisHom_injective [hπ : NeZero π] :
    Function.Injective (finiteAffineGaloisHom p π n) := by
  intro g h heq
  apply finiteCoordinates_injective p π n
  exact Prod.ext (congrArg (fun x => x.left.toAdd) heq)
    (congrArg (fun x => x.right.val) heq)

/-- Cardinality of the canonical finite affine group. -/
theorem card_finiteAffineGroup (H : Subgroup (ZMod (p ^ n))ˣ) :
    Nat.card (FiniteAffineGroup p n H) = p ^ n * Nat.card H := by
  have : NeZero (p ^ n) := ⟨pow_ne_zero n (Fact.out : p.Prime).ne_zero⟩
  calc
    _ = Nat.card (Multiplicative (ZMod (p ^ n)) × H) :=
      Nat.card_congr SemidirectProduct.equivProd
    _ = Nat.card (ZMod (p ^ n)) * Nat.card H := by
      rw [Nat.card_prod, Nat.card_congr Multiplicative.toAdd]
    _ = _ := by rw [Nat.card_eq_fintype_card, ZMod.card]

/-- The actual finite cyclotomic fixer is precisely the finite character kernel. -/
theorem finiteCyclotomicInclusion_fixingSubgroup :
    (finiteCyclotomicInclusion p π n).fieldRange.fixingSubgroup =
        (finiteCyclotomicCharacter p π n).ker := by
  let i := finiteCyclotomicInclusion p π n
  ext g
  rw [MonoidHom.mem_ker]
  constructor
  · intro hg
    have hr : diagonalCyclotomicRestriction p π n g = 1 := by
      apply AlgEquiv.ext
      intro x
      apply (show Function.Injective i from i.injective)
      change i (diagonalCyclotomicRestriction p π n g x) = i x
      rw [diagonalCyclotomicRestriction_commutes]
      exact (IntermediateField.mem_fixingSubgroup_iff i.fieldRange g).mp hg (i x) ⟨x, rfl⟩
    rw [← cyclotomicLayerCharacterOver_diagonalRestriction, hr, map_one]
  · intro hg
    have hr : diagonalCyclotomicRestriction p π n g = 1 := by
      apply cyclotomicLayerCharacterOver_injective p n
      rw [cyclotomicLayerCharacterOver_diagonalRestriction, hg, map_one]
    rw [IntermediateField.mem_fixingSubgroup_iff]
    rintro x ⟨y, rfl⟩
    have h := diagonalCyclotomicRestriction_commutes p π n g y
    rw [hr] at h
    exact h.symm

/-- The actual finite pure-radical fixer is precisely the zero Kummer coordinate. -/
theorem mem_finiteRadicalInclusion_fixingSubgroup_iff [hπ : NeZero π]
    (g : falseTateLayer p π n n ≃ₐ[K] falseTateLayer p π n n) :
    g ∈ (finiteRadicalInclusion p π n).fieldRange.fixingSubgroup ↔
        finiteKummerExponent p π n g = 0 := by
  let i := finiteRadicalInclusion p π n
  constructor
  · intro hg
    apply finiteKummerExponent_unique p π n g 0
    simp only [ZMod.val_zero, pow_zero, one_mul]
    exact (IntermediateField.mem_fixingSubgroup_iff i.fieldRange g).mp hg _
      ⟨⟨radical p π n, radical_mem_radicalLayer p π n⟩, rfl⟩
  · intro hb
    rw [IntermediateField.mem_fixingSubgroup_iff]
    have heq : g.toAlgHom.comp i = i := by
      apply IntermediateField.adjoin_algHom_ext
      intro z hz
      obtain rfl := Set.mem_singleton_iff.mp hz
      change g (layerRadical p π n) = layerRadical p π n
      have h := finiteKummerExponent_spec p π n g
      simpa only [hb, ZMod.val_zero, pow_zero, one_mul] using h
    rintro x ⟨y, rfl⟩
    exact AlgHom.congr_fun heq y

/-- The canonical finite affine group with the full unit group. -/
abbrev FullFiniteAffineGroup :=
  SemidirectProduct (Multiplicative (ZMod (p ^ n))) (ZMod (p ^ n))ˣ (finiteAffineAction p n)

/-- The canonical inclusion from an actual unit-image affine group into the
full finite affine group. -/
def finiteAffineInclusion (H : Subgroup (ZMod (p ^ n))ˣ) :
    FiniteAffineGroup p n H →* FullFiniteAffineGroup p n :=
  SemidirectProduct.map (MonoidHom.id _) H.subtype (fun _ => rfl)

omit [Fact p.Prime] in
theorem finiteAffineInclusion_injective (H : Subgroup (ZMod (p ^ n))ˣ) :
    Function.Injective (finiteAffineInclusion p n H) := by
  intro g h heq
  apply SemidirectProduct.ext
  · exact congrArg (fun x : FullFiniteAffineGroup p n => x.left) heq
  · apply Subtype.ext
    exact congrArg (fun x : FullFiniteAffineGroup p n => x.right) heq

open scoped commutatorElement in
omit [Fact p.Prime] in
/-- The normalized affine commutator gives its actual translation coordinate. -/
theorem finiteAffine_commutator_inl (g : FullFiniteAffineGroup p n) (b : ZMod (p ^ n)) :
    ⁅g, (SemidirectProduct.inl (Multiplicative.ofAdd b) : FullFiniteAffineGroup p n)⁆ =
      SemidirectProduct.inl (Multiplicative.ofAdd (((g.right : ZMod (p ^ n)) - 1) * b)) := by
  apply SemidirectProduct.ext
  · simp only [commutatorElement_def, SemidirectProduct.mul_left,
      SemidirectProduct.mul_right, SemidirectProduct.inv_left, SemidirectProduct.inv_right,
      SemidirectProduct.left_inl, SemidirectProduct.right_inl, mul_one, mul_inv_cancel,
      inv_one, map_one, MulAut.one_apply]
    apply congrArg Multiplicative.ofAdd
    change g.left.toAdd + (g.right : ZMod (p ^ n)) * b +
      (g.right : ZMod (p ^ n)) * ((g.right⁻¹ : (ZMod (p ^ n))ˣ) * -g.left.toAdd) + -b = _
    have hu := congrArg (fun u : (ZMod (p ^ n))ˣ => (u : ZMod (p ^ n))) (mul_inv_cancel g.right)
    change (g.right : ZMod (p ^ n)) * (g.right⁻¹ : (ZMod (p ^ n))ˣ) = 1 at hu
    rw [← mul_assoc, hu, one_mul]
    ring
  · simp [commutatorElement_def]

end FiniteAffineCoordinates

section FiniteAffineSurjectivity

variable {K : Type*} [NontriviallyNormedField K] [IsCompleteDiscreteValuedField K] [CharZero K]
variable (p : ℕ) [Fact p.Prime] [Algebra (ℚ_[p]) K]
variable (π : 𝒪[K])

/-- Every finite translation coordinate and every actual finite cyclotomic
coordinate are realized together on the original diagonal field. -/
theorem exists_finiteCoordinates_eq [hp₂ : Fact (p ≠ 2)] [hπ : Fact (Irreducible π)] (n : ℕ)
    (b : ZMod (p ^ n)) (u : (ZMod (p ^ n))ˣ)
    (hu : u ∈ (cyclotomicLayerCharacterOver (K := K) p n).range) :
    ∃ g : falseTateLayer p (π : K) n n ≃ₐ[K] falseTateLayer p (π : K) n n,
      finiteKummerExponent p (π : K) n g = b ∧
        finiteCyclotomicCharacter p (π : K) n g = u := by
  have : NeZero (p ^ n) := ⟨pow_ne_zero n (Fact.out : p.Prime).ne_zero⟩
  let hπ₀ : (π : K) ≠ 0 := fun h => hπ.out.ne_zero (Subtype.ext h)
  obtain ⟨c, hc⟩ := hu
  obtain ⟨γ, hγ⟩ := cyclotomicLayerRestrictionOver_surjective (K := K) p n c
  have hu' : Units.map (PadicInt.toZModPow n).toMonoidHom
      (cyclotomicExtensionCharacter p γ) = u :=
    (cyclotomicLayerCharacterOver_restrict p n γ).symm.trans
      ((congrArg (cyclotomicLayerCharacterOver p n) hγ).trans hc)
  obtain ⟨g, hb, hχ⟩ := exists_padicCoordinates_eq p π (b.val : ℤ_[p])
    (cyclotomicExtensionCharacter p γ) ⟨γ, rfl⟩
  refine ⟨infiniteLayerRestriction p (π : K) n g, ?_, ?_⟩
  · rw [← padicKummerExponent_toZModPow, hb]
    simp only [map_natCast, ZMod.natCast_zmod_val]
  · rw [← padicCyclotomicCharacter_toZModPow, hχ]
    exact hu'

/-- The normalized coordinate map is onto the whole finite affine group,
with no enlargement of the actual finite unit image. -/
theorem finiteAffineGaloisHom_surjective [hp₂ : Fact (p ≠ 2)] [hπ : Fact (Irreducible π)] (n : ℕ) :
    Function.Surjective
      (finiteAffineGaloisHom p (π : K) n) := by
  intro x
  obtain ⟨g, hb, hχ⟩ := exists_finiteCoordinates_eq p π n x.left.toAdd x.right.val
    x.right.property
  refine ⟨g, ?_⟩
  apply SemidirectProduct.ext
  · exact congrArg Multiplicative.ofAdd hb
  · exact Subtype.ext hχ

/-- The actual finite diagonal Galois group is the full canonical affine
semidirect product with its actual finite cyclotomic image. -/
def finiteDiagonalGaloisEquiv [hp₂ : Fact (p ≠ 2)] [hπ : Fact (Irreducible π)] (n : ℕ) :
    (falseTateLayer p (π : K) n n ≃ₐ[K] falseTateLayer p (π : K) n n) ≃*
      FiniteAffineGroup p n (cyclotomicLayerCharacterOver (K := K) p n).range :=
  MulEquiv.ofBijective
    (finiteAffineGaloisHom p (π : K) n)
    ⟨finiteAffineGaloisHom_injective p (π : K) n,
      finiteAffineGaloisHom_surjective p π n⟩

/-- Degree of the original diagonal field, retaining the actual cyclotomic degree. -/
theorem finrank_falseTateLayer_diagonal [hp₂ : Fact (p ≠ 2)] [hπ : Fact (Irreducible π)] (n : ℕ) :
    Module.finrank K (falseTateLayer p (π : K) n n) =
      p ^ n * Module.finrank K (cyclotomicLayer (K := K) p n) := by
  have := falseTateLayer_isGalois p (π : K) n
  rw [← IsGalois.card_aut_eq_finrank K (falseTateLayer p (π : K) n n),
    Nat.card_congr (finiteDiagonalGaloisEquiv p π n).toEquiv,
    card_finiteAffineGroup, card_cyclotomicLayerCharacterOver_range]

/-- The finite cyclotomic fixing subgroup is the full translation factor
in the actual diagonal affine isomorphism. -/
theorem finiteDiagonalGaloisEquiv_mem_translations [hp₂ : Fact (p ≠ 2)] [hπ : Fact (Irreducible π)]
    (n : ℕ)
    (g : falseTateLayer p (π : K) n n ≃ₐ[K] falseTateLayer p (π : K) n n) :
    finiteDiagonalGaloisEquiv p π n g ∈
      (SemidirectProduct.inl : Multiplicative (ZMod (p ^ n)) →*
        FiniteAffineGroup p n (cyclotomicLayerCharacterOver (K := K) p n).range).range ↔
      g ∈ (finiteCyclotomicInclusion p (π : K) n).fieldRange.fixingSubgroup := by
  rw [finiteCyclotomicInclusion_fixingSubgroup, SemidirectProduct.range_inl_eq_ker_rightHom,
    MonoidHom.mem_ker, MonoidHom.mem_ker]
  constructor
  · exact fun h => congrArg Subtype.val h
  · exact fun h => Subtype.ext h

/-- The finite radical fixing subgroup is the actual pure-unit factor. -/
theorem finiteDiagonalGaloisEquiv_mem_units [hp₂ : Fact (p ≠ 2)] [hπ : Fact (Irreducible π)] (n : ℕ)
    (g : falseTateLayer p (π : K) n n ≃ₐ[K] falseTateLayer p (π : K) n n) :
    finiteDiagonalGaloisEquiv p π n g ∈
      (SemidirectProduct.inr : (cyclotomicLayerCharacterOver (K := K) p n).range →*
        FiniteAffineGroup p n (cyclotomicLayerCharacterOver (K := K) p n).range).range ↔
      g ∈ (finiteRadicalInclusion p (π : K) n).fieldRange.fixingSubgroup := by
  rw [mem_finiteRadicalInclusion_fixingSubgroup_iff p (π : K) n]
  constructor
  · rintro ⟨u, hu⟩
    exact (congrArg (fun x => x.left.toAdd) hu).symm
  · intro hb
    refine ⟨(finiteDiagonalGaloisEquiv p π n g).right, ?_⟩
    apply SemidirectProduct.ext
    · exact congrArg Multiplicative.ofAdd hb.symm
    · rfl

/-- The relative scalar action uses precisely the original finite cyclotomic inclusion. -/
local instance finiteDiagonalCyclotomicAlgebra (n : ℕ) :
    Algebra (cyclotomicLayer (K := K) p n) (falseTateLayer p (π : K) n n) :=
  (finiteCyclotomicInclusion p (π : K) n).toRingHom.toAlgebra

local instance finiteDiagonalCyclotomicScalarTower (n : ℕ) :
    IsScalarTower K (cyclotomicLayer (K := K) p n) (falseTateLayer p (π : K) n n) :=
  IsScalarTower.of_algebraMap_eq (congrFun rfl)

/-- The original finite diagonal field has relative degree p^n over its
original finite cyclotomic subfield. -/
theorem finrank_falseTateLayer_over_cyclotomic [hp₂ : Fact (p ≠ 2)] [hπ : Fact (Irreducible π)]
    (n : ℕ) :
    Module.finrank (cyclotomicLayer (K := K) p n) (falseTateLayer p (π : K) n n) = p ^ n := by
  have hd := Module.finrank_mul_finrank K (cyclotomicLayer (K := K) p n)
    (falseTateLayer p (π : K) n n)
  rw [finrank_falseTateLayer_diagonal p π n] at hd
  have hpos : 0 < Module.finrank K (cyclotomicLayer (K := K) p n) := Module.finrank_pos
  nlinarith

end FiniteAffineSurjectivity

section RationalFiniteAffine

variable (p : ℕ) [Fact p.Prime]
variable (π : 𝒪[ℚ_[p]])

/-- The general finite character specializes to the existing actual rational
cyclotomic character. -/
theorem cyclotomicLayerCharacterOver_padic (n : ℕ) :
    cyclotomicLayerCharacterOver (K := ℚ_[p]) p n = cyclotomicLayerCharacter p n := rfl

/-- The original rational diagonal Galois group realizes the full finite unit
factor, in the same normalized action coordinates. -/
def finiteDiagonalGaloisEquiv_padic [hp₂ : Fact (p ≠ 2)] [hπ : Fact (Irreducible π)] (n : ℕ) :
    (falseTateLayer p (π : ℚ_[p]) n n ≃ₐ[ℚ_[p]]
      falseTateLayer p (π : ℚ_[p]) n n) ≃* FullFiniteAffineGroup p n := by
  let hπ₀ : (π : ℚ_[p]) ≠ 0 := fun h => hπ.out.ne_zero (Subtype.ext h)
  let f := (finiteAffineInclusion p n (cyclotomicLayerCharacterOver (K := ℚ_[p]) p n).range).comp
    (finiteAffineGaloisHom p (π : ℚ_[p]) n)
  apply MulEquiv.ofBijective f
  constructor
  · exact (finiteAffineInclusion_injective p n _).comp
      (finiteAffineGaloisHom_injective p (π : ℚ_[p]) n)
  · intro x
    have hu : x.right ∈ (cyclotomicLayerCharacterOver (K := ℚ_[p]) p n).range := by
      rw [cyclotomicLayerCharacterOver_padic]
      exact cyclotomicLayerCharacter_surjective p n x.right
    obtain ⟨g, hb, hχ⟩ := exists_finiteCoordinates_eq p π n x.left.toAdd x.right hu
    refine ⟨g, ?_⟩
    apply SemidirectProduct.ext
    · exact congrArg Multiplicative.ofAdd hb
    · exact hχ

/-- The actual rational affine isomorphism retains the finite Kummer coordinate. -/
theorem finiteDiagonalGaloisEquiv_padic_left [hp₂ : Fact (p ≠ 2)] [hπ : Fact (Irreducible π)]
    (n : ℕ)
    (g : falseTateLayer p (π : ℚ_[p]) n n ≃ₐ[ℚ_[p]]
      falseTateLayer p (π : ℚ_[p]) n n) :
    (finiteDiagonalGaloisEquiv_padic p π n g).left.toAdd =
      finiteKummerExponent p (π : ℚ_[p]) n g := rfl

/-- The actual rational affine isomorphism retains the finite cyclotomic character. -/
theorem finiteDiagonalGaloisEquiv_padic_right [hp₂ : Fact (p ≠ 2)] [hπ : Fact (Irreducible π)]
    (n : ℕ)
    (g : falseTateLayer p (π : ℚ_[p]) n n ≃ₐ[ℚ_[p]]
      falseTateLayer p (π : ℚ_[p]) n n) :
    (finiteDiagonalGaloisEquiv_padic p π n g).right =
      finiteCyclotomicCharacter p (π : ℚ_[p]) n g := rfl

/-- Every positive rational diagonal layer has the expected actual degree,
including the first layer. -/
theorem finrank_falseTateLayer_diagonal_padic [hp₂ : Fact (p ≠ 2)] [hπ : Fact (Irreducible π)]
    (n : ℕ) :
    Module.finrank (ℚ_[p]) (falseTateLayer p (π : ℚ_[p]) (n + 1) (n + 1)) =
      p ^ (n + 1) * (p - 1) * p ^ n := by
  rw [finrank_falseTateLayer_diagonal p π (n + 1), finrank_cyclotomicLayer_padic,
    Nat.totient_prime_pow_succ (Fact.out : p.Prime)]
  ring

/-- The original rational cyclotomic fixer is the entire translation factor. -/
theorem finiteDiagonalGaloisEquiv_padic_mem_translations
    [hp₂ : Fact (p ≠ 2)] [hπ : Fact (Irreducible π)] (n : ℕ)
    (g : falseTateLayer p (π : ℚ_[p]) n n ≃ₐ[ℚ_[p]]
      falseTateLayer p (π : ℚ_[p]) n n) :
    finiteDiagonalGaloisEquiv_padic p π n g ∈
      (SemidirectProduct.inl : Multiplicative (ZMod (p ^ n)) →* FullFiniteAffineGroup p n).range ↔
      g ∈ (finiteCyclotomicInclusion p (π : ℚ_[p]) n).fieldRange.fixingSubgroup := by
  rw [finiteCyclotomicInclusion_fixingSubgroup, SemidirectProduct.range_inl_eq_ker_rightHom,
    MonoidHom.mem_ker, MonoidHom.mem_ker]
  rfl

/-- The original rational radical fixer is the entire pure-unit factor. -/
theorem finiteDiagonalGaloisEquiv_padic_mem_units
    [hp₂ : Fact (p ≠ 2)] [hπ : Fact (Irreducible π)] (n : ℕ)
    (g : falseTateLayer p (π : ℚ_[p]) n n ≃ₐ[ℚ_[p]]
      falseTateLayer p (π : ℚ_[p]) n n) :
    finiteDiagonalGaloisEquiv_padic p π n g ∈
      (SemidirectProduct.inr : (ZMod (p ^ n))ˣ →* FullFiniteAffineGroup p n).range ↔
      g ∈ (finiteRadicalInclusion p (π : ℚ_[p]) n).fieldRange.fixingSubgroup := by
  rw [mem_finiteRadicalInclusion_fixingSubgroup_iff p (π : ℚ_[p]) n]
  constructor
  · rintro ⟨u, hu⟩
    exact (congrArg (fun x => x.left.toAdd) hu).symm
  · intro hb
    refine ⟨(finiteDiagonalGaloisEquiv_padic p π n g).right, ?_⟩
    apply SemidirectProduct.ext
    · exact congrArg Multiplicative.ofAdd hb.symm
    · rfl

end RationalFiniteAffine

section RationalTotalRamification

open FontaineWintenberger
open scoped commutatorElement

variable (p : ℕ) [Fact p.Prime]
variable (π : 𝒪[ℚ_[p]])

/-- Oddness makes the literal affine multiplier two invertible at every
finite level, including the zeroth level. -/
def finiteAffineTwo [hp₂ : Fact (p ≠ 2)] (n : ℕ) : (ZMod (p ^ n))ˣ :=
  ZMod.unitOfCoprime 2 (by
    have hp : p.Coprime 2 := (Fact.out : p.Prime).coprime_iff_not_dvd.mpr (by
      intro h
      have hle := Nat.le_of_dvd (by decide : 0 < 2) h
      exact hp₂.out (le_antisymm hle (Fact.out : p.Prime).two_le))
    exact hp.symm.pow_right n)

@[simp]
theorem coe_finiteAffineTwo [hp₂ : Fact (p ≠ 2)] (n : ℕ) :
    (finiteAffineTwo p n : ZMod (p ^ n)) = 2 := ZMod.coe_unitOfCoprime _ _

/-- Every actual translation in the original rational finite Galois group
belongs to its original inertia subgroup. -/
theorem finiteDiagonal_translation_mem_inertia
    [hp₂ : Fact (p ≠ 2)] [hπ : Fact (Irreducible π)] (n : ℕ) (b : ZMod (p ^ n)) :
    (finiteDiagonalGaloisEquiv_padic p π n).symm
        (SemidirectProduct.inl (Multiplicative.ofAdd b)) ∈
      lowerRamificationGroup
        (falseTateLayer p (π : ℚ_[p]) n n ≃ₐ[ℚ_[p]] falseTateLayer p (π : ℚ_[p]) n n)
        (IsLocalRing.maximalIdeal (spectralIntegerRing (ℚ_[p])
          (falseTateLayer p (π : ℚ_[p]) n n))) 0 := by
  have := falseTateLayer_isGalois p (π : ℚ_[p]) n
  let e := finiteDiagonalGaloisEquiv_padic p π n
  let δ := e.symm (SemidirectProduct.inr (finiteAffineTwo p n))
  let τ := e.symm (SemidirectProduct.inl (Multiplicative.ofAdd b))
  have h := commutatorElement_mem_lowerRamificationGroup_zero (ℚ_[p])
    (falseTateLayer p (π : ℚ_[p]) n n) δ τ
  have heq : ⁅δ, τ⁆ = τ := by
    apply e.injective
    rw [map_commutatorElement]
    change ⁅e (e.symm (SemidirectProduct.inr (finiteAffineTwo p n))),
      e (e.symm (SemidirectProduct.inl (Multiplicative.ofAdd b)))⁆ =
        e (e.symm (SemidirectProduct.inl (Multiplicative.ofAdd b)))
    rw [e.apply_symm_apply, e.apply_symm_apply, finiteAffine_commutator_inl]
    simp only [SemidirectProduct.right_inr, coe_finiteAffineTwo]
    rw [show (2 : ZMod (p ^ n)) - 1 = 1 by ring, one_mul]
  rwa [heq] at h

/-- The original finite cyclotomic fixing subgroup lies in the original
inertia group; no total ramification is assumed. -/
theorem finiteCyclotomicFixing_le_inertia [hp₂ : Fact (p ≠ 2)] [hπ : Fact (Irreducible π)] (n : ℕ) :
    (finiteCyclotomicInclusion p (π : ℚ_[p]) n).fieldRange.fixingSubgroup ≤
      lowerRamificationGroup
        (falseTateLayer p (π : ℚ_[p]) n n ≃ₐ[ℚ_[p]] falseTateLayer p (π : ℚ_[p]) n n)
        (IsLocalRing.maximalIdeal (spectralIntegerRing (ℚ_[p])
          (falseTateLayer p (π : ℚ_[p]) n n))) 0 := by
  intro g hg
  obtain ⟨b, hb⟩ := (finiteDiagonalGaloisEquiv_padic_mem_translations p π n g).mpr hg
  have h := finiteDiagonal_translation_mem_inertia p π n b.toAdd
  have heq : (finiteDiagonalGaloisEquiv_padic p π n).symm
      (SemidirectProduct.inl b) = g := by
    rw [hb, (finiteDiagonalGaloisEquiv_padic p π n).symm_apply_apply]
  exact heq ▸ h

/-- Every positive original rational diagonal layer has full inertia,
including the first layer, at an odd prime. -/
theorem lowerRamificationGroup_falseTateLayer_zero
    [hp₂ : Fact (p ≠ 2)] [hπ : Fact (Irreducible π)] (n : ℕ) :
    lowerRamificationGroup
      (falseTateLayer p (π : ℚ_[p]) (n + 1) (n + 1) ≃ₐ[ℚ_[p]]
        falseTateLayer p (π : ℚ_[p]) (n + 1) (n + 1))
      (IsLocalRing.maximalIdeal (spectralIntegerRing (ℚ_[p])
        (falseTateLayer p (π : ℚ_[p]) (n + 1) (n + 1)))) 0 = ⊤ := by
  let D := falseTateLayer p (π : ℚ_[p]) (n + 1) (n + 1)
  have := falseTateLayer_isGalois p (π : ℚ_[p]) (n + 1)
  let i := finiteCyclotomicInclusion p (π : ℚ_[p]) (n + 1)
  let I := lowerRamificationGroup (D ≃ₐ[ℚ_[p]] D)
    (IsLocalRing.maximalIdeal (spectralIntegerRing (ℚ_[p]) D)) 0
  have hidx := fixingSubgroup_sup_lowerRamificationGroup_zero_index_eq_residueDegree (ℚ_[p])
    D i.fieldRange
  rw [sup_eq_right.mpr (finiteCyclotomicFixing_le_inertia p π (n + 1)),
    spectral_residueDegree_algEquiv (ℚ_[p]) (cyclotomicLayer (K := ℚ_[p]) p (n + 1))
      i.equivFieldRange,
    cyclotomicLayer_spectral_residueDegree] at hidx
  exact Subgroup.index_eq_one.mp hidx

/-- The original spectral residue degree of each positive rational diagonal
layer is one at every odd prime. -/
theorem falseTateLayer_spectral_residueDegree
    [hp₂ : Fact (p ≠ 2)] [hπ : Fact (Irreducible π)] (n : ℕ) :
    Module.finrank
      (𝓀[ℚ_[p]])
      (IsLocalRing.ResidueField (spectralIntegerRing (ℚ_[p])
        (falseTateLayer p (π : ℚ_[p]) (n + 1) (n + 1)))) = 1 := by
  let D := falseTateLayer p (π : ℚ_[p]) (n + 1) (n + 1)
  have := falseTateLayer_isGalois p (π : ℚ_[p]) (n + 1)
  have h := fixingSubgroup_sup_lowerRamificationGroup_zero_index_eq_residueDegree (ℚ_[p]) D
    (⊤ : IntermediateField (ℚ_[p]) D)
  rw [lowerRamificationGroup_falseTateLayer_zero p π n, sup_top_eq, Subgroup.index_top,
    spectral_residueDegree_algEquiv (ℚ_[p]) D (IntermediateField.topEquiv :
      (⊤ : IntermediateField (ℚ_[p]) D) ≃ₐ[ℚ_[p]] D).symm] at h
  exact h.symm

/-- The original spectral ramification index equals the full field degree
for every positive rational diagonal layer at an odd prime. -/
theorem falseTateLayer_spectral_ramificationIdx
    [hp₂ : Fact (p ≠ 2)] [hπ : Fact (Irreducible π)] (n : ℕ) :
    (IsLocalRing.maximalIdeal (spectralIntegerRing (ℚ_[p])
      (falseTateLayer p (π : ℚ_[p]) (n + 1) (n + 1)))).ramificationIdx
        𝒪[ℚ_[p]] =
      Module.finrank (ℚ_[p]) (falseTateLayer p (π : ℚ_[p]) (n + 1) (n + 1)) := by
  have h := extensionValuationSubring_ramificationIdx_mul_residueDegree (ℚ_[p])
    (falseTateLayer p (π : ℚ_[p]) (n + 1) (n + 1))
    (spectralValuation (ℚ_[p]) (falseTateLayer p (π : ℚ_[p]) (n + 1) (n + 1)))
  rwa [falseTateLayer_spectral_residueDegree p π n, mul_one] at h

end RationalTotalRamification

section RationalInfiniteTotalRamification

open FontaineWintenberger

variable (p : ℕ) [Fact p.Prime]
variable (π : 𝒪[ℚ_[p]])

/-- The actual residue inclusion from a positive diagonal layer to the
original infinite false Tate field. -/
def falseTateResidueFromLayer (n : ℕ) :
    IsLocalRing.ResidueField (spectralIntegerRing (ℚ_[p])
      (falseTateLayer p (π : ℚ_[p]) (n + 1) (n + 1))) →ₐ[
        𝓀[ℚ_[p]]]
      IsLocalRing.ResidueField (spectralIntegerRing (ℚ_[p])
        (falseTateExtension p (π : ℚ_[p]))) :=
  spectralResidueInclusion (ℚ_[p]) (IntermediateField.inclusion
    (falseTateLayer_le_falseTateExtension p (π : ℚ_[p]) (n + 1) (n + 1)))

/-- Every actual infinite residue class comes from a positive original
diagonal layer, using the original field and residue inclusions. -/
theorem exists_falseTateResidueFromLayer_preimage
    (z : IsLocalRing.ResidueField (spectralIntegerRing (ℚ_[p])
      (falseTateExtension p (π : ℚ_[p])))) :
    ∃ n, ∃ x, falseTateResidueFromLayer p π n x = z := by
  obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective z
  obtain ⟨m, hm⟩ :=
    (mem_falseTateExtension_iff_diagonal p (π : ℚ_[p])
      (((x : spectralIntegerRing (ℚ_[p]) (falseTateExtension p (π : ℚ_[p]))) :
        falseTateExtension p (π : ℚ_[p])) : AlgebraicClosure (ℚ_[p]))).mp
      (x : falseTateExtension p (π : ℚ_[p])).property
  let i := IntermediateField.inclusion
    (falseTateLayer_le_falseTateExtension p (π : ℚ_[p]) (m + 1) (m + 1))
  let y : falseTateLayer p (π : ℚ_[p]) (m + 1) (m + 1) :=
    ⟨x, falseTateLayer_mono p (π : ℚ_[p]) (Nat.le_succ m) (Nat.le_succ m) hm⟩
  have hyi : i y = (x : falseTateExtension p (π : ℚ_[p])) := Subtype.ext rfl
  let : Algebra (falseTateLayer p (π : ℚ_[p]) (m + 1) (m + 1))
      (falseTateExtension p (π : ℚ_[p])) := i.toRingHom.toAlgebra
  let : IsScalarTower (ℚ_[p]) (falseTateLayer p (π : ℚ_[p]) (m + 1) (m + 1))
      (falseTateExtension p (π : ℚ_[p])) :=
    IsScalarTower.of_algebraMap_eq (fun r => (i.commutes r).symm)
  have hy : y ∈ spectralIntegerRing (ℚ_[p]) (falseTateLayer p (π : ℚ_[p]) (m + 1) (m + 1)) := by
    rw [mem_spectralIntegerRing,
      spectralNorm.eq_of_tower (L := falseTateExtension p (π : ℚ_[p])) y]
    change spectralNorm (ℚ_[p]) (falseTateExtension p (π : ℚ_[p])) (i y) ≤ 1
    rw [hyi]
    exact (mem_spectralIntegerRing (ℚ_[p]) _ _).mp x.property
  refine ⟨m, IsLocalRing.residue _ ⟨y, hy⟩, ?_⟩
  change spectralResidueInclusion (ℚ_[p]) i (IsLocalRing.residue _ ⟨y, hy⟩) = _
  rw [spectralResidueInclusion_residue]
  congr 1

/-- The actual base-residue map onto the original infinite false Tate
residue field is surjective at every odd prime. -/
theorem falseTateExtension_residue_algebraMap_surjective
    [hp₂ : Fact (p ≠ 2)] [hπ : Fact (Irreducible π)] :
    Function.Surjective (algebraMap
      (𝓀[ℚ_[p]])
      (IsLocalRing.ResidueField (spectralIntegerRing (ℚ_[p])
        (falseTateExtension p (π : ℚ_[p]))))) := by
  intro z
  obtain ⟨n, x, hx⟩ := exists_falseTateResidueFromLayer_preimage p π z
  have hsurj := (Algebra.finrank_eq_one_iff_bijective_algebraMap.mp
    (falseTateLayer_spectral_residueDegree p π n)).surjective
  obtain ⟨a, ha⟩ := hsurj x
  refine ⟨a, ?_⟩
  rw [← (falseTateResidueFromLayer p π n).commutes a, ha, hx]

/-- The original infinite false Tate field has exactly the original rational
residue field at an odd prime. -/
theorem falseTateExtension_residueDegree_padic [hp₂ : Fact (p ≠ 2)] [hπ : Fact (Irreducible π)] :
    Module.finrank
      (𝓀[ℚ_[p]])
      (IsLocalRing.ResidueField (spectralIntegerRing (ℚ_[p])
        (falseTateExtension p (π : ℚ_[p])))) = 1 := by
  apply Algebra.finrank_eq_one_iff_bijective_algebraMap.mpr
  exact ⟨(algebraMap
    (𝓀[ℚ_[p]])
    (IsLocalRing.ResidueField (spectralIntegerRing (ℚ_[p])
      (falseTateExtension p (π : ℚ_[p]))))).injective,
    falseTateExtension_residue_algebraMap_surjective p π⟩

/-- Every original finite separable subextension of the odd rational false
Tate field has residue degree one under its actual specified embedding. -/
theorem finiteSubextension_falseTate_residueDegree_padic
    [hp₂ : Fact (p ≠ 2)] [hπ : Fact (Irreducible π)]
    (E : Type*) [Field E] [Algebra (ℚ_[p]) E] [FiniteDimensional (ℚ_[p]) E]
    (i : E →ₐ[ℚ_[p]] falseTateExtension p (π : ℚ_[p])) :
    Module.finrank
      (𝓀[ℚ_[p]])
      (IsLocalRing.ResidueField (spectralIntegerRing (ℚ_[p]) E)) = 1 := by
  apply Algebra.finrank_eq_one_iff_bijective_algebraMap.mpr
  refine ⟨(algebraMap
    (𝓀[ℚ_[p]])
    (IsLocalRing.ResidueField (spectralIntegerRing (ℚ_[p]) E))).injective, ?_⟩
  intro z
  obtain ⟨a, ha⟩ := falseTateExtension_residue_algebraMap_surjective p π
    (spectralResidueInclusion (ℚ_[p]) i z)
  refine ⟨a, (spectralResidueInclusion (ℚ_[p]) i).injective ?_⟩
  exact ((spectralResidueInclusion (ℚ_[p]) i).commutes a).trans ha

/-- Every original finite subextension is totally ramified, with its own
spectral integer ring and its actual specified inclusion into the odd tower. -/
theorem finiteSubextension_falseTate_ramificationIdx_padic
    [hp₂ : Fact (p ≠ 2)] [hπ : Fact (Irreducible π)]
    (E : Type*) [Field E] [Algebra (ℚ_[p]) E] [FiniteDimensional (ℚ_[p]) E]
    (i : E →ₐ[ℚ_[p]] falseTateExtension p (π : ℚ_[p])) :
    (IsLocalRing.maximalIdeal (spectralIntegerRing (ℚ_[p]) E)).ramificationIdx
      𝒪[ℚ_[p]] = Module.finrank (ℚ_[p]) E := by
  have h := extensionValuationSubring_ramificationIdx_mul_residueDegree (ℚ_[p]) E
    (spectralValuation (ℚ_[p]) E)
  rwa [finiteSubextension_falseTate_residueDegree_padic p π E i, mul_one] at h

end RationalInfiniteTotalRamification

end FalseTateExtension
