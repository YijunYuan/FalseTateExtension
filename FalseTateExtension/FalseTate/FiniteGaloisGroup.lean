/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FalseTateExtension.Cyclotomic.Filtration
public import FalseTateExtension.Cyclotomic.InfiniteCharacter
public import FalseTateExtension.FalseTate.LiuLemma
public import FontaineWintenberger.APF.Tower.Residue
public import FontaineWintenberger.APF.Tower.TotallyRamified
public import FontaineWintenberger.Ramification.Different.Subextension
public import FontaineWintenberger.Ramification.Lower.FiniteResidue
public import FontaineWintenberger.Ramification.Lower.Inertia
public import FontaineWintenberger.Ramification.Upper.ResidueEquiv
public import Mathlib.Data.ZMod.Units
public import Mathlib.FieldTheory.Finite.Basic

/-!
# The Galois groups of the finite layers

For `p ≠ 2`, the finite coordinates identify `Gal(K(π^{1/p^n}, ζ_{p^n})/K)` with `ℤ/p^n ⋊ (image of
the cyclotomic character)`; over `K = ℚ_p` the image is all of `(ℤ/p^n)ˣ`.
-/

@[expose] public section

noncomputable section

namespace FalseTateExtension

open FontaineWintenberger

section FiniteCyclotomicImage

variable {K : Type*} [Field K] [CharZero K] (p : ℕ) [Fact p.Prime] (n : ℕ)

/-- The primitive root in its finite cyclotomic field over
an arbitrary characteristic-zero base. -/
def cyclotomicLayerRootOver : cyclotomicLayer (K := K) p n :=
  ⟨rootOfUnity p n, rootOfUnity_mem_cyclotomicLayer p n⟩

theorem isPrimitiveRoot_cyclotomicLayerRootOver :
    IsPrimitiveRoot (cyclotomicLayerRootOver (K := K) p n) (p ^ n) :=
  (isPrimitiveRoot_rootOfUnity (K := K) p n).of_map_of_injective
    (f := (cyclotomicLayer (K := K) p n).val) (cyclotomicLayer p n).val.injective

/-- The finite cyclotomic character on the cyclotomic field over
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

/-- Restriction from the cyclotomic union to the
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

/-- Reduction of the infinite character is precisely the
finite character of restriction. -/
theorem cyclotomicLayerCharacterOver_restrict
    (g : cyclotomicExtension (K := K) p ≃ₐ[K] cyclotomicExtension (K := K) p) :
    cyclotomicLayerCharacterOver p n (cyclotomicLayerRestrictionOver p n g) =
      Units.map (PadicInt.toZModPow n).toMonoidHom (cyclotomicExtensionCharacter p g) := by
  apply cyclotomicLayerCharacterOver_unique p n
  let i := IntermediateField.inclusion (cyclotomicLayer_le_cyclotomicExtension (K := K) p n)
  apply (show Function.Injective i from i.injective)
  rw [map_pow, cyclotomicLayerRestrictionOver_commutes]
  exact cyclotomicExtensionCharacter_spec p n g

/-- The finite cyclotomic image has the cyclotomic degree. -/
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

/-- The finite cyclotomic inclusion, with the diagonal field kept
as its named codomain. -/
def finiteCyclotomicInclusion :
    cyclotomicLayer (K := K) p n →ₐ[K] falseTateLayer p π n n :=
  IntermediateField.inclusion le_sup_right

/-- The finite radical inclusion in the same named diagonal field. -/
def finiteRadicalInclusion : radicalLayer p π n →ₐ[K] falseTateLayer p π n n :=
  IntermediateField.inclusion le_sup_left

/-- Restriction from the diagonal field to its
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

/-- The diagonal character is the character on the cyclotomic
subfield under restriction. -/
theorem cyclotomicLayerCharacterOver_diagonalRestriction
    (g : falseTateLayer p π n n ≃ₐ[K] falseTateLayer p π n n) :
    cyclotomicLayerCharacterOver p n (diagonalCyclotomicRestriction p π n g) =
      finiteCyclotomicCharacter p π n g := by
  apply cyclotomicLayerCharacterOver_unique p n
  let i := finiteCyclotomicInclusion p π n
  apply (show Function.Injective i from i.injective)
  rw [map_pow, diagonalCyclotomicRestriction_commutes]
  exact finiteCyclotomicCharacter_spec p π n g

/-- The finite affine unit coordinate belongs to the finite
cyclotomic character image. -/
theorem finiteCyclotomicCharacter_mem_range
    (g : falseTateLayer p π n n ≃ₐ[K] falseTateLayer p π n n) :
    finiteCyclotomicCharacter p π n g ∈ (cyclotomicLayerCharacterOver (K := K) p n).range :=
  ⟨diagonalCyclotomicRestriction p π n g,
    cyclotomicLayerCharacterOver_diagonalRestriction p π n g⟩

/-- The finite affine action, in multiplicative notation for the
additive coordinate of the semidirect product. -/
abbrev finiteAffineAction : (ZMod (p ^ n))ˣ →* MulAut (Multiplicative (ZMod (p ^ n))) :=
  affineAction (ZMod (p ^ n)) (MonoidHom.id _)

/-- The finite affine group with a specified unit image. -/
abbrev FiniteAffineGroup (H : Subgroup (ZMod (p ^ n))ˣ) : Type :=
  AffineGroup (ZMod (p ^ n)) H.subtype

/-- The normalized finite action coordinates in the affine group
with the finite cyclotomic image. -/
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

/-- Cardinality of the finite affine group. -/
theorem card_finiteAffineGroup (H : Subgroup (ZMod (p ^ n))ˣ) :
    Nat.card (FiniteAffineGroup p n H) = p ^ n * Nat.card H := by
  have : NeZero (p ^ n) := ⟨pow_ne_zero n (Fact.out : p.Prime).ne_zero⟩
  calc
    _ = Nat.card (Multiplicative (ZMod (p ^ n)) × H) :=
      Nat.card_congr SemidirectProduct.equivProd
    _ = Nat.card (ZMod (p ^ n)) * Nat.card H := by
      rw [Nat.card_prod, Nat.card_congr Multiplicative.toAdd]
    _ = _ := by rw [Nat.card_eq_fintype_card, ZMod.card]

/-- The finite cyclotomic fixer is precisely the finite character kernel. -/
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

/-- The finite pure-radical fixer is precisely the zero Kummer coordinate. -/
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

/-- The finite affine group with the full unit group. -/
abbrev FullFiniteAffineGroup : Type := AffineGroup (ZMod (p ^ n)) (MonoidHom.id _)

/-- The inclusion from a unit-image affine group into the
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
/-- The normalized affine commutator gives its translation coordinate. -/
theorem finiteAffine_commutator_inl (g : FullFiniteAffineGroup p n) (b : ZMod (p ^ n)) :
    ⁅g, (SemidirectProduct.inl (Multiplicative.ofAdd b) : FullFiniteAffineGroup p n)⁆ =
      SemidirectProduct.inl (Multiplicative.ofAdd (((g.right : ZMod (p ^ n)) - 1) * b)) :=
  AffineGroup.commutator_inl _ g b

end FiniteAffineCoordinates

section FiniteAffineSurjectivity

variable {K : Type*} [NontriviallyNormedField K] [IsCompleteDiscreteValuedField K] [CharZero K]
variable (p : ℕ) [Fact p.Prime] [Algebra (ℚ_[p]) K]
variable (π : 𝒪[K])

/-- Every finite translation coordinate and every finite cyclotomic
coordinate are realized together on the diagonal field. -/
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
with no enlargement of the finite unit image. -/
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

/-- The finite diagonal Galois group is the full affine
semidirect product with its finite cyclotomic image. -/
def finiteDiagonalGaloisEquiv [hp₂ : Fact (p ≠ 2)] [hπ : Fact (Irreducible π)] (n : ℕ) :
    (falseTateLayer p (π : K) n n ≃ₐ[K] falseTateLayer p (π : K) n n) ≃*
      FiniteAffineGroup p n (cyclotomicLayerCharacterOver (K := K) p n).range :=
  MulEquiv.ofBijective
    (finiteAffineGaloisHom p (π : K) n)
    ⟨finiteAffineGaloisHom_injective p (π : K) n,
      finiteAffineGaloisHom_surjective p π n⟩

/-- Degree of the diagonal field, retaining the cyclotomic degree. -/
theorem finrank_falseTateLayer_diagonal [hp₂ : Fact (p ≠ 2)] [hπ : Fact (Irreducible π)] (n : ℕ) :
    Module.finrank K (falseTateLayer p (π : K) n n) =
      p ^ n * Module.finrank K (cyclotomicLayer (K := K) p n) := by
  have := falseTateLayer_isGalois p (π : K) n
  rw [← IsGalois.card_aut_eq_finrank K (falseTateLayer p (π : K) n n),
    Nat.card_congr (finiteDiagonalGaloisEquiv p π n).toEquiv,
    card_finiteAffineGroup, card_cyclotomicLayerCharacterOver_range]

/-- The finite cyclotomic fixing subgroup is the full translation factor
in the diagonal affine isomorphism. -/
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

/-- The finite radical fixing subgroup is the pure-unit factor. -/
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

/-- The relative scalar action uses precisely the finite cyclotomic inclusion. -/
local instance finiteDiagonalCyclotomicAlgebra (n : ℕ) :
    Algebra (cyclotomicLayer (K := K) p n) (falseTateLayer p (π : K) n n) :=
  (finiteCyclotomicInclusion p (π : K) n).toRingHom.toAlgebra

local instance finiteDiagonalCyclotomicScalarTower (n : ℕ) :
    IsScalarTower K (cyclotomicLayer (K := K) p n) (falseTateLayer p (π : K) n n) :=
  IsScalarTower.of_algebraMap_eq (congrFun rfl)

/-- The finite diagonal field has relative degree p^n over its
finite cyclotomic subfield. -/
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

/-- The general finite character specializes to the rational
cyclotomic character. -/
theorem cyclotomicLayerCharacterOver_padic (n : ℕ) :
    cyclotomicLayerCharacterOver (K := ℚ_[p]) p n = cyclotomicLayerCharacter p n := rfl

/-- The rational diagonal Galois group realizes the full finite unit
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

/-- The rational affine isomorphism retains the finite Kummer coordinate. -/
theorem finiteDiagonalGaloisEquiv_padic_left [hp₂ : Fact (p ≠ 2)] [hπ : Fact (Irreducible π)]
    (n : ℕ)
    (g : falseTateLayer p (π : ℚ_[p]) n n ≃ₐ[ℚ_[p]]
      falseTateLayer p (π : ℚ_[p]) n n) :
    (finiteDiagonalGaloisEquiv_padic p π n g).left.toAdd =
      finiteKummerExponent p (π : ℚ_[p]) n g := rfl

/-- The rational affine isomorphism retains the finite cyclotomic character. -/
theorem finiteDiagonalGaloisEquiv_padic_right [hp₂ : Fact (p ≠ 2)] [hπ : Fact (Irreducible π)]
    (n : ℕ)
    (g : falseTateLayer p (π : ℚ_[p]) n n ≃ₐ[ℚ_[p]]
      falseTateLayer p (π : ℚ_[p]) n n) :
    (finiteDiagonalGaloisEquiv_padic p π n g).right =
      finiteCyclotomicCharacter p (π : ℚ_[p]) n g := rfl

/-- Every positive rational diagonal layer has the expected degree,
including the first layer. -/
theorem finrank_falseTateLayer_diagonal_padic [hp₂ : Fact (p ≠ 2)] [hπ : Fact (Irreducible π)]
    (n : ℕ) :
    Module.finrank (ℚ_[p]) (falseTateLayer p (π : ℚ_[p]) (n + 1) (n + 1)) =
      p ^ (n + 1) * (p - 1) * p ^ n := by
  rw [finrank_falseTateLayer_diagonal p π (n + 1), finrank_cyclotomicLayer_padic,
    Nat.totient_prime_pow_succ (Fact.out : p.Prime)]
  ring

/-- The rational cyclotomic fixer is the entire translation factor. -/
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

/-- The rational radical fixer is the entire pure-unit factor. -/
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

end FalseTateExtension
end
