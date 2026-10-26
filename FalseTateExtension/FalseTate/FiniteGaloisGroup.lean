/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FalseTateExtension.Cyclotomic.Filtration
public import FalseTateExtension.Cyclotomic.InfiniteCharacter
public import FalseTateExtension.Cyclotomic.Restriction
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

Let `K` be a field of characteristic zero, `π ∈ K` nonzero and `L_n = K(π^{1/p^n}, ζ_{p^n})`.
The Kummer exponent `b_n` and the cyclotomic character `χ_n` give an injective homomorphism
`g ↦ (b_n(g), χ_n(g))` from `Gal(L_n/K)` to the affine group `ℤ/p^n ⋊ H_n`, where `H_n ≤ (ℤ/p^n)ˣ`
is the image of the cyclotomic character of `K(ζ_{p^n})/K` and `H_n` acts on `ℤ/p^n` by
multiplication. When `K/ℚ_p` is a complete discretely valued field, `π` a uniformizer of `K` and
`p ≠ 2`, it is an isomorphism, so `[L_n : K] = p^n [K(ζ_{p^n}) : K]` and `[L_n : K(ζ_{p^n})] = p^n`;
under it, `Gal(L_n/K(ζ_{p^n}))` is the group of translations `ℤ/p^n ⋊ 1` and
`Gal(L_n/K(π^{1/p^n}))` the group of units `0 ⋊ H_n`. Over `K = ℚ_p` the image `H_n` is all of
`(ℤ/p^n)ˣ`, so `Gal(L_n/ℚ_p) ≅ ℤ/p^n ⋊ (ℤ/p^n)ˣ` and `[L_{n+1} : ℚ_p] = p^{n+1} φ(p^{n+1})`.

## Main results

* `cyclotomicLayerCharacter`, `card_cyclotomicLayerCharacter_range`: the cyclotomic
  character `Gal(K(ζ_{p^n})/K) →* (ℤ/p^n)ˣ`; it is injective with image of order
  `[K(ζ_{p^n}) : K]`.
* `FiniteAffineGroup`, `FullFiniteAffineGroup`: the affine groups `ℤ/p^n ⋊ H` for `H ≤ (ℤ/p^n)ˣ`
  and `ℤ/p^n ⋊ (ℤ/p^n)ˣ`.
* `finiteDiagonalGaloisEquiv`: `Gal(L_n/K) ≃* ℤ/p^n ⋊ H_n`, `g ↦ (b_n(g), χ_n(g))`.
* `finrank_falseTateLayer_diagonal`, `finrank_falseTateLayer_over_cyclotomic`:
  `[L_n : K] = p^n [K(ζ_{p^n}) : K]` and `[L_n : K(ζ_{p^n})] = p^n`.
* `finiteDiagonalGaloisEquivPadic`: `Gal(L_n/ℚ_p) ≃* ℤ/p^n ⋊ (ℤ/p^n)ˣ`.
* `finrank_falseTateLayer_diagonal_padic`: `[L_{n+1} : ℚ_p] = p^{n+1} (p - 1) p^n`.
* `finiteDiagonalGaloisEquivPadic_mem_translations`,
  `finiteDiagonalGaloisEquivPadic_mem_units`: `Gal(L_n/ℚ_p(ζ_{p^n}))` and
  `Gal(L_n/ℚ_p(π^{1/p^n}))` are the translations and the units of `ℤ/p^n ⋊ (ℤ/p^n)ˣ`.

## References

* [Liu, *On lattices in semi-stable representations: a proof of a conjecture of
  Breuil*](https://doi.org/10.1112/S0010437X0700317X), §5.1.
* [Viviani, *Ramification groups and Artin conductors of radical extensions of
  ℚ*](https://doi.org/10.5802/jtnb.470), §6.
-/

@[expose] public section

noncomputable section

namespace FalseTateExtension

open FontaineWintenberger

section FiniteCyclotomicImage

variable {K : Type*} [Field K] [CharZero K] (p : ℕ) [Fact p.Prime] (n : ℕ)

/-- The cyclotomic character of the restriction of `g ∈ Gal(K(ζ_{p^∞})/K)` to `K(ζ_{p^n})` is
`χ(g) mod p^n`, where `χ : Gal(K(ζ_{p^∞})/K) →* ℤ_pˣ` is the cyclotomic character. -/
theorem cyclotomicLayerCharacter_restrictionToLayer
    (g : cyclotomicExtension (K := K) p ≃ₐ[K] cyclotomicExtension (K := K) p) :
    cyclotomicLayerCharacter p n (cyclotomicRestrictionToLayer p n g) =
      Units.map (PadicInt.toZModPow n).toMonoidHom (cyclotomicExtensionCharacter p g) := by
  apply cyclotomicLayerCharacter_unique p n
  let i := IntermediateField.inclusion (cyclotomicLayer_le_cyclotomicExtension (K := K) p n)
  apply (show Function.Injective i from i.injective)
  rw [map_pow, cyclotomicRestrictionToLayer_commutes]
  exact cyclotomicExtensionCharacter_spec p n g

end FiniteCyclotomicImage

section FiniteAffineCoordinates

variable {K : Type*} [Field K] [CharZero K] (p : ℕ) [Fact p.Prime] (π : K) (n : ℕ)

/-- The inclusion `K(ζ_{p^n}) → K(π^{1/p^n}, ζ_{p^n})`. -/
def finiteCyclotomicInclusion :
    cyclotomicLayer (K := K) p n →ₐ[K] falseTateLayer p π n n :=
  IntermediateField.inclusion le_sup_right

/-- The inclusion `K(π^{1/p^n}) → K(π^{1/p^n}, ζ_{p^n})`. -/
def finiteRadicalInclusion : radicalLayer p π n →ₐ[K] falseTateLayer p π n n :=
  IntermediateField.inclusion le_sup_left

/-- Restriction `Gal(K(π^{1/p^n}, ζ_{p^n})/K) →* Gal(K(ζ_{p^n})/K)`. -/
def diagonalCyclotomicRestriction :
    (falseTateLayer p π n n ≃ₐ[K] falseTateLayer p π n n) →*
      (cyclotomicLayer (K := K) p n ≃ₐ[K] cyclotomicLayer (K := K) p n) :=
  IntermediateField.restrictNormalHomOfLE
    (le_sup_right : cyclotomicLayer p n ≤ falseTateLayer p π n n)

/-- The restriction of `g ∈ Gal(K(π^{1/p^n}, ζ_{p^n})/K)` to `K(ζ_{p^n})` agrees with `g` on
`K(ζ_{p^n})`. -/
theorem diagonalCyclotomicRestriction_commutes
    (g : falseTateLayer p π n n ≃ₐ[K] falseTateLayer p π n n)
    (x : cyclotomicLayer (K := K) p n) :
    finiteCyclotomicInclusion p π n (diagonalCyclotomicRestriction p π n g x) =
      g (finiteCyclotomicInclusion p π n x) :=
  IntermediateField.restrictNormalHomOfLE_commutes _ g x

/-- The cyclotomic character of the restriction of `g ∈ Gal(K(π^{1/p^n}, ζ_{p^n})/K)` to
`K(ζ_{p^n})` is `χ_n(g)`. -/
theorem cyclotomicLayerCharacter_diagonalRestriction
    (g : falseTateLayer p π n n ≃ₐ[K] falseTateLayer p π n n) :
    cyclotomicLayerCharacter p n (diagonalCyclotomicRestriction p π n g) =
      finiteCyclotomicCharacter p π n g := by
  apply cyclotomicLayerCharacter_unique p n
  let i := finiteCyclotomicInclusion p π n
  apply (show Function.Injective i from i.injective)
  rw [map_pow, diagonalCyclotomicRestriction_commutes]
  exact finiteCyclotomicCharacter_spec p π n g

/-- `χ_n(g)` lies in the image of the cyclotomic character of `K(ζ_{p^n})/K`. -/
theorem finiteCyclotomicCharacter_mem_range
    (g : falseTateLayer p π n n ≃ₐ[K] falseTateLayer p π n n) :
    finiteCyclotomicCharacter p π n g ∈ (cyclotomicLayerCharacter (K := K) p n).range :=
  ⟨diagonalCyclotomicRestriction p π n g,
    cyclotomicLayerCharacter_diagonalRestriction p π n g⟩

/-- The action of `(ℤ/p^n)ˣ` on the additive group `ℤ/p^n` by multiplication. -/
abbrev finiteAffineAction : (ZMod (p ^ n))ˣ →* MulAut (Multiplicative (ZMod (p ^ n))) :=
  affineAction (ZMod (p ^ n)) (MonoidHom.id _)

/-- The affine group `ℤ/p^n ⋊ H` for a subgroup `H ≤ (ℤ/p^n)ˣ`, `H` acting on `ℤ/p^n` by
multiplication. -/
abbrev FiniteAffineGroup (H : Subgroup (ZMod (p ^ n))ˣ) : Type :=
  AffineGroup (ZMod (p ^ n)) H.subtype

/-- The homomorphism `g ↦ (b_n(g), χ_n(g))` from `Gal(K(π^{1/p^n}, ζ_{p^n})/K)` to `ℤ/p^n ⋊ H_n`,
where `H_n ≤ (ℤ/p^n)ˣ` is the image of the cyclotomic character of `K(ζ_{p^n})/K`. -/
def finiteAffineGaloisHom [hπ : NeZero π] :
    (falseTateLayer p π n n ≃ₐ[K] falseTateLayer p π n n) →*
      FiniteAffineGroup p n (cyclotomicLayerCharacter (K := K) p n).range where
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

/-- `g ↦ (b_n(g), χ_n(g))` is injective on `Gal(K(π^{1/p^n}, ζ_{p^n})/K)`. -/
theorem finiteAffineGaloisHom_injective [hπ : NeZero π] :
    Function.Injective (finiteAffineGaloisHom p π n) := by
  intro g h heq
  apply finiteCoordinates_injective p π n
  exact Prod.ext (congrArg (fun x => x.left.toAdd) heq)
    (congrArg (fun x => x.right.val) heq)

/-- `|ℤ/p^n ⋊ H| = p^n |H|`. -/
theorem card_finiteAffineGroup (H : Subgroup (ZMod (p ^ n))ˣ) :
    Nat.card (FiniteAffineGroup p n H) = p ^ n * Nat.card H := by
  have : NeZero (p ^ n) := ⟨pow_ne_zero n (Fact.out : p.Prime).ne_zero⟩
  calc
    _ = Nat.card (Multiplicative (ZMod (p ^ n)) × H) :=
      Nat.card_congr SemidirectProduct.equivProd
    _ = Nat.card (ZMod (p ^ n)) * Nat.card H := by
      rw [Nat.card_prod, Nat.card_congr Multiplicative.toAdd]
    _ = _ := by rw [Nat.card_eq_fintype_card, ZMod.card]

/-- `Gal(K(π^{1/p^n}, ζ_{p^n})/K(ζ_{p^n})) = ker χ_n`. -/
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
    rw [← cyclotomicLayerCharacter_diagonalRestriction, hr, map_one]
  · intro hg
    have hr : diagonalCyclotomicRestriction p π n g = 1 := by
      apply cyclotomicLayerCharacter_injective p n
      rw [cyclotomicLayerCharacter_diagonalRestriction, hg, map_one]
    rw [IntermediateField.mem_fixingSubgroup_iff]
    rintro x ⟨y, rfl⟩
    have h := diagonalCyclotomicRestriction_commutes p π n g y
    rw [hr] at h
    exact h.symm

/-- `g ∈ Gal(K(π^{1/p^n}, ζ_{p^n})/K)` fixes `K(π^{1/p^n})` if and only if `b_n(g) = 0`. -/
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
      ⟨⟨pPowRoot p π n, pPowRoot_mem_radicalLayer p π n⟩, rfl⟩
  · intro hb
    rw [IntermediateField.mem_fixingSubgroup_iff]
    have heq : g.toAlgHom.comp i = i := by
      apply IntermediateField.adjoin_algHom_ext
      intro z hz
      obtain rfl := Set.mem_singleton_iff.mp hz
      change g (pPowRootLayer p π n) = pPowRootLayer p π n
      have h := finiteKummerExponent_spec p π n g
      simpa only [hb, ZMod.val_zero, pow_zero, one_mul] using h
    rintro x ⟨y, rfl⟩
    exact AlgHom.congr_fun heq y

/-- The affine group `ℤ/p^n ⋊ (ℤ/p^n)ˣ`, the units acting on `ℤ/p^n` by multiplication. -/
abbrev FullFiniteAffineGroup : Type := AffineGroup (ZMod (p ^ n)) (MonoidHom.id _)

/-- The inclusion `ℤ/p^n ⋊ H → ℤ/p^n ⋊ (ℤ/p^n)ˣ` for a subgroup `H ≤ (ℤ/p^n)ˣ`. -/
def finiteAffineInclusion (H : Subgroup (ZMod (p ^ n))ˣ) :
    FiniteAffineGroup p n H →* FullFiniteAffineGroup p n :=
  SemidirectProduct.map (MonoidHom.id _) H.subtype (fun _ => rfl)

omit [Fact p.Prime] in
/-- The inclusion `ℤ/p^n ⋊ H → ℤ/p^n ⋊ (ℤ/p^n)ˣ` is injective. -/
theorem finiteAffineInclusion_injective (H : Subgroup (ZMod (p ^ n))ˣ) :
    Function.Injective (finiteAffineInclusion p n H) := by
  intro g h heq
  apply SemidirectProduct.ext
  · exact congrArg (fun x : FullFiniteAffineGroup p n => x.left) heq
  · apply Subtype.ext
    exact congrArg (fun x : FullFiniteAffineGroup p n => x.right) heq

open scoped commutatorElement in
omit [Fact p.Prime] in
/-- `[(a, u), (b, 1)] = ((u - 1) b, 1)` in `ℤ/p^n ⋊ (ℤ/p^n)ˣ`. -/
theorem finiteAffine_commutator_inl (g : FullFiniteAffineGroup p n) (b : ZMod (p ^ n)) :
    ⁅g, (SemidirectProduct.inl (Multiplicative.ofAdd b) : FullFiniteAffineGroup p n)⁆ =
      SemidirectProduct.inl (Multiplicative.ofAdd (((g.right : ZMod (p ^ n)) - 1) * b)) :=
  AffineGroup.commutator_inl _ g b

end FiniteAffineCoordinates

section FiniteAffineSurjectivity

variable {K : Type*} [NontriviallyNormedField K] [IsCompleteDiscreteValuedField K] [CharZero K]
variable (p : ℕ) [Fact p.Prime] [Algebra (ℚ_[p]) K]
variable (π : 𝒪[K])

/-- For `b ∈ ℤ/p^n` and `u` in the image of the cyclotomic character of `K(ζ_{p^n})/K`, there is
`g ∈ Gal(K(π^{1/p^n}, ζ_{p^n})/K)` with `b_n(g) = b` and `χ_n(g) = u`. -/
theorem exists_finiteCoordinates_eq [hp₂ : Fact (p ≠ 2)] [hπ : Fact (Irreducible π)] (n : ℕ)
    (b : ZMod (p ^ n)) (u : (ZMod (p ^ n))ˣ)
    (hu : u ∈ (cyclotomicLayerCharacter (K := K) p n).range) :
    ∃ g : falseTateLayer p (π : K) n n ≃ₐ[K] falseTateLayer p (π : K) n n,
      finiteKummerExponent p (π : K) n g = b ∧
        finiteCyclotomicCharacter p (π : K) n g = u := by
  have : NeZero (p ^ n) := ⟨pow_ne_zero n (Fact.out : p.Prime).ne_zero⟩
  let hπ₀ : (π : K) ≠ 0 := fun h => hπ.out.ne_zero (Subtype.ext h)
  obtain ⟨c, hc⟩ := hu
  obtain ⟨γ, hγ⟩ := cyclotomicRestrictionToLayer_surjective (K := K) p n c
  have hu' : Units.map (PadicInt.toZModPow n).toMonoidHom
      (cyclotomicExtensionCharacter p γ) = u :=
    (cyclotomicLayerCharacter_restrictionToLayer p n γ).symm.trans
      ((congrArg (cyclotomicLayerCharacter p n) hγ).trans hc)
  obtain ⟨g, hb, hχ⟩ := exists_padicCoordinates_eq p π (b.val : ℤ_[p])
    (cyclotomicExtensionCharacter p γ) ⟨γ, rfl⟩
  refine ⟨infiniteLayerRestriction p (π : K) n g, ?_, ?_⟩
  · rw [← padicKummerExponent_toZModPow, hb]
    simp only [map_natCast, ZMod.natCast_zmod_val]
  · rw [← padicCyclotomicCharacter_toZModPow, hχ]
    exact hu'

/-- `g ↦ (b_n(g), χ_n(g))` maps `Gal(K(π^{1/p^n}, ζ_{p^n})/K)` onto `ℤ/p^n ⋊ H_n`. -/
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

/-- `Gal(K(π^{1/p^n}, ζ_{p^n})/K) ≃* ℤ/p^n ⋊ H_n`, `g ↦ (b_n(g), χ_n(g))`, where `H_n ≤ (ℤ/p^n)ˣ`
is the image of the cyclotomic character of `K(ζ_{p^n})/K`. -/
def finiteDiagonalGaloisEquiv [hp₂ : Fact (p ≠ 2)] [hπ : Fact (Irreducible π)] (n : ℕ) :
    (falseTateLayer p (π : K) n n ≃ₐ[K] falseTateLayer p (π : K) n n) ≃*
      FiniteAffineGroup p n (cyclotomicLayerCharacter (K := K) p n).range :=
  MulEquiv.ofBijective
    (finiteAffineGaloisHom p (π : K) n)
    ⟨finiteAffineGaloisHom_injective p (π : K) n,
      finiteAffineGaloisHom_surjective p π n⟩

/-- `[K(π^{1/p^n}, ζ_{p^n}) : K] = p^n [K(ζ_{p^n}) : K]`. -/
theorem finrank_falseTateLayer_diagonal [hp₂ : Fact (p ≠ 2)] [hπ : Fact (Irreducible π)] (n : ℕ) :
    Module.finrank K (falseTateLayer p (π : K) n n) =
      p ^ n * Module.finrank K (cyclotomicLayer (K := K) p n) := by
  have := falseTateLayer_isGalois p (π : K) n
  rw [← IsGalois.card_aut_eq_finrank K (falseTateLayer p (π : K) n n),
    Nat.card_congr (finiteDiagonalGaloisEquiv p π n).toEquiv,
    card_finiteAffineGroup, card_cyclotomicLayerCharacter_range]

/-- Under `Gal(K(π^{1/p^n}, ζ_{p^n})/K) ≃ ℤ/p^n ⋊ H_n`, the subgroup
`Gal(K(π^{1/p^n}, ζ_{p^n})/K(ζ_{p^n}))` corresponds to the translations `ℤ/p^n ⋊ 1`. -/
theorem finiteDiagonalGaloisEquiv_mem_translations [hp₂ : Fact (p ≠ 2)] [hπ : Fact (Irreducible π)]
    (n : ℕ)
    (g : falseTateLayer p (π : K) n n ≃ₐ[K] falseTateLayer p (π : K) n n) :
    finiteDiagonalGaloisEquiv p π n g ∈
      (SemidirectProduct.inl : Multiplicative (ZMod (p ^ n)) →*
        FiniteAffineGroup p n (cyclotomicLayerCharacter (K := K) p n).range).range ↔
      g ∈ (finiteCyclotomicInclusion p (π : K) n).fieldRange.fixingSubgroup := by
  rw [finiteCyclotomicInclusion_fixingSubgroup, SemidirectProduct.range_inl_eq_ker_rightHom,
    MonoidHom.mem_ker, MonoidHom.mem_ker]
  constructor
  · exact fun h => congrArg Subtype.val h
  · exact fun h => Subtype.ext h

/-- Under `Gal(K(π^{1/p^n}, ζ_{p^n})/K) ≃ ℤ/p^n ⋊ H_n`, the subgroup
`Gal(K(π^{1/p^n}, ζ_{p^n})/K(π^{1/p^n}))` corresponds to the units `0 ⋊ H_n`. -/
theorem finiteDiagonalGaloisEquiv_mem_units [hp₂ : Fact (p ≠ 2)] [hπ : Fact (Irreducible π)] (n : ℕ)
    (g : falseTateLayer p (π : K) n n ≃ₐ[K] falseTateLayer p (π : K) n n) :
    finiteDiagonalGaloisEquiv p π n g ∈
      (SemidirectProduct.inr : (cyclotomicLayerCharacter (K := K) p n).range →*
        FiniteAffineGroup p n (cyclotomicLayerCharacter (K := K) p n).range).range ↔
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

/-- The `K(ζ_{p^n})`-algebra structure on `K(π^{1/p^n}, ζ_{p^n})` given by the inclusion. -/
local instance finiteDiagonalCyclotomicAlgebra (n : ℕ) :
    Algebra (cyclotomicLayer (K := K) p n) (falseTateLayer p (π : K) n n) :=
  (finiteCyclotomicInclusion p (π : K) n).toRingHom.toAlgebra

/-- `K ⊆ K(ζ_{p^n}) ⊆ K(π^{1/p^n}, ζ_{p^n})` is a tower of fields. -/
local instance finiteDiagonalCyclotomicScalarTower (n : ℕ) :
    IsScalarTower K (cyclotomicLayer (K := K) p n) (falseTateLayer p (π : K) n n) :=
  IsScalarTower.of_algebraMap_eq (congrFun rfl)

/-- `[K(π^{1/p^n}, ζ_{p^n}) : K(ζ_{p^n})] = p^n`. -/
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

/-- `Gal(ℚ_p(π^{1/p^n}, ζ_{p^n})/ℚ_p) ≃* ℤ/p^n ⋊ (ℤ/p^n)ˣ`, `g ↦ (b_n(g), χ_n(g))`. -/
def finiteDiagonalGaloisEquivPadic [hp₂ : Fact (p ≠ 2)] [hπ : Fact (Irreducible π)] (n : ℕ) :
    (falseTateLayer p (π : ℚ_[p]) n n ≃ₐ[ℚ_[p]]
      falseTateLayer p (π : ℚ_[p]) n n) ≃* FullFiniteAffineGroup p n := by
  let hπ₀ : (π : ℚ_[p]) ≠ 0 := fun h => hπ.out.ne_zero (Subtype.ext h)
  let f := (finiteAffineInclusion p n (cyclotomicLayerCharacter (K := ℚ_[p]) p n).range).comp
    (finiteAffineGaloisHom p (π : ℚ_[p]) n)
  apply MulEquiv.ofBijective f
  constructor
  · exact (finiteAffineInclusion_injective p n _).comp
      (finiteAffineGaloisHom_injective p (π : ℚ_[p]) n)
  · intro x
    have hu : x.right ∈ (cyclotomicLayerCharacter (K := ℚ_[p]) p n).range := by
      exact cyclotomicLayerCharacter_surjective p n x.right
    obtain ⟨g, hb, hχ⟩ := exists_finiteCoordinates_eq p π n x.left.toAdd x.right hu
    refine ⟨g, ?_⟩
    apply SemidirectProduct.ext
    · exact congrArg Multiplicative.ofAdd hb
    · exact hχ

/-- The translation coordinate of `g` under `finiteDiagonalGaloisEquivPadic` is the Kummer
exponent `b_n(g)`. -/
theorem finiteDiagonalGaloisEquivPadic_left [hp₂ : Fact (p ≠ 2)] [hπ : Fact (Irreducible π)]
    (n : ℕ)
    (g : falseTateLayer p (π : ℚ_[p]) n n ≃ₐ[ℚ_[p]]
      falseTateLayer p (π : ℚ_[p]) n n) :
    (finiteDiagonalGaloisEquivPadic p π n g).left.toAdd =
      finiteKummerExponent p (π : ℚ_[p]) n g := rfl

/-- The unit coordinate of `g` under `finiteDiagonalGaloisEquivPadic` is the cyclotomic
character `χ_n(g)`. -/
theorem finiteDiagonalGaloisEquivPadic_right [hp₂ : Fact (p ≠ 2)] [hπ : Fact (Irreducible π)]
    (n : ℕ)
    (g : falseTateLayer p (π : ℚ_[p]) n n ≃ₐ[ℚ_[p]]
      falseTateLayer p (π : ℚ_[p]) n n) :
    (finiteDiagonalGaloisEquivPadic p π n g).right =
      finiteCyclotomicCharacter p (π : ℚ_[p]) n g := rfl

/-- `[ℚ_p(π^{1/p^{n+1}}, ζ_{p^{n+1}}) : ℚ_p] = p^{n+1} φ(p^{n+1}) = p^{n+1} (p - 1) p^n`. -/
theorem finrank_falseTateLayer_diagonal_padic [hp₂ : Fact (p ≠ 2)] [hπ : Fact (Irreducible π)]
    (n : ℕ) :
    Module.finrank (ℚ_[p]) (falseTateLayer p (π : ℚ_[p]) (n + 1) (n + 1)) =
      p ^ (n + 1) * (p - 1) * p ^ n := by
  rw [finrank_falseTateLayer_diagonal p π (n + 1), finrank_cyclotomicLayer_padic,
    Nat.totient_prime_pow_succ (Fact.out : p.Prime)]
  ring

/-- Under `Gal(ℚ_p(π^{1/p^n}, ζ_{p^n})/ℚ_p) ≃ ℤ/p^n ⋊ (ℤ/p^n)ˣ`, the subgroup fixing
`ℚ_p(ζ_{p^n})` corresponds to the translations `ℤ/p^n ⋊ 1`. -/
theorem finiteDiagonalGaloisEquivPadic_mem_translations
    [hp₂ : Fact (p ≠ 2)] [hπ : Fact (Irreducible π)] (n : ℕ)
    (g : falseTateLayer p (π : ℚ_[p]) n n ≃ₐ[ℚ_[p]]
      falseTateLayer p (π : ℚ_[p]) n n) :
    finiteDiagonalGaloisEquivPadic p π n g ∈
      (SemidirectProduct.inl : Multiplicative (ZMod (p ^ n)) →* FullFiniteAffineGroup p n).range ↔
      g ∈ (finiteCyclotomicInclusion p (π : ℚ_[p]) n).fieldRange.fixingSubgroup := by
  rw [finiteCyclotomicInclusion_fixingSubgroup, SemidirectProduct.range_inl_eq_ker_rightHom,
    MonoidHom.mem_ker, MonoidHom.mem_ker]
  rfl

/-- Under `Gal(ℚ_p(π^{1/p^n}, ζ_{p^n})/ℚ_p) ≃ ℤ/p^n ⋊ (ℤ/p^n)ˣ`, the subgroup fixing
`ℚ_p(π^{1/p^n})` corresponds to the units `0 ⋊ (ℤ/p^n)ˣ`. -/
theorem finiteDiagonalGaloisEquivPadic_mem_units
    [hp₂ : Fact (p ≠ 2)] [hπ : Fact (Irreducible π)] (n : ℕ)
    (g : falseTateLayer p (π : ℚ_[p]) n n ≃ₐ[ℚ_[p]]
      falseTateLayer p (π : ℚ_[p]) n n) :
    finiteDiagonalGaloisEquivPadic p π n g ∈
      (SemidirectProduct.inr : (ZMod (p ^ n))ˣ →* FullFiniteAffineGroup p n).range ↔
      g ∈ (finiteRadicalInclusion p (π : ℚ_[p]) n).fieldRange.fixingSubgroup := by
  rw [mem_finiteRadicalInclusion_fixingSubgroup_iff p (π : ℚ_[p]) n]
  constructor
  · rintro ⟨u, hu⟩
    exact (congrArg (fun x => x.left.toAdd) hu).symm
  · intro hb
    refine ⟨(finiteDiagonalGaloisEquivPadic p π n g).right, ?_⟩
    apply SemidirectProduct.ext
    · exact congrArg Multiplicative.ofAdd hb.symm
    · rfl

end RationalFiniteAffine

@[deprecated (since := "2026-10-26")]
alias finiteDiagonalGaloisEquiv_padic := finiteDiagonalGaloisEquivPadic

@[deprecated (since := "2026-10-26")]
alias finiteDiagonalGaloisEquiv_padic_left := finiteDiagonalGaloisEquivPadic_left

@[deprecated (since := "2026-10-26")]
alias finiteDiagonalGaloisEquiv_padic_right := finiteDiagonalGaloisEquivPadic_right

@[deprecated (since := "2026-10-26")]
alias finiteDiagonalGaloisEquiv_padic_mem_translations :=
  finiteDiagonalGaloisEquivPadic_mem_translations

@[deprecated (since := "2026-10-26")]
alias finiteDiagonalGaloisEquiv_padic_mem_units := finiteDiagonalGaloisEquivPadic_mem_units

end FalseTateExtension
end
