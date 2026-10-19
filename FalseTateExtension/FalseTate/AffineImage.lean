/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FalseTateExtension.Affine.Index
public import FalseTateExtension.Cyclotomic.APF
public import FalseTateExtension.Cyclotomic.InertiaImage
public import FalseTateExtension.Kummer.APF
public import FalseTateExtension.Mathlib.FieldTheory.Galois.InfiniteCorrespondence
public import FontaineWintenberger.APF.Galois
public import FontaineWintenberger.APF.Galois.Restriction

/-!
# The affine image of the false Tate Galois group

The closed embedding of `Gal(K_FT/K)` into `ℤ_[p] ⋊ ℤ_[p]ˣ` identifies the Galois group with a
closed subgroup `falseTateAffineImage`; the subgroup fixing the Kummer extension corresponds to the
pure units of that image, and the unit projection has the image of the cyclotomic character as
range.

## References

* Liu, *On lattices in semi-stable representations: a proof of a conjecture of Breuil*, §5.1.
-/

@[expose] public section

noncomputable section

namespace FalseTateExtension

open FontaineWintenberger

section AffineImage

variable {K : Type*} [Field K] [CharZero K] (p : ℕ) [Fact p.Prime] (π : K)

local notation "Γ" => falseTateExtension p π ≃ₐ[K] falseTateExtension p π

/-- The closed image of the false Tate Galois group under its
Kummer and cyclotomic coordinates. -/
def falseTateAffineImage [hπ : NeZero π] : ClosedSubgroup (PadicAffineGroup p) where
  toSubgroup := (affineGaloisHom p π).range
  isClosed' := (isClosedEmbedding_affineGaloisHom p π).isClosed_range

/-- The Krull Galois group is the closed affine image,
with its group structure and topology. -/
def falseTateGaloisEquivAffineImage [hπ : NeZero π] : Γ ≃ₜ* falseTateAffineImage p π := by
  have := falseTateExtension_isGalois p π
  let f : Γ →* falseTateAffineImage p π := (affineGaloisHom p π).rangeRestrict
  have hf : Function.Bijective f :=
    ⟨fun g h heq => affineGaloisHom_injective p π (congrArg Subtype.val heq),
      (affineGaloisHom p π).rangeRestrict_surjective⟩
  let e := MulEquiv.ofBijective f hf
  have hc : Continuous e := (continuous_affineGaloisHom p π).subtype_mk _
  exact
    { e with
      continuous_toFun := hc
      continuous_invFun := hc.continuous_symm_of_equiv_compact_to_t2 }

@[simp]
theorem falseTateAffineEquiv_apply [hπ : NeZero π] (g : Γ) :
    (falseTateGaloisEquivAffineImage p π g : PadicAffineGroup p) = affineGaloisHom p π g := rfl

/-- Unit projection of the affine isomorphism is exactly the
cyclotomic character. -/
theorem falseTateAffineEquiv_projection [hπ : NeZero π] :
    (affineProjection (falseTateAffineImage p π)).comp
      (falseTateGaloisEquivAffineImage p π).toMonoidHom = padicCyclotomicCharacter p π := rfl

/-- The affine unit image is the cyclotomic character
image on the cyclotomic subfield. -/
theorem falseTateAffineImage_projection_range [hπ : NeZero π] :
    (affineProjection (falseTateAffineImage p π)).range =
      (cyclotomicExtensionCharacter (K := K) p).range := by
  rw [← padicCyclotomicCharacter_range p π]
  ext u
  constructor
  · rintro ⟨g, rfl⟩
    obtain ⟨σ, rfl⟩ := (falseTateGaloisEquivAffineImage p π).surjective g
    exact ⟨σ, rfl⟩
  · rintro ⟨σ, rfl⟩
    exact ⟨falseTateGaloisEquivAffineImage p π σ, rfl⟩

/-- The infinite radical tower lies in the false Tate field. -/
theorem kummerExtension_le_falseTateExtension :
    kummerExtension p π ≤ falseTateExtension p π := by
  rw [falseTateExtension_eq_sup]
  exact le_sup_left

/-- The inclusion of the radical tower into the false Tate field. -/
def falseTateKummerInclusion : kummerExtension p π →ₐ[K] falseTateExtension p π :=
  IntermediateField.inclusion (kummerExtension_le_falseTateExtension p π)

/-- The subgroup fixing the infinite radical tower. -/
def falseTateKummerFixing : Subgroup Γ := (falseTateKummerInclusion p π).fieldRange.fixingSubgroup

/-- Fixing every radical is equivalent to vanishing of the
p-adic translation coordinate. -/
theorem mem_falseTateKummerFixing_iff [hπ : NeZero π] (σ : Γ) :
    σ ∈ falseTateKummerFixing p π ↔ padicKummerExponent p π σ = 0 := by
  constructor
  · intro hσ
    change σ ∈ (falseTateKummerInclusion p π).fieldRange.fixingSubgroup at hσ
    have hfix := (IntermediateField.mem_fixingSubgroup_iff _ σ).mp hσ
    apply PadicInt.ext_of_toZModPow.mp
    intro n
    rw [padicKummerExponent_toZModPow, map_zero]
    apply finiteKummerExponent_unique p π n _ 0
    simp only [ZMod.val_zero, pow_zero, one_mul]
    apply (IntermediateField.inclusion (falseTateLayer_le_falseTateExtension p π n n)).injective
    change (IntermediateField.inclusion (falseTateLayer_le_falseTateExtension p π n n))
        (infiniteLayerRestriction p π n σ (pPowRootLayer p π n)) =
      (IntermediateField.inclusion (falseTateLayer_le_falseTateExtension p π n n))
        (pPowRootLayer p π n)
    rw [infiniteLayerRestriction_commutes]
    let y : kummerExtension p π := ⟨pPowRoot p π n,
      radicalLayer_le_kummerExtension p π n (pPowRoot_mem_radicalLayer p π n)⟩
    exact hfix _ ⟨y, rfl⟩
  · intro hσ
    change σ ∈ (falseTateKummerInclusion p π).fieldRange.fixingSubgroup
    rw [IntermediateField.mem_fixingSubgroup_iff]
    rintro x ⟨y, rfl⟩
    obtain ⟨n, hn⟩ := (mem_kummerExtension_iff p π (y : AlgebraicClosure K)).mp y.property
    let i : radicalLayer p π n →ₐ[K] falseTateExtension p π :=
      IntermediateField.inclusion ((radicalLayer_le_kummerExtension p π n).trans
        (kummerExtension_le_falseTateExtension p π))
    have heq : σ.toAlgHom.comp i = i := by
      apply IntermediateField.adjoin_algHom_ext
      intro z hz
      obtain rfl := Set.mem_singleton_iff.mp hz
      have ha : finiteKummerExponent p π n
          (infiniteLayerRestriction p π n σ) = 0 := by
        rw [← padicKummerExponent_toZModPow, hσ, map_zero]
      have h := finiteKummerExponent_spec p π n (infiniteLayerRestriction p π n σ)
      rw [ha, ZMod.val_zero, pow_zero, one_mul] at h
      have hh := congrArg
        (IntermediateField.inclusion (falseTateLayer_le_falseTateExtension p π n n)) h
      rw [infiniteLayerRestriction_commutes] at hh
      exact hh
    exact AlgHom.congr_fun heq ⟨y.val, hn⟩

/-- Pure units in the affine image pull back to the radical fixer. -/
theorem falseTateAffineEquiv_mem_pureUnits [hπ : NeZero π] (σ : Γ) :
    falseTateGaloisEquivAffineImage p π σ ∈ affinePureUnits (falseTateAffineImage p π) ↔
      σ ∈ falseTateKummerFixing p π := by
  rw [mem_affinePureUnits, mem_falseTateKummerFixing_iff p π]
  rfl

/-- The radical fixer becomes exactly the pure-unit subgroup in
the closed affine image. -/
theorem falseTateKummerFixing_map_affine [hπ : NeZero π] :
    (falseTateKummerFixing p π).map (falseTateGaloisEquivAffineImage p π).toMonoidHom =
      affinePureUnits (falseTateAffineImage p π) := by
  ext g
  obtain ⟨σ, rfl⟩ := (falseTateGaloisEquivAffineImage p π).surjective g
  constructor
  · rintro ⟨τ, hτ, heq⟩
    have hτσ := (falseTateGaloisEquivAffineImage p π).injective heq
    subst τ
    exact (falseTateAffineEquiv_mem_pureUnits p π σ).mpr hτ
  · intro hσ
    exact ⟨σ, (falseTateAffineEquiv_mem_pureUnits p π σ).mp hσ, rfl⟩

variable [Algebra (ℚ_[p]) K] [FiniteDimensional (ℚ_[p]) K]

/-- The affine unit projection has infinite image for every finite
p-adic base, including the dyadic case. -/
theorem falseTateAffineImage_projection_infinite [hπ : NeZero π] :
    Infinite (affineProjection (falseTateAffineImage p π)).range := by
  rw [falseTateAffineImage_projection_range]
  let := padicUnits_infinite p
  let H := (cyclotomicExtensionCharacter (K := K) p).range
  rcases finite_or_infinite H with hfin | hinf
  · let := hfin
    have hprod := H.card_mul_index
    rw [show Nat.card ((ℤ_[p])ˣ) = 0 from Nat.card_eq_zero_of_infinite] at hprod
    have hpos : 0 < Nat.card H * H.index :=
      Nat.mul_pos Nat.card_pos (cyclotomicExtensionCharacter_index_pos p)
    exact False.elim (hpos.ne' hprod)
  · exact hinf

omit [Algebra (ℚ_[p]) K] [FiniteDimensional (ℚ_[p]) K] in
/-- The character is faithful when the translation kernel vanishes. -/
theorem padicCyclotomicCharacter_injective_of_translationKernel_eq_bot
    [hπ : NeZero π]
    (hM : (affineTranslationKernel (falseTateAffineImage p π)).toAddSubgroup = ⊥) :
    Function.Injective (padicCyclotomicCharacter p π) := by
  have hi : Function.Injective ((affineProjection (falseTateAffineImage p π)).comp
      (falseTateGaloisEquivAffineImage p π).toMonoidHom) :=
    (affineProjection_injective_of_translationKernel_eq_bot _ hM).comp
      (falseTateGaloisEquivAffineImage p π).injective
  rw [falseTateAffineEquiv_projection] at hi
  exact hi

omit [Algebra (ℚ_[p]) K] [FiniteDimensional (ℚ_[p]) K] in
/-- The cyclotomic inclusion has trivial fixing subgroup when the
translation kernel vanishes. -/
theorem falseTate_cyclotomicFixing_eq_bot_of_translationKernel_eq_bot
    [hπ : NeZero π]
    (hM : (affineTranslationKernel (falseTateAffineImage p π)).toAddSubgroup = ⊥) :
    (IntermediateField.inclusion
      (cyclotomicExtension_le_falseTateExtension p π)).fieldRange.fixingSubgroup = ⊥ := by
  let i := IntermediateField.inclusion (cyclotomicExtension_le_falseTateExtension p π)
  apply bot_unique
  intro g hg
  have hρ : cyclotomicRestriction p π g = 1 := by
    apply AlgEquiv.ext
    intro x
    apply i.injective
    change i (cyclotomicRestriction p π g x) = i x
    rw [cyclotomicRestriction_commutes]
    exact (IntermediateField.mem_fixingSubgroup_iff _ g).mp hg (i x) ⟨x, rfl⟩
  apply padicCyclotomicCharacter_injective_of_translationKernel_eq_bot p π hM
  calc
    _ = cyclotomicExtensionCharacter p (cyclotomicRestriction p π g) :=
      congrArg (fun f => f g) (padicCyclotomicCharacter_eq_comp p π)
    _ = 1 := by rw [hρ, map_one]
    _ = _ := (map_one _).symm

omit [Algebra (ℚ_[p]) K] [FiniteDimensional (ℚ_[p]) K] in
/-- A vanishing translation kernel makes the false Tate
field equal to its cyclotomic subfield, by infinite Galois correspondence. -/
theorem falseTateExtension_eq_cyclotomicExtension_of_translationKernel_eq_bot
    [hπ : NeZero π]
    (hM : (affineTranslationKernel (falseTateAffineImage p π)).toAddSubgroup = ⊥) :
    falseTateExtension p π = cyclotomicExtension (K := K) p := by
  have := falseTateExtension_isGalois p π
  exact IntermediateField.eq_of_inclusion_fixingSubgroup_eq_bot
    (cyclotomicExtension_le_falseTateExtension p π)
    (falseTate_cyclotomicFixing_eq_bot_of_translationKernel_eq_bot p π hM)

end AffineImage

end FalseTateExtension
end
