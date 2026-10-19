/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FalseTateExtension.AffineIndex
public import FalseTateExtension.Padic.CyclotomicAPF
public import FalseTateExtension.Padic.CyclotomicInertiaCompletion
public import FalseTateExtension.KummerProfile
public import FontaineWintenberger.APF.Galois

/-!
# Strict APF of the actual false Tate extension

The actual affine Galois image identifies its radical-fixer and cyclotomic
projection indices with the ramification indices of the original fields.
Their bounded growth proves APF and strict APF of the original false Tate
extension, retaining its finite residue factor and including the prime two.
-/

@[expose] public section

noncomputable section

namespace FalseTateExtension

open FontaineWintenberger

private theorem intermediateField_eq_of_inclusion_fixing_eq_bot
    {F Ω : Type*} [Field F] [Field Ω] [Algebra F Ω]
    {S T : IntermediateField F Ω} [IsGalois F T] (hST : S ≤ T)
    (hfix : (IntermediateField.inclusion hST).fieldRange.fixingSubgroup = ⊥) : T = S := by
  let i := IntermediateField.inclusion hST
  have htop : i.fieldRange = ⊤ := by
    calc
      i.fieldRange = IntermediateField.fixedField i.fieldRange.fixingSubgroup :=
        (InfiniteGalois.fixedField_fixingSubgroup i.fieldRange).symm
      _ = IntermediateField.fixedField (⊥ : Subgroup (T ≃ₐ[F] T)) :=
        congrArg IntermediateField.fixedField hfix
      _ = ⊤ := IntermediateField.fixedField_bot
  apply le_antisymm _ hST
  intro x hx
  have hx' : (⟨x, hx⟩ : T) ∈ i.fieldRange := by
    rw [htop]
    trivial
  obtain ⟨y, hy⟩ := hx'
  have hy' : (y : Ω) = x := congrArg Subtype.val hy
  exact hy' ▸ y.property

section AffineImage

variable {K : Type*} [Field K] [CharZero K] (p : ℕ) [Fact p.Prime] (π : K)

local notation "Γ" => falseTateExtension p π ≃ₐ[K] falseTateExtension p π

/-- The closed image of the original false Tate Galois group under its
actual Kummer and cyclotomic coordinates. -/
def falseTateAffineImage (hπ : π ≠ 0) : ClosedSubgroup (PadicAffineGroup p) where
  toSubgroup := (affineGaloisHom p π hπ).range
  isClosed' := (isClosedEmbedding_affineGaloisHom p π hπ).isClosed_range

/-- The original Krull Galois group is the actual closed affine image,
with its original group structure and topology. -/
def falseTateAffineEquiv (hπ : π ≠ 0) : Γ ≃ₜ* falseTateAffineImage p π hπ := by
  have := falseTateExtension_isGalois p π hπ
  let f : Γ →* falseTateAffineImage p π hπ := (affineGaloisHom p π hπ).rangeRestrict
  have hf : Function.Bijective f :=
    ⟨fun g h heq => affineGaloisHom_injective p π hπ (congrArg Subtype.val heq),
      (affineGaloisHom p π hπ).rangeRestrict_surjective⟩
  let e := MulEquiv.ofBijective f hf
  have hc : Continuous e := (continuous_affineGaloisHom p π hπ).subtype_mk _
  exact
    { e with
      continuous_toFun := hc
      continuous_invFun := hc.continuous_symm_of_equiv_compact_to_t2 }

@[simp]
theorem falseTateAffineEquiv_apply (hπ : π ≠ 0) (g : Γ) :
    (falseTateAffineEquiv p π hπ g : PadicAffineGroup p) = affineGaloisHom p π hπ g := rfl

/-- Unit projection of the actual affine isomorphism is exactly the
original cyclotomic character. -/
theorem falseTateAffineEquiv_projection (hπ : π ≠ 0) :
    (affineProjection (falseTateAffineImage p π hπ)).comp
      (falseTateAffineEquiv p π hπ).toMonoidHom = padicCyclotomicCharacter p π := rfl

/-- The actual affine unit image is the canonical cyclotomic character
image on the original cyclotomic subfield. -/
theorem falseTateAffineImage_projection_range (hπ : π ≠ 0) :
    (affineProjection (falseTateAffineImage p π hπ)).range =
      (cyclotomicExtensionCharacter (K := K) p).range := by
  rw [← padicCyclotomicCharacter_range p π hπ]
  ext u
  constructor
  · rintro ⟨g, rfl⟩
    obtain ⟨σ, rfl⟩ := (falseTateAffineEquiv p π hπ).surjective g
    exact ⟨σ, rfl⟩
  · rintro ⟨σ, rfl⟩
    exact ⟨falseTateAffineEquiv p π hπ σ, rfl⟩

/-- The actual infinite radical tower lies in the original false Tate field. -/
theorem kummerExtension_le_falseTateExtension :
    kummerExtension p π ≤ falseTateExtension p π := by
  rw [falseTateExtension_eq_sup]
  exact le_sup_left

/-- The original inclusion of the actual radical tower into the false Tate field. -/
def falseTateKummerInclusion : kummerExtension p π →ₐ[K] falseTateExtension p π :=
  IntermediateField.inclusion (kummerExtension_le_falseTateExtension p π)

/-- The actual subgroup fixing the original infinite radical tower. -/
def falseTateKummerFixing : Subgroup Γ := (falseTateKummerInclusion p π).fieldRange.fixingSubgroup

/-- Fixing every actual radical is equivalent to vanishing of the
canonical p-adic translation coordinate. -/
theorem mem_falseTateKummerFixing_iff (hπ : π ≠ 0) (σ : Γ) :
    σ ∈ falseTateKummerFixing p π ↔ padicKummerExponent p π hπ σ = 0 := by
  constructor
  · intro hσ
    change σ ∈ (falseTateKummerInclusion p π).fieldRange.fixingSubgroup at hσ
    have hfix := (IntermediateField.mem_fixingSubgroup_iff _ σ).mp hσ
    apply PadicInt.ext_of_toZModPow.mp
    intro n
    rw [padicKummerExponent_toZModPow, map_zero]
    apply finiteKummerExponent_unique p π n hπ _ 0
    simp only [ZMod.val_zero, pow_zero, one_mul]
    apply (IntermediateField.inclusion (falseTateLayer_le_falseTateExtension p π n n)).injective
    change (IntermediateField.inclusion (falseTateLayer_le_falseTateExtension p π n n))
        (infiniteLayerRestriction p π hπ n σ (layerRadical p π n)) =
      (IntermediateField.inclusion (falseTateLayer_le_falseTateExtension p π n n))
        (layerRadical p π n)
    rw [infiniteLayerRestriction_commutes]
    let y : kummerExtension p π := ⟨radical p π n,
      radicalLayer_le_kummerExtension p π n (radical_mem_radicalLayer p π n)⟩
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
      have ha : finiteKummerExponent p π n hπ
          (infiniteLayerRestriction p π hπ n σ) = 0 := by
        rw [← padicKummerExponent_toZModPow, hσ, map_zero]
      have h := finiteKummerExponent_spec p π n hπ (infiniteLayerRestriction p π hπ n σ)
      rw [ha, ZMod.val_zero, pow_zero, one_mul] at h
      have hh := congrArg
        (IntermediateField.inclusion (falseTateLayer_le_falseTateExtension p π n n)) h
      rw [infiniteLayerRestriction_commutes] at hh
      exact hh
    exact AlgHom.congr_fun heq ⟨y.val, hn⟩

/-- Pure units in the actual affine image pull back to the actual radical fixer. -/
theorem falseTateAffineEquiv_mem_pureUnits (hπ : π ≠ 0) (σ : Γ) :
    falseTateAffineEquiv p π hπ σ ∈ affinePureUnits (falseTateAffineImage p π hπ) ↔
      σ ∈ falseTateKummerFixing p π := by
  rw [mem_affinePureUnits, mem_falseTateKummerFixing_iff p π hπ]
  rfl

/-- The actual radical fixer becomes exactly the pure-unit subgroup in
the original closed affine image. -/
theorem falseTateKummerFixing_map_affine (hπ : π ≠ 0) :
    (falseTateKummerFixing p π).map (falseTateAffineEquiv p π hπ).toMonoidHom =
      affinePureUnits (falseTateAffineImage p π hπ) := by
  ext g
  obtain ⟨σ, rfl⟩ := (falseTateAffineEquiv p π hπ).surjective g
  constructor
  · rintro ⟨τ, hτ, heq⟩
    have hτσ := (falseTateAffineEquiv p π hπ).injective heq
    subst τ
    exact (falseTateAffineEquiv_mem_pureUnits p π hπ σ).mpr hτ
  · intro hσ
    exact ⟨σ, (falseTateAffineEquiv_mem_pureUnits p π hπ σ).mp hσ, rfl⟩

variable [Algebra (Padic p) K] [FiniteDimensional (Padic p) K]

/-- The actual affine unit projection has infinite image for every finite
p-adic base, including the dyadic case. -/
theorem falseTateAffineImage_projection_infinite (hπ : π ≠ 0) :
    Infinite (affineProjection (falseTateAffineImage p π hπ)).range := by
  rw [falseTateAffineImage_projection_range]
  let := padicUnits_infinite p
  let H := (cyclotomicExtensionCharacter (K := K) p).range
  rcases finite_or_infinite H with hfin | hinf
  · let := hfin
    have hprod := H.card_mul_index
    rw [show Nat.card ((PadicInt p)ˣ) = 0 from Nat.card_eq_zero_of_infinite] at hprod
    have hpos : 0 < Nat.card H * H.index :=
      Nat.mul_pos Nat.card_pos (cyclotomicExtensionCharacter_index_pos p)
    exact False.elim (hpos.ne' hprod)
  · exact hinf

omit [Algebra (Padic p) K] [FiniteDimensional (Padic p) K] in
/-- The actual character is faithful when the actual translation kernel vanishes. -/
theorem padicCyclotomicCharacter_injective_of_translationKernel_eq_bot
    (hπ : π ≠ 0)
    (hM : (affineTranslationKernel (falseTateAffineImage p π hπ)).toAddSubgroup = ⊥) :
    Function.Injective (padicCyclotomicCharacter p π) := by
  have hi : Function.Injective ((affineProjection (falseTateAffineImage p π hπ)).comp
      (falseTateAffineEquiv p π hπ).toMonoidHom) :=
    (affineProjection_injective_of_translationKernel_eq_bot _ hM).comp
      (falseTateAffineEquiv p π hπ).injective
  rw [falseTateAffineEquiv_projection] at hi
  exact hi

omit [Algebra (Padic p) K] [FiniteDimensional (Padic p) K] in
/-- The original cyclotomic inclusion has trivial fixing subgroup when the
actual translation kernel vanishes. -/
theorem falseTate_cyclotomicFixing_eq_bot_of_translationKernel_eq_bot
    (hπ : π ≠ 0)
    (hM : (affineTranslationKernel (falseTateAffineImage p π hπ)).toAddSubgroup = ⊥) :
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
  apply padicCyclotomicCharacter_injective_of_translationKernel_eq_bot p π hπ hM
  calc
    _ = cyclotomicExtensionCharacter p (cyclotomicRestriction p π g) :=
      congrArg (fun f => f g) (padicCyclotomicCharacter_eq_comp p π)
    _ = 1 := by rw [hρ, map_one]
    _ = _ := (map_one _).symm

omit [Algebra (Padic p) K] [FiniteDimensional (Padic p) K] in
/-- A vanishing actual translation kernel makes the original false Tate
field equal to its actual cyclotomic subfield, by infinite Galois correspondence. -/
theorem falseTateExtension_eq_cyclotomicExtension_of_translationKernel_eq_bot
    (hπ : π ≠ 0)
    (hM : (affineTranslationKernel (falseTateAffineImage p π hπ)).toAddSubgroup = ⊥) :
    falseTateExtension p π = cyclotomicExtension (K := K) p := by
  have := falseTateExtension_isGalois p π hπ
  exact intermediateField_eq_of_inclusion_fixing_eq_bot
    (cyclotomicExtension_le_falseTateExtension p π)
    (falseTate_cyclotomicFixing_eq_bot_of_translationKernel_eq_bot p π hπ hM)

end AffineImage

section UpperProducts

variable {K : Type*} [NontriviallyNormedField K] [IsCompleteDiscreteValuedField K]
    [PerfectField (IsLocalRing.ResidueField
      (NormedField.valuation (K := K)).valuationSubring)] [CharZero K]

private theorem apfSubgroup_map_eq_comap_upper_infinite
    (E : IntermediateField K (SeparableClosure K)) [IsGalois K E]
    (M : IntermediateField K E) {u : ℝ} (hu : -1 ≤ u) :
    apfSubgroup K (M.map E.val) u =
      (M.fixingSubgroup ⊔ upperRamificationGroupInfinite K E u).comap
        (AlgEquiv.restrictNormalHom E) := by
  let ρ : (SeparableClosure K ≃ₐ[K] SeparableClosure K) →* (E ≃ₐ[K] E) :=
    AlgEquiv.restrictNormalHom E
  have hfix : (M.map E.val).fixingSubgroup = M.fixingSubgroup.comap ρ :=
    IntermediateField.map_fixingSubgroup (F := K) (E := E)
      (E' := SeparableClosure K) (L := M)
  have hker : E.fixingSubgroup ≤ M.fixingSubgroup.comap ρ := by
    rw [← IntermediateField.restrictNormalHom_ker E]
    intro g hg
    change ρ g ∈ M.fixingSubgroup
    rw [MonoidHom.mem_ker.mp hg]
    exact M.fixingSubgroup.one_mem
  unfold apfSubgroup
  rw [hfix]
  calc
    _ = M.fixingSubgroup.comap ρ ⊔
        (E.fixingSubgroup ⊔ absoluteUpperRamificationGroup K u) := by
      rw [← sup_assoc, sup_eq_left.mpr hker]
    _ = M.fixingSubgroup.comap ρ ⊔
        (upperRamificationGroupInfinite K E u).comap ρ := by
      rw [← apfSubgroup, apfSubgroup_eq_comap_upperInfinite K E hu]
    _ = _ := Subgroup.comap_sup_eq ρ _ _
      (AlgEquiv.restrictNormalHom_surjective (F := K) (K₁ := E) (SeparableClosure K))

variable (p : ℕ) [Fact p.Prime] (π : K)

/-- Actual infinite upper restriction identifies the full APF product
index of any subfield of the original false Tate field. The subfield may
be nonnormal and infinite, and its residue factor is retained. -/
theorem apfSubgroup_fieldRange_index_eq_falseTateFixing_sup_upper
    (hπ : π ≠ 0) (M : IntermediateField K (falseTateExtension p π))
    (j : falseTateExtension p π →ₐ[K] SeparableClosure K) {u : ℝ} (hu : -1 ≤ u) :
    (apfSubgroup K (j.comp M.val).fieldRange u).index =
      (M.fixingSubgroup ⊔ upperRamificationGroupInfinite K (falseTateExtension p π) u).index := by
  have := falseTateExtension_isGalois p π hπ
  let e := j.equivFieldRange
  let : IsGalois K j.fieldRange := IsGalois.of_algEquiv e
  have hr : (j.comp M.val).fieldRange = (M.map e.toAlgHom).map j.fieldRange.val := by
    rw [IntermediateField.fieldRange_comp_val, IntermediateField.map_map]
    rfl
  rw [hr, apfSubgroup_map_eq_comap_upper_infinite j.fieldRange (M.map e.toAlgHom) hu,
    Subgroup.index_comap_of_surjective _
      (AlgEquiv.restrictNormalHom_surjective (F := K) (K₁ := j.fieldRange) (SeparableClosure K)),
    ← fixingSubgroup_map_autCongr e M,
    ← upperRamificationGroupInfinite_map_autCongr K e hu, ← Subgroup.map_sup]
  exact Subgroup.index_map_equiv _ e.autCongr

/-- Naturality of the actual cyclotomic character identifies the upper
character images of the original false Tate and cyclotomic fields. -/
theorem falseTateCharacter_map_upperRamificationGroupInfinite
    (hπ : π ≠ 0) {u : ℝ} (hu : -1 ≤ u) :
    (upperRamificationGroupInfinite K (falseTateExtension p π) u).map
        (padicCyclotomicCharacter p π) =
      (upperRamificationGroupInfinite K (cyclotomicExtension (K := K) p) u).map
        (cyclotomicExtensionCharacter p) := by
  have := falseTateExtension_isGalois p π hπ
  rw [← restrictNormalHom_map_upperRamificationGroupInfinite K (AlgebraicClosure K)
      (falseTateExtension p π) u hu, Subgroup.map_map,
    cyclotomicExtension_map_upper_from_algebraicClosure (F := K) p hu]
  congr 1
  apply MonoidHom.ext
  intro τ
  exact cyclotomicCharacter_eq_of_intertwines p
    (algebraMap (falseTateExtension p π) (AlgebraicClosure K))
    (τ.restrictNormal (falseTateExtension p π)).toRingEquiv τ.toRingEquiv
    (AlgEquiv.restrictNormal_commutes τ (falseTateExtension p π))

/-- Ordinary restriction from the actual false Tate extension sends its
actual upper group onto the upper group of its original cyclotomic field. -/
theorem cyclotomicRestriction_map_upperRamificationGroupInfinite
    (hπ : π ≠ 0) {u : ℝ} (hu : -1 ≤ u) :
    (upperRamificationGroupInfinite K (falseTateExtension p π) u).map
        (cyclotomicRestriction p π) =
      upperRamificationGroupInfinite K (cyclotomicExtension (K := K) p) u := by
  have h := falseTateCharacter_map_upperRamificationGroupInfinite p π hπ hu
  rw [padicCyclotomicCharacter_eq_comp, ← Subgroup.map_map] at h
  exact le_antisymm
    ((Subgroup.map_le_map_iff_of_injective (cyclotomicExtensionCharacter_injective p)).mp h.le)
    ((Subgroup.map_le_map_iff_of_injective (cyclotomicExtensionCharacter_injective p)).mp h.ge)

variable [Algebra (Padic p) K] [FiniteDimensional (Padic p) K]

/-- The unit projection index of the actual affine upper group equals
the full upper index of the original cyclotomic extension. -/
theorem falseTateAffine_upper_projection_index (hπ : π ≠ 0) {u : ℝ} (hu : -1 ≤ u) :
    (((upperRamificationGroupInfinite K (falseTateExtension p π) u).map
        (falseTateAffineEquiv p π hπ).toMonoidHom).map
          (affineProjection (falseTateAffineImage p π hπ)).rangeRestrict).index =
      (upperRamificationGroupInfinite K (cyclotomicExtension (K := K) p) u).index := by
  let U := upperRamificationGroupInfinite K (falseTateExtension p π) u
  let V := upperRamificationGroupInfinite K (cyclotomicExtension (K := K) p) u
  let e := falseTateAffineEquiv p π hπ
  let q := affineProjection (falseTateAffineImage p π hπ)
  let J := (U.map e.toMonoidHom).map q.rangeRestrict
  have hJ : J.map q.range.subtype = U.map (padicCyclotomicCharacter p π) := by
    rw [Subgroup.map_map, Subgroup.map_map]
    rfl
  have hχ : U.map (padicCyclotomicCharacter p π) =
      V.map (cyclotomicExtensionCharacter p) := by
    rw [padicCyclotomicCharacter_eq_comp, ← Subgroup.map_map,
      cyclotomicRestriction_map_upperRamificationGroupInfinite p π hπ hu]
  have hJi := J.index_map q.range.subtype
  rw [(MonoidHom.ker_eq_bot_iff _).mpr Subtype.val_injective, sup_bot_eq,
    Subgroup.range_subtype] at hJi
  have hVi := V.index_map (cyclotomicExtensionCharacter (K := K) p)
  rw [(MonoidHom.ker_eq_bot_iff _).mpr (cyclotomicExtensionCharacter_injective p),
    sup_bot_eq] at hVi
  apply Nat.eq_of_mul_eq_mul_right (cyclotomicExtensionCharacter_index_pos (K := K) p)
  calc
    J.index * (cyclotomicExtensionCharacter (K := K) p).range.index =
        J.index * q.range.index :=
      congrArg (fun n : ℕ => J.index * n)
        (congrArg (fun H : Subgroup ((PadicInt p)ˣ) => H.index)
          (falseTateAffineImage_projection_range p π hπ)).symm
    _ = (J.map q.range.subtype).index := hJi.symm
    _ = (V.map (cyclotomicExtensionCharacter p)).index := by rw [hJ, hχ]
    _ = V.index * (cyclotomicExtensionCharacter (K := K) p).range.index := hVi

end UpperProducts

section RadicalIndex

variable {K : Type*} [NontriviallyNormedField K] [IsCompleteDiscreteValuedField K]
    [PerfectField (IsLocalRing.ResidueField
      (NormedField.valuation (K := K)).valuationSubring)] [CharZero K]
variable (p : ℕ) [Fact p.Prime]
variable {π : (NormedField.valuation (K := K)).valuationSubring}

/-- The actual pure-unit product index is exactly the intrinsic radical
index. Total ramification of the radical tower removes its residue factor;
no total ramification of the false Tate field is used. -/
theorem falseTateAffine_upper_radical_index (hπ : Irreducible π)
    (he : 0 < (IsDiscreteValuationRing.addVal
      (NormedField.valuation (K := K)).valuationSubring
      (p : (NormedField.valuation (K := K)).valuationSubring)).toNat)
    {u : ℝ} (hu : 0 ≤ u) :
    let hπ₀ : (π : K) ≠ 0 := fun h => hπ.ne_zero (Subtype.ext h)
    (affinePureUnits (falseTateAffineImage p (π : K) hπ₀) ⊔
      (upperRamificationGroupInfinite K (falseTateExtension p (π : K)) u).map
        (falseTateAffineEquiv p (π : K) hπ₀).toMonoidHom).index =
      apfIndex K (kummerExtension p (π : K)) u := by
  let hπ₀ : (π : K) ≠ 0 := fun h => hπ.ne_zero (Subtype.ext h)
  let i := falseTateKummerInclusion p (π : K)
  let M := i.fieldRange
  let e := falseTateAffineEquiv p (π : K) hπ₀
  let j : falseTateExtension p (π : K) →ₐ[K] SeparableClosure K := IsSepClosed.lift
  have hr : (j.comp M.val).fieldRange = (j.comp i).fieldRange := by
    ext z
    constructor
    · rintro ⟨m, rfl⟩
      obtain ⟨y, hy⟩ := m.property
      exact ⟨y, congrArg j hy⟩
    · rintro ⟨y, rfl⟩
      exact ⟨⟨i y, ⟨y, rfl⟩⟩, rfl⟩
  have hfix : M.fixingSubgroup.map e.toMonoidHom =
      affinePureUnits (falseTateAffineImage p (π : K) hπ₀) :=
    falseTateKummerFixing_map_affine p (π : K) hπ₀
  calc
    _ = ((M.fixingSubgroup ⊔
        upperRamificationGroupInfinite K (falseTateExtension p (π : K)) u).map
          e.toMonoidHom).index := by rw [Subgroup.map_sup, hfix]
    _ = (M.fixingSubgroup ⊔
        upperRamificationGroupInfinite K (falseTateExtension p (π : K)) u).index :=
      Subgroup.index_map_equiv _ e.toMulEquiv
    _ = (apfSubgroup K (j.comp M.val).fieldRange u).index :=
      (apfSubgroup_fieldRange_index_eq_falseTateFixing_sup_upper p (π : K) hπ₀ M j
        (by linarith : -1 ≤ u)).symm
    _ = _ := by
      rw [hr]
      exact kummerExtension_apfSubgroup_fieldRange_index p hπ he (j.comp i) hu

end RadicalIndex

section FiniteBase

variable {K : Type*} [NontriviallyNormedField K] [IsCompleteDiscreteValuedField K]
    [PerfectField (IsLocalRing.ResidueField
      (NormedField.valuation (K := K)).valuationSubring)] [CharZero K]
variable (p : ℕ) [Fact p.Prime] [NormedAlgebra (Padic p) K]
    [FiniteDimensional (Padic p) K]
variable {π : (NormedField.valuation (K := K)).valuationSubring}

omit [PerfectField (IsLocalRing.ResidueField
  (NormedField.valuation (K := K)).valuationSubring)] [CharZero K]
  [FiniteDimensional (Padic p) K] in
private theorem falseTateBase_addVal_p_pos :
    0 < (IsDiscreteValuationRing.addVal
      (NormedField.valuation (K := K)).valuationSubring
      (p : (NormedField.valuation (K := K)).valuationSubring)).toNat := by
  rw [addVal_p_toNat_eq_padic_ramificationIdx p]
  exact local_ramificationIdx_pos
    (NormedField.valuation (K := Padic p)).valuationSubring
    (NormedField.valuation (K := K)).valuationSubring

/-- If the actual translation kernel is nonzero, the full false Tate upper
index is finite and uniformly comparable with the original radical and
cyclotomic indices. The constants depend only on the actual affine image. -/
theorem exists_falseTate_upper_index_comparison (hπ : Irreducible π)
    (hM : (affineTranslationKernel (falseTateAffineImage p (π : K)
      (fun h => hπ.ne_zero (Subtype.ext h)))).toAddSubgroup ≠ ⊥) :
    ∃ C D : ℕ, 0 < C ∧ 0 < D ∧ ∀ u : ℝ, 0 ≤ u →
      (upperRamificationGroupInfinite K (falseTateExtension p (π : K)) u).FiniteIndex ∧
      apfIndex K (kummerExtension p (π : K)) u *
          (upperRamificationGroupInfinite K (cyclotomicExtension (K := K) p) u).index ≤
        D * (upperRamificationGroupInfinite K (falseTateExtension p (π : K)) u).index ∧
      (upperRamificationGroupInfinite K (falseTateExtension p (π : K)) u).index ≤
        C * apfIndex K (kummerExtension p (π : K)) u *
          (upperRamificationGroupInfinite K (cyclotomicExtension (K := K) p) u).index := by
  let hπ₀ : (π : K) ≠ 0 := fun h => hπ.ne_zero (Subtype.ext h)
  let G := falseTateAffineImage p (π : K) hπ₀
  let e := falseTateAffineEquiv p (π : K) hπ₀
  have := falseTateExtension_isGalois p (π : K) hπ₀
  let : Infinite (affineProjection G).range :=
    falseTateAffineImage_projection_infinite p (π : K) hπ₀
  obtain ⟨C, D, hC, hD, hcomp⟩ := affineIndex_comparison G hM
  refine ⟨C, D, hC, hD, fun u hu => ?_⟩
  let U := upperRamificationGroupInfinite K (falseTateExtension p (π : K)) u
  let I := U.map e.toMonoidHom
  let : I.Normal := Subgroup.Normal.map inferInstance e.toMonoidHom e.surjective
  have hclosed : IsClosed (I : Set G) :=
    ((isCompact_upperRamificationGroupInfinite K (falseTateExtension p (π : K)) u).image
      e.continuous).isClosed
  have hA : (affinePureUnits G ⊔ I).index = apfIndex K (kummerExtension p (π : K)) u :=
    falseTateAffine_upper_radical_index p hπ (falseTateBase_addVal_p_pos p) hu
  have hB : (I.map (affineProjection G).rangeRestrict).index =
      (upperRamificationGroupInfinite K (cyclotomicExtension (K := K) p) u).index :=
    falseTateAffine_upper_projection_index p (π : K) hπ₀ (by linarith : -1 ≤ u)
  have hAfin : (affinePureUnits G ⊔ I).FiniteIndex := by
    rw [Subgroup.finiteIndex_iff, hA]
    have := isAPF_kummerExtension p hπ
    exact Nat.ne_of_gt (IsAPF.apfIndex_pos K (kummerExtension p (π : K)) hu)
  have hBfin : (I.map (affineProjection G).rangeRestrict).FiniteIndex := by
    rw [Subgroup.finiteIndex_iff, hB]
    let := (isAPF_iff_upperInfinite_finiteIndex K _).mp
      (isAPF_cyclotomicExtension p K) u (by linarith)
    exact Subgroup.FiniteIndex.index_ne_zero
  obtain ⟨hIfin, _, hlo, hhi⟩ := hcomp I hclosed hAfin hBfin
  have hindex : I.index = U.index := Subgroup.index_map_equiv U e.toMulEquiv
  refine ⟨?_, ?_, ?_⟩
  · rw [Subgroup.finiteIndex_iff, ← hindex]
    exact hIfin.index_ne_zero
  · simpa only [hA, hB, hindex] using hlo
  · simpa only [hA, hB, hindex] using hhi

/-- If the actual translation kernel vanishes, the full upper index is
exactly the original cyclotomic upper index. -/
theorem falseTate_upper_index_of_translationKernel_eq_bot (hπ : Irreducible π)
    (hM : (affineTranslationKernel (falseTateAffineImage p (π : K)
      (fun h => hπ.ne_zero (Subtype.ext h)))).toAddSubgroup = ⊥)
    {u : ℝ} (hu : -1 ≤ u) :
    (upperRamificationGroupInfinite K (falseTateExtension p (π : K)) u).index =
      (upperRamificationGroupInfinite K (cyclotomicExtension (K := K) p) u).index := by
  let hπ₀ : (π : K) ≠ 0 := fun h => hπ.ne_zero (Subtype.ext h)
  let G := falseTateAffineImage p (π : K) hπ₀
  let e := falseTateAffineEquiv p (π : K) hπ₀
  let U := upperRamificationGroupInfinite K (falseTateExtension p (π : K)) u
  calc
    U.index = (U.map e.toMonoidHom).index := (Subgroup.index_map_equiv U e.toMulEquiv).symm
    _ = ((U.map e.toMonoidHom).map (affineProjection G).rangeRestrict).index :=
      (affineProjection_index_of_translationKernel_eq_bot G hM _).symm
    _ = _ := falseTateAffine_upper_projection_index p (π : K) hπ₀ hu

/-- The original false Tate extension is APF over every finite
norm-compatible `p`-adic base, including the prime two. -/
theorem isAPF_falseTateExtension (hπ : Irreducible π) :
    IsAPF K (falseTateExtension p (π : K)) := by
  let hπ₀ : (π : K) ≠ 0 := fun h => hπ.ne_zero (Subtype.ext h)
  have := falseTateExtension_isGalois p (π : K) hπ₀
  have hnonneg (u : ℝ) (hu : 0 ≤ u) :
      (upperRamificationGroupInfinite K (falseTateExtension p (π : K)) u).FiniteIndex := by
    by_cases hM : (affineTranslationKernel (falseTateAffineImage p (π : K) hπ₀)).toAddSubgroup = ⊥
    · rw [Subgroup.finiteIndex_iff, falseTate_upper_index_of_translationKernel_eq_bot p hπ hM
        (by linarith : -1 ≤ u)]
      let := (isAPF_iff_upperInfinite_finiteIndex K _).mp
        (isAPF_cyclotomicExtension p K) u (by linarith)
      exact Subgroup.FiniteIndex.index_ne_zero
    · obtain ⟨C, D, _, _, hcomp⟩ := exists_falseTate_upper_index_comparison p hπ hM
      exact (hcomp u hu).1
  apply (isAPF_iff_upperInfinite_finiteIndex K _).mpr
  intro u hu
  by_cases h : 0 ≤ u
  · exact hnonneg u h
  · let := hnonneg 0 le_rfl
    exact Subgroup.finiteIndex_of_le
      (upperRamificationGroupInfinite_antitoneOn K (falseTateExtension p (π : K))
        hu (by norm_num : -1 ≤ (0 : ℝ)) (le_of_not_ge h))

/-- The full original false Tate upper index has bounded growth across
the actual positive ramification-index shift of the base. -/
theorem exists_falseTate_upper_index_boundedGrowth (hπ : Irreducible π) :
    ∃ Q : ℕ, 0 < Q ∧ ∃ V : ℝ, 0 ≤ V ∧ ∀ u : ℝ, V ≤ u →
      (upperRamificationGroupInfinite K (falseTateExtension p (π : K))
        (u + ((IsDiscreteValuationRing.addVal
          (NormedField.valuation (K := K)).valuationSubring
          (p : (NormedField.valuation (K := K)).valuationSubring)).toNat : ℝ))).index ≤
        Q * (upperRamificationGroupInfinite K (falseTateExtension p (π : K)) u).index := by
  let hπ₀ : (π : K) ≠ 0 := fun h => hπ.ne_zero (Subtype.ext h)
  let a := (IsDiscreteValuationRing.addVal
    (NormedField.valuation (K := K)).valuationSubring
    (p : (NormedField.valuation (K := K)).valuationSubring)).toNat
  obtain ⟨V, hV, hcyc⟩ :=
    exists_upperRamificationGroupInfinite_cyclotomic_index_add_ramificationIdx p K
  have hB (u : ℝ) (hu : V ≤ u) :
      (upperRamificationGroupInfinite K (cyclotomicExtension (K := K) p)
        (u + (a : ℝ))).index =
        p * (upperRamificationGroupInfinite K (cyclotomicExtension (K := K) p) u).index := by
    simpa only [a, addVal_p_toNat_eq_padic_ramificationIdx p] using hcyc u hu
  by_cases hM : (affineTranslationKernel (falseTateAffineImage p (π : K) hπ₀)).toAddSubgroup = ⊥
  · refine ⟨p, (Fact.out : p.Prime).pos, V, hV, fun u hu => ?_⟩
    rw [falseTate_upper_index_of_translationKernel_eq_bot p hπ hM
      (by linarith [show (0 : ℝ) ≤ (a : ℝ) from Nat.cast_nonneg a] : -1 ≤ u + (a : ℝ)),
      falseTate_upper_index_of_translationKernel_eq_bot p hπ hM
        (by linarith : -1 ≤ u), hB u hu]
  · obtain ⟨C, D, hC, hD, hcomp⟩ := exists_falseTate_upper_index_comparison p hπ hM
    refine ⟨C * D * p ^ 2, Nat.mul_pos (Nat.mul_pos hC hD)
      (pow_pos (Fact.out : p.Prime).pos _), V, hV, fun u hu => ?_⟩
    have hu₀ : 0 ≤ u := hV.trans hu
    have hshift := (hcomp (u + (a : ℝ)) (add_nonneg hu₀ (Nat.cast_nonneg a))).2.2
    have hA := kummerExtension_apfIndex_growth p hπ (falseTateBase_addVal_p_pos p) hu₀
    calc
      _ ≤ C * apfIndex K (kummerExtension p (π : K)) (u + (a : ℝ)) *
          (upperRamificationGroupInfinite K (cyclotomicExtension (K := K) p)
            (u + (a : ℝ))).index := hshift
      _ ≤ C * (p * apfIndex K (kummerExtension p (π : K)) u) *
          (p * (upperRamificationGroupInfinite K (cyclotomicExtension (K := K) p) u).index) := by
        rw [hB u hu]
        exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left C hA)
      _ = (C * p * p) * (apfIndex K (kummerExtension p (π : K)) u *
          (upperRamificationGroupInfinite K (cyclotomicExtension (K := K) p) u).index) := by ring
      _ ≤ (C * p * p) * (D *
          (upperRamificationGroupInfinite K (falseTateExtension p (π : K)) u).index) :=
        Nat.mul_le_mul_left _ (hcomp u hu₀).2.1
      _ = _ := by ring

omit [NormedAlgebra (Padic p) K] [FiniteDimensional (Padic p) K] in
/-- The actual full upper index retains the fixed inertia index as a
factor. This identity allows a finite initial residue extension. -/
theorem falseTate_upper_index_eq_apfIndex_mul_inertia_index (hπ : Irreducible π)
    {u : ℝ} (hu : 0 ≤ u) :
    (upperRamificationGroupInfinite K (falseTateExtension p (π : K)) u).index =
      apfIndex K (falseTateExtension p (π : K)) u *
        (upperRamificationGroupInfinite K (falseTateExtension p (π : K)) 0).index := by
  have := falseTateExtension_isGalois p (π : K)
    (fun h => hπ.ne_zero (Subtype.ext h))
  rw [apfIndex_eq_upperInfiniteRelIndex K _ hu]
  exact (Subgroup.relIndex_mul_index
    (upperRamificationGroupInfinite_antitoneOn K _
      (by norm_num : -1 ≤ (0 : ℝ)) (by linarith : -1 ≤ u) hu)).symm

/-- Cancelling the positive finite inertia factor gives bounded growth of
the intrinsic false Tate index over its original base. -/
theorem exists_falseTate_apfIndex_boundedGrowth (hπ : Irreducible π) :
    ∃ Q : ℕ, 0 < Q ∧ ∃ V : ℝ, 0 ≤ V ∧ ∀ u : ℝ, V ≤ u →
      apfIndex K (falseTateExtension p (π : K))
        (u + ((IsDiscreteValuationRing.addVal
          (NormedField.valuation (K := K)).valuationSubring
          (p : (NormedField.valuation (K := K)).valuationSubring)).toNat : ℝ)) ≤
        Q * apfIndex K (falseTateExtension p (π : K)) u := by
  have := falseTateExtension_isGalois p (π : K)
    (fun h => hπ.ne_zero (Subtype.ext h))
  let := (isAPF_iff_upperInfinite_finiteIndex K _).mp
    (isAPF_falseTateExtension p hπ) 0 (by norm_num)
  have hzero : 0 < (upperRamificationGroupInfinite K (falseTateExtension p (π : K)) 0).index :=
    Nat.pos_of_ne_zero Subgroup.FiniteIndex.index_ne_zero
  obtain ⟨Q, hQ, V, hV, hfull⟩ := exists_falseTate_upper_index_boundedGrowth p hπ
  refine ⟨Q, hQ, V, hV, fun u hu => ?_⟩
  have hg := hfull u hu
  rw [falseTate_upper_index_eq_apfIndex_mul_inertia_index p hπ
      (add_nonneg (hV.trans hu) (Nat.cast_nonneg _)),
    falseTate_upper_index_eq_apfIndex_mul_inertia_index p hπ (hV.trans hu),
    ← Nat.mul_assoc] at hg
  exact (mul_le_mul_iff_left₀ hzero).mp hg

/-- Every actual false Tate extension over a finite norm-compatible
`p`-adic base is strictly APF, including the prime two and a finite initial
residue extension. -/
theorem isStrictlyAPF_falseTateExtension (hπ : Irreducible π) :
    IsStrictlyAPF K (falseTateExtension p (π : K)) := by
  obtain ⟨Q, hQ, V, _, hgrowth⟩ := exists_falseTate_apfIndex_boundedGrowth p hπ
  have := isAPF_falseTateExtension p hπ
  apply isStrictlyAPF_of_apfIndex_boundedGrowth K _ (U := V)
    (Nat.cast_pos.mpr (falseTateBase_addVal_p_pos (K := K) p)) (Nat.cast_pos.mpr hQ)
  intro u hu
  exact_mod_cast hgrowth u hu

end FiniteBase

section CanonicalFiniteBase

variable (p : ℕ) [Fact p.Prime]
variable (K : Type*) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
    [CharZero K] [NormedAlgebra (Padic p) K] [FiniteDimensional (Padic p) K]
variable (π : (NormedField.valuation (K := K)).valuationSubring)

/-- Over an arbitrary finite norm-compatible `p`-adic base, the canonical
unit-ball DVR structure and its actual perfect residue field supply every
valued-field hypothesis of false Tate strictness. -/
theorem isStrictlyAPF_falseTateExtension_of_finiteDimensional (hπ : Irreducible π) :
    letI := cyclotomicBase_isCompleteDiscreteValuedField p K
    IsStrictlyAPF K (falseTateExtension p (π : K)) := by
  let := cyclotomicBase_isCompleteDiscreteValuedField p K
  let := normedAlgebra_residueField_perfectField (Padic p) K
  exact isStrictlyAPF_falseTateExtension p hπ

/-- Canonical public APF over every finite norm-compatible `p`-adic base,
without a separate chosen DVR or perfect-residue hypothesis. -/
theorem isAPF_falseTateExtension_of_finiteDimensional (hπ : Irreducible π) :
    letI := cyclotomicBase_isCompleteDiscreteValuedField p K
    IsAPF K (falseTateExtension p (π : K)) := by
  let := cyclotomicBase_isCompleteDiscreteValuedField p K
  exact (isStrictlyAPF_falseTateExtension_of_finiteDimensional p K π hπ).toIsAPF

end CanonicalFiniteBase

end FalseTateExtension
