/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FalseTateExtension.Affine.Index
public import FalseTateExtension.Cyclotomic.APF
public import FalseTateExtension.Cyclotomic.InertiaImage
public import FalseTateExtension.FalseTate.AffineImage
public import FalseTateExtension.Kummer.APF
public import FalseTateExtension.Mathlib.FieldTheory.Galois.InfiniteCorrespondence
public import FontaineWintenberger.APF.Galois
public import FontaineWintenberger.APF.Galois.Restriction

/-!
# The false Tate extension is strictly APF

For a finite extension `K/ℚ_p` with uniformizer `π`, `K_FT = K(π^{1/p^∞}, ζ_{p^∞})` is strictly
arithmetically profinite over `K`. The indices of the upper ramification groups of `K_FT/K` are
compared with those of `K_cyc/K` and `K_Kum/K` through the affine image, and the bounded growth of
the latter gives the APF condition and the strict bound.

## References

* Wintenberger, *Le corps des normes de certaines extensions infinies de corps locaux;
  applications*, §1.2.
-/

@[expose] public section

noncomputable section

namespace FalseTateExtension

open FontaineWintenberger

section UpperProducts

variable {K : Type*} [NontriviallyNormedField K] [IsCompleteDiscreteValuedField K]
    [PerfectField (𝓀[K])] [CharZero K]

variable (p : ℕ) [Fact p.Prime] (π : K)

/-- Infinite upper restriction identifies the full APF product
index of any subfield of the false Tate field. The subfield may
be nonnormal and infinite, and its residue factor is retained. -/
theorem apfSubgroup_fieldRange_index_eq_falseTateFixing_sup_upper
    [hπ : NeZero π] (M : IntermediateField K (falseTateExtension p π))
    (j : falseTateExtension p π →ₐ[K] SeparableClosure K) {u : ℝ} (hu : -1 ≤ u) :
    (apfSubgroup K (j.comp M.val).fieldRange u).index =
      (M.fixingSubgroup ⊔ upperRamificationGroupInfinite K (falseTateExtension p π) u).index := by
  have := falseTateExtension_isGalois p π
  let e := j.equivFieldRange
  let : IsGalois K j.fieldRange := IsGalois.of_algEquiv e
  have hr : (j.comp M.val).fieldRange = (M.map e.toAlgHom).map j.fieldRange.val := by
    rw [IntermediateField.fieldRange_comp_val, IntermediateField.map_map]
    rfl
  rw [hr, apfSubgroup_map_eq_comap_upperRamificationGroupInfinite K j.fieldRange
    (M.map e.toAlgHom) hu,
    Subgroup.index_comap_of_surjective _
      (AlgEquiv.restrictNormalHom_surjective (F := K) (K₁ := j.fieldRange) (SeparableClosure K)),
    ← fixingSubgroup_map_autCongr e M,
    ← upperRamificationGroupInfinite_map_autCongr K e hu, ← Subgroup.map_sup]
  exact Subgroup.index_map_equiv _ e.autCongr

/-- Naturality of the cyclotomic character identifies the upper
character images of the false Tate and cyclotomic fields. -/
theorem falseTateCharacter_map_upperRamificationGroupInfinite
    [hπ : NeZero π] {u : ℝ} (hu : -1 ≤ u) :
    (upperRamificationGroupInfinite K (falseTateExtension p π) u).map
        (padicCyclotomicCharacter p π) =
      (upperRamificationGroupInfinite K (cyclotomicExtension (K := K) p) u).map
        (cyclotomicExtensionCharacter p) := by
  have := falseTateExtension_isGalois p π
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

/-- Restriction from the false Tate extension sends its
upper group onto the upper group of its cyclotomic field. -/
theorem cyclotomicRestriction_map_upperRamificationGroupInfinite
    [hπ : NeZero π] {u : ℝ} (hu : -1 ≤ u) :
    (upperRamificationGroupInfinite K (falseTateExtension p π) u).map
        (cyclotomicRestriction p π) =
      upperRamificationGroupInfinite K (cyclotomicExtension (K := K) p) u := by
  have h := falseTateCharacter_map_upperRamificationGroupInfinite p π hu
  rw [padicCyclotomicCharacter_eq_comp, ← Subgroup.map_map] at h
  exact le_antisymm
    ((Subgroup.map_le_map_iff_of_injective (cyclotomicExtensionCharacter_injective p)).mp h.le)
    ((Subgroup.map_le_map_iff_of_injective (cyclotomicExtensionCharacter_injective p)).mp h.ge)

variable [Algebra (ℚ_[p]) K] [FiniteDimensional (ℚ_[p]) K]

/-- The unit projection index of the affine upper group equals
the full upper index of the cyclotomic extension. -/
theorem falseTateAffine_upper_projection_index [hπ : NeZero π] {u : ℝ} (hu : -1 ≤ u) :
    (((upperRamificationGroupInfinite K (falseTateExtension p π) u).map
        (falseTateGaloisEquivAffineImage p π).toMonoidHom).map
          (affineProjection (falseTateAffineImage p π)).rangeRestrict).index =
      (upperRamificationGroupInfinite K (cyclotomicExtension (K := K) p) u).index := by
  let U := upperRamificationGroupInfinite K (falseTateExtension p π) u
  let V := upperRamificationGroupInfinite K (cyclotomicExtension (K := K) p) u
  let e := falseTateGaloisEquivAffineImage p π
  let q := affineProjection (falseTateAffineImage p π)
  let J := (U.map e.toMonoidHom).map q.rangeRestrict
  have hJ : J.map q.range.subtype = U.map (padicCyclotomicCharacter p π) := by
    rw [Subgroup.map_map, Subgroup.map_map]
    rfl
  have hχ : U.map (padicCyclotomicCharacter p π) =
      V.map (cyclotomicExtensionCharacter p) := by
    rw [padicCyclotomicCharacter_eq_comp, ← Subgroup.map_map,
      cyclotomicRestriction_map_upperRamificationGroupInfinite p π hu]
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
        (congrArg (fun H : Subgroup ((ℤ_[p])ˣ) => H.index)
          (falseTateAffineImage_projection_range p π)).symm
    _ = (J.map q.range.subtype).index := hJi.symm
    _ = (V.map (cyclotomicExtensionCharacter p)).index := by rw [hJ, hχ]
    _ = V.index * (cyclotomicExtensionCharacter (K := K) p).range.index := hVi

end UpperProducts

section RadicalIndex

variable {K : Type*} [NontriviallyNormedField K] [IsCompleteDiscreteValuedField K]
    [PerfectField (𝓀[K])] [CharZero K]
variable (p : ℕ) [Fact p.Prime]
variable (π : 𝒪[K])

/-- The pure-unit product index is exactly the radical
index. Total ramification of the radical tower removes its residue factor;
no total ramification of the false Tate field is used. -/
theorem falseTateAffine_upper_pPowRoot_index [hπ : Fact (Irreducible π)]
    (he : 0 < (IsDiscreteValuationRing.addVal
      𝒪[K]
      (p : 𝒪[K])).toNat)
    {u : ℝ} (hu : 0 ≤ u) :
    (affinePureUnits (falseTateAffineImage p (π : K)) ⊔
      (upperRamificationGroupInfinite K (falseTateExtension p (π : K)) u).map
        (falseTateGaloisEquivAffineImage p (π : K)).toMonoidHom).index =
      apfIndex K (kummerExtension p (π : K)) u := by
  let hπ₀ : (π : K) ≠ 0 := fun h => hπ.out.ne_zero (Subtype.ext h)
  let i := falseTateKummerInclusion p (π : K)
  let M := i.fieldRange
  let e := falseTateGaloisEquivAffineImage p (π : K)
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
      affinePureUnits (falseTateAffineImage p (π : K)) :=
    falseTateKummerFixing_map_affine p (π : K)
  calc
    _ = ((M.fixingSubgroup ⊔
        upperRamificationGroupInfinite K (falseTateExtension p (π : K)) u).map
          e.toMonoidHom).index := by rw [Subgroup.map_sup, hfix]
    _ = (M.fixingSubgroup ⊔
        upperRamificationGroupInfinite K (falseTateExtension p (π : K)) u).index :=
      Subgroup.index_map_equiv _ e.toMulEquiv
    _ = (apfSubgroup K (j.comp M.val).fieldRange u).index :=
      (apfSubgroup_fieldRange_index_eq_falseTateFixing_sup_upper p (π : K) M j
        (by linarith : -1 ≤ u)).symm
    _ = _ := by
      rw [hr]
      exact kummerExtension_apfSubgroup_fieldRange_index p π he (j.comp i) hu

end RadicalIndex

section FiniteBase

variable {K : Type*} [NontriviallyNormedField K] [IsCompleteDiscreteValuedField K]
    [PerfectField (𝓀[K])] [CharZero K]
variable (p : ℕ) [Fact p.Prime] [NormedAlgebra (ℚ_[p]) K]
    [FiniteDimensional (ℚ_[p]) K]
variable (π : 𝒪[K])

omit [PerfectField (𝓀[K])] [CharZero K]
  [FiniteDimensional (ℚ_[p]) K] in
theorem falseTateBase_addVal_p_pos :
    0 < (IsDiscreteValuationRing.addVal
      𝒪[K]
      (p : 𝒪[K])).toNat := by
  rw [addVal_p_toNat_eq_padic_ramificationIdx p]
  exact local_ramificationIdx_pos
    𝒪[ℚ_[p]]
    𝒪[K]

/-- If the translation kernel is nonzero, the full false Tate upper
index is finite and uniformly comparable with the radical and
cyclotomic indices. The constants depend only on the affine image. -/
theorem exists_falseTate_upper_index_comparison [hπ : Fact (Irreducible π)]
    (hM : (affineTranslationKernel (falseTateAffineImage p (π : K))).toAddSubgroup ≠ ⊥) :
    ∃ C D : ℕ, 0 < C ∧ 0 < D ∧ ∀ u : ℝ, 0 ≤ u →
      (upperRamificationGroupInfinite K (falseTateExtension p (π : K)) u).FiniteIndex ∧
      apfIndex K (kummerExtension p (π : K)) u *
          (upperRamificationGroupInfinite K (cyclotomicExtension (K := K) p) u).index ≤
        D * (upperRamificationGroupInfinite K (falseTateExtension p (π : K)) u).index ∧
      (upperRamificationGroupInfinite K (falseTateExtension p (π : K)) u).index ≤
        C * apfIndex K (kummerExtension p (π : K)) u *
          (upperRamificationGroupInfinite K (cyclotomicExtension (K := K) p) u).index := by
  let hπ₀ : (π : K) ≠ 0 := fun h => hπ.out.ne_zero (Subtype.ext h)
  let G := falseTateAffineImage p (π : K)
  let e := falseTateGaloisEquivAffineImage p (π : K)
  have := falseTateExtension_isGalois p (π : K)
  let : Infinite (affineProjection G).range :=
    falseTateAffineImage_projection_infinite p (π : K)
  obtain ⟨C, D, hC, hD, hcomp⟩ := affineIndex_comparison G hM
  refine ⟨C, D, hC, hD, fun u hu => ?_⟩
  let U := upperRamificationGroupInfinite K (falseTateExtension p (π : K)) u
  let I := U.map e.toMonoidHom
  let : I.Normal := Subgroup.Normal.map inferInstance e.toMonoidHom e.surjective
  have hclosed : IsClosed (I : Set G) :=
    ((isCompact_upperRamificationGroupInfinite K (falseTateExtension p (π : K)) u).image
      e.continuous).isClosed
  have hA : (affinePureUnits G ⊔ I).index = apfIndex K (kummerExtension p (π : K)) u :=
    falseTateAffine_upper_pPowRoot_index p π (falseTateBase_addVal_p_pos p) hu
  have hB : (I.map (affineProjection G).rangeRestrict).index =
      (upperRamificationGroupInfinite K (cyclotomicExtension (K := K) p) u).index :=
    falseTateAffine_upper_projection_index p (π : K) (by linarith : -1 ≤ u)
  have hAfin : (affinePureUnits G ⊔ I).FiniteIndex := by
    rw [Subgroup.finiteIndex_iff, hA]
    have := isAPF_kummerExtension p π
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

/-- If the translation kernel vanishes, the full upper index is
exactly the cyclotomic upper index. -/
theorem falseTate_upper_index_of_translationKernel_eq_bot [hπ : Fact (Irreducible π)]
    (hM : (affineTranslationKernel (falseTateAffineImage p (π : K))).toAddSubgroup = ⊥)
    {u : ℝ} (hu : -1 ≤ u) :
    (upperRamificationGroupInfinite K (falseTateExtension p (π : K)) u).index =
      (upperRamificationGroupInfinite K (cyclotomicExtension (K := K) p) u).index := by
  let hπ₀ : (π : K) ≠ 0 := fun h => hπ.out.ne_zero (Subtype.ext h)
  let G := falseTateAffineImage p (π : K)
  let e := falseTateGaloisEquivAffineImage p (π : K)
  let U := upperRamificationGroupInfinite K (falseTateExtension p (π : K)) u
  calc
    U.index = (U.map e.toMonoidHom).index := (Subgroup.index_map_equiv U e.toMulEquiv).symm
    _ = ((U.map e.toMonoidHom).map (affineProjection G).rangeRestrict).index :=
      (affineProjection_index_of_translationKernel_eq_bot G hM _).symm
    _ = _ := falseTateAffine_upper_projection_index p (π : K) hu

/-- The false Tate extension is APF over every finite
norm-compatible `p`-adic base, including the prime two. -/
instance isAPF_falseTateExtension [hπ : Fact (Irreducible π)] :
    IsAPF K (falseTateExtension p (π : K)) := by
  let hπ₀ : (π : K) ≠ 0 := fun h => hπ.out.ne_zero (Subtype.ext h)
  have := falseTateExtension_isGalois p (π : K)
  have hnonneg (u : ℝ) (hu : 0 ≤ u) :
      (upperRamificationGroupInfinite K (falseTateExtension p (π : K)) u).FiniteIndex := by
    by_cases hM : (affineTranslationKernel (falseTateAffineImage p (π : K))).toAddSubgroup = ⊥
    · rw [Subgroup.finiteIndex_iff, falseTate_upper_index_of_translationKernel_eq_bot p π hM
        (by linarith : -1 ≤ u)]
      let := (isAPF_iff_upperInfinite_finiteIndex K _).mp
        (isAPF_cyclotomicExtension p K) u (by linarith)
      exact Subgroup.FiniteIndex.index_ne_zero
    · obtain ⟨C, D, _, _, hcomp⟩ := exists_falseTate_upper_index_comparison p π hM
      exact (hcomp u hu).1
  apply (isAPF_iff_upperInfinite_finiteIndex K _).mpr
  intro u hu
  by_cases h : 0 ≤ u
  · exact hnonneg u h
  · let := hnonneg 0 le_rfl
    exact Subgroup.finiteIndex_of_le
      (upperRamificationGroupInfinite_antitoneOn K (falseTateExtension p (π : K))
        hu (by norm_num : -1 ≤ (0 : ℝ)) (le_of_not_ge h))

/-- The full false Tate upper index has bounded growth across
the positive ramification-index shift of the base. -/
theorem exists_falseTate_upper_index_boundedGrowth [hπ : Fact (Irreducible π)] :
    ∃ Q : ℕ, 0 < Q ∧ ∃ V : ℝ, 0 ≤ V ∧ ∀ u : ℝ, V ≤ u →
      (upperRamificationGroupInfinite K (falseTateExtension p (π : K))
        (u + ((IsDiscreteValuationRing.addVal
          𝒪[K]
          (p : 𝒪[K])).toNat : ℝ))).index ≤
        Q * (upperRamificationGroupInfinite K (falseTateExtension p (π : K)) u).index := by
  let hπ₀ : (π : K) ≠ 0 := fun h => hπ.out.ne_zero (Subtype.ext h)
  let a := (IsDiscreteValuationRing.addVal
    𝒪[K]
    (p : 𝒪[K])).toNat
  obtain ⟨V, hV, hcyc⟩ :=
    exists_upperRamificationGroupInfinite_cyclotomic_index_add_ramificationIdx p K
  have hB (u : ℝ) (hu : V ≤ u) :
      (upperRamificationGroupInfinite K (cyclotomicExtension (K := K) p)
        (u + (a : ℝ))).index =
        p * (upperRamificationGroupInfinite K (cyclotomicExtension (K := K) p) u).index := by
    simpa only [a, addVal_p_toNat_eq_padic_ramificationIdx p] using hcyc u hu
  by_cases hM : (affineTranslationKernel (falseTateAffineImage p (π : K))).toAddSubgroup = ⊥
  · refine ⟨p, (Fact.out : p.Prime).pos, V, hV, fun u hu => ?_⟩
    rw [falseTate_upper_index_of_translationKernel_eq_bot p π hM
      (by linarith [show (0 : ℝ) ≤ (a : ℝ) from Nat.cast_nonneg a] : -1 ≤ u + (a : ℝ)),
      falseTate_upper_index_of_translationKernel_eq_bot p π hM
        (by linarith : -1 ≤ u), hB u hu]
  · obtain ⟨C, D, hC, hD, hcomp⟩ := exists_falseTate_upper_index_comparison p π hM
    refine ⟨C * D * p ^ 2, Nat.mul_pos (Nat.mul_pos hC hD)
      (pow_pos (Fact.out : p.Prime).pos _), V, hV, fun u hu => ?_⟩
    have hu₀ : 0 ≤ u := hV.trans hu
    have hshift := (hcomp (u + (a : ℝ)) (add_nonneg hu₀ (Nat.cast_nonneg a))).2.2
    have hA := kummerExtension_apfIndex_growth p π (falseTateBase_addVal_p_pos p) hu₀
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

omit [NormedAlgebra (ℚ_[p]) K] [FiniteDimensional (ℚ_[p]) K] in
/-- The full upper index retains the fixed inertia index as a
factor. This identity allows a finite initial residue extension. -/
theorem falseTate_upper_index_eq_apfIndex_mul_inertia_index [hπ : Fact (Irreducible π)]
    {u : ℝ} (hu : 0 ≤ u) :
    (upperRamificationGroupInfinite K (falseTateExtension p (π : K)) u).index =
      apfIndex K (falseTateExtension p (π : K)) u *
        (upperRamificationGroupInfinite K (falseTateExtension p (π : K)) 0).index := by
  have := falseTateExtension_isGalois p (π : K)
  rw [apfIndex_eq_upperInfiniteRelIndex K _ hu]
  exact (Subgroup.relIndex_mul_index
    (upperRamificationGroupInfinite_antitoneOn K _
      (by norm_num : -1 ≤ (0 : ℝ)) (by linarith : -1 ≤ u) hu)).symm

/-- Cancelling the positive finite inertia factor gives bounded growth of
the false Tate index over its base. -/
theorem exists_falseTate_apfIndex_boundedGrowth [hπ : Fact (Irreducible π)] :
    ∃ Q : ℕ, 0 < Q ∧ ∃ V : ℝ, 0 ≤ V ∧ ∀ u : ℝ, V ≤ u →
      apfIndex K (falseTateExtension p (π : K))
        (u + ((IsDiscreteValuationRing.addVal
          𝒪[K]
          (p : 𝒪[K])).toNat : ℝ)) ≤
        Q * apfIndex K (falseTateExtension p (π : K)) u := by
  have := falseTateExtension_isGalois p (π : K)
  let := (isAPF_iff_upperInfinite_finiteIndex K _).mp
    (isAPF_falseTateExtension p π) 0 (by norm_num)
  have hzero : 0 < (upperRamificationGroupInfinite K (falseTateExtension p (π : K)) 0).index :=
    Nat.pos_of_ne_zero Subgroup.FiniteIndex.index_ne_zero
  obtain ⟨Q, hQ, V, hV, hfull⟩ := exists_falseTate_upper_index_boundedGrowth p π
  refine ⟨Q, hQ, V, hV, fun u hu => ?_⟩
  have hg := hfull u hu
  rw [falseTate_upper_index_eq_apfIndex_mul_inertia_index p π
      (add_nonneg (hV.trans hu) (Nat.cast_nonneg _)),
    falseTate_upper_index_eq_apfIndex_mul_inertia_index p π (hV.trans hu),
    ← Nat.mul_assoc] at hg
  exact (mul_le_mul_iff_left₀ hzero).mp hg

/-- Every false Tate extension over a finite norm-compatible
`p`-adic base is strictly APF, including the prime two and a finite initial
residue extension. -/
instance isStrictlyAPF_falseTateExtension [hπ : Fact (Irreducible π)] :
    IsStrictlyAPF K (falseTateExtension p (π : K)) := by
  obtain ⟨Q, hQ, V, _, hgrowth⟩ := exists_falseTate_apfIndex_boundedGrowth p π
  have := isAPF_falseTateExtension p π
  apply isStrictlyAPF_of_apfIndex_boundedGrowth K _ (U := V)
    (Nat.cast_pos.mpr (falseTateBase_addVal_p_pos (K := K) p)) (Nat.cast_pos.mpr hQ)
  intro u hu
  exact_mod_cast hgrowth u hu

end FiniteBase

section CanonicalFiniteBase

variable (p : ℕ) [Fact p.Prime]
variable (K : Type*) [NontriviallyNormedField K] [IsCompleteDiscreteValuedField K]
    [CharZero K] [NormedAlgebra (ℚ_[p]) K] [FiniteDimensional (ℚ_[p]) K]
variable (π : 𝒪[K])

/-- Over an arbitrary finite norm-compatible `p`-adic base, the
unit-ball DVR structure and its perfect residue field supply every
valued-field hypothesis of false Tate strictness. -/
instance isStrictlyAPF_falseTateExtension_of_finiteDimensional [hπ : Fact (Irreducible π)] :
    IsStrictlyAPF K (falseTateExtension p (π : K)) := by
  let := normedAlgebra_residueField_perfectField (ℚ_[p]) K
  exact isStrictlyAPF_falseTateExtension p π

/-- Public APF over every finite norm-compatible `p`-adic base,
without a separate DVR or perfect-residue hypothesis. -/
instance isAPF_falseTateExtension_of_finiteDimensional [hπ : Fact (Irreducible π)] :
    IsAPF K (falseTateExtension p (π : K)) := by
  exact (isStrictlyAPF_falseTateExtension_of_finiteDimensional p K π).toIsAPF

end CanonicalFiniteBase

end FalseTateExtension
end
