/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FalseTateExtension.Padic.CyclotomicUpper
public import FalseTateExtension.Padic.CyclotomicInertia
public import FalseTateExtension.Padic.InfiniteCharacter
public import FalseTateExtension.Padic.GeneralCharacter
public import FontaineWintenberger.Ramification.Infinite.Basic
public import FontaineWintenberger.APF.Galois
public import FontaineWintenberger.APF.Strict
public import FontaineWintenberger.APF.Subextension
public import FontaineWintenberger.APF.BaseChange.Strict
public import FontaineWintenberger.APF.Tower.Stages
public import FontaineWintenberger.APF.Finite.Slope

/-!
# The actual cyclotomic upper groups and APF property

The original finite-layer restrictions identify the actual infinite rational
cyclotomic upper groups with principal-unit kernels. The resulting indices
supply the quantitative growth criterion for strict APF.
-/

@[expose] public section

noncomputable section

open FontaineWintenberger

namespace FalseTateExtension

variable (p : ℕ) [Fact p.Prime]

local notation "Qp" => Padic p
local notation "Cyc" => cyclotomicExtension (K := Padic p) p

local instance : IsDiscreteValuationRing
    (NormedField.valuation (K := Padic p)).valuationSubring :=
  cyclotomicBase_unitBall_isDiscreteValuationRing p (Padic p)

/-- The original positive cyclotomic layers test the actual infinite upper
condition, through their original inclusion isomorphisms. -/
theorem mem_upperRamificationGroupInfinite_cyclotomic_iff
    {u : ℝ} (hu : -1 ≤ u) (g : Cyc ≃ₐ[Qp] Cyc) :
    g ∈ upperRamificationGroupInfinite Qp Cyc u ↔
      ∀ n, cyclotomicLayerRestriction p (n + 1) g ∈
        upperRamificationGroup
          (R := spectralIntegerRing Qp (cyclotomicLayer (K := Qp) p (n + 1)))
          (cyclotomicLayer (K := Qp) p (n + 1) ≃ₐ[Qp]
            cyclotomicLayer (K := Qp) p (n + 1)) u := by
  rw [mem_upperRamificationGroupInfinite_iff_cofinal Qp Cyc
    (cyclotomicFiniteLayer (K := Qp) p)
    (fun D ↦ exists_le_cyclotomicFiniteLayer p D.toIntermediateField) hu]
  apply forall_congr'
  intro n
  rw [restrictNormal_cyclotomicFiniteLayer,
    ← upperRamificationGroup_map_autCongr Qp (cyclotomicFiniteLayerEquiv (K := Qp) p n) hu,
    Subgroup.mem_map_equiv]
  simp only [MulEquiv.symm_apply_apply]
  rfl

/-- At every positive upper interval the actual infinite group is the
kernel of restriction to the original finite cyclotomic layer. -/
theorem upperRamificationGroupInfinite_cyclotomic_eq_ker
    (r : ℕ) {u : ℝ} (hu0 : (r : ℝ) < u) (hu1 : u ≤ (r : ℝ) + 1) :
    upperRamificationGroupInfinite Qp Cyc u = (cyclotomicLayerRestriction p (r + 1)).ker := by
  have hu : -1 ≤ u := by linarith [Nat.cast_nonneg (α := ℝ) r]
  ext g
  rw [mem_upperRamificationGroupInfinite_cyclotomic_iff p hu, MonoidHom.mem_ker]
  constructor
  · intro hg
    have h := hg r
    rw [upperRamificationGroup_cyclotomic_eq_bot p r hu0, Subgroup.mem_bot] at h
    exact h
  · intro hg n
    by_cases hn : n ≤ r
    · have hres : cyclotomicLayerRestriction p (n + 1) g = 1 := by
        change cyclotomicRestrictionToLayer p (n + 1) g = 1
        rw [cyclotomicRestrictionToLayer_comp p (by omega : n + 1 ≤ r + 1)]
        change cyclotomicRestrictionBetweenLayers p (by omega : n + 1 ≤ r + 1)
          (cyclotomicLayerRestriction p (r + 1) g) = 1
        rw [hg, map_one]
      rw [hres]
      exact Subgroup.one_mem _
    · rw [upperRamificationGroup_cyclotomic_eq_comap_unitReduction p n r (by omega) hu0 hu1,
        Subgroup.mem_comap, MonoidHom.mem_ker, cyclotomicLayerCharacter_restrict]
      apply Units.ext
      change ZMod.castHom (pow_dvd_pow p (by omega : r + 1 ≤ n + 1)) (ZMod (p ^ (r + 1)))
          (PadicInt.toZModPow (n + 1) (cyclotomicExtensionCharacter p g : PadicInt p)) = 1
      have hcomp := congrArg
        (fun f : PadicInt p →+* ZMod (p ^ (r + 1)) ↦
          f (cyclotomicExtensionCharacter p g : PadicInt p))
        (PadicInt.zmod_cast_comp_toZModPow (r + 1) (n + 1) (by omega))
      simp only [RingHom.comp_apply] at hcomp
      rw [hcomp]
      have hchar := cyclotomicLayerCharacter_restrict p (r + 1) g
      rw [hg, map_one] at hchar
      exact congrArg Units.val hchar.symm

/-- The actual infinite rational cyclotomic extension is totally ramified
at the level of its full upper inertia subgroup. -/
theorem upperRamificationGroupInfinite_cyclotomic_zero :
    upperRamificationGroupInfinite Qp Cyc 0 = ⊤ := by
  apply top_unique
  intro g _
  rw [mem_upperRamificationGroupInfinite_cyclotomic_iff p (by norm_num)]
  intro n
  rw [upperRamificationGroup_cyclotomic_zero]
  trivial

/-- Nonpositive upper parameters retain the whole actual cyclotomic group. -/
theorem upperRamificationGroupInfinite_cyclotomic_of_nonpos
    {u : ℝ} (hu : -1 ≤ u) (hu0 : u ≤ 0) :
    upperRamificationGroupInfinite Qp Cyc u = ⊤ := by
  apply top_unique
  rw [← upperRamificationGroupInfinite_cyclotomic_zero p]
  exact upperRamificationGroupInfinite_antitoneOn Qp Cyc hu (by norm_num) hu0

private theorem exists_cyclotomic_upper_interval {u : ℝ} (hu : 0 < u) :
    ∃ r : ℕ, (r : ℝ) < u ∧ u ≤ (r : ℝ) + 1 := by
  have hc : 0 < Nat.ceil u := Nat.lt_ceil.mpr (by simpa using hu)
  refine ⟨Nat.ceil u - 1, Nat.lt_ceil.mp (by omega), ?_⟩
  have h := Nat.le_ceil u
  have hn : Nat.ceil u - 1 + 1 = Nat.ceil u := by omega
  have hcast : ((Nat.ceil u - 1 : ℕ) : ℝ) + 1 = (Nat.ceil u : ℝ) := by exact_mod_cast hn
  linarith

/-- The restriction kernel is precisely the principal-unit condition in the
original infinite cyclotomic character. -/
theorem upperRamificationGroupInfinite_cyclotomic_eq_character_ker
    (r : ℕ) {u : ℝ} (hu0 : (r : ℝ) < u) (hu1 : u ≤ (r : ℝ) + 1) :
    upperRamificationGroupInfinite Qp Cyc u =
      ((Units.map (PadicInt.toZModPow (r + 1)).toMonoidHom).comp
        (cyclotomicExtensionCharacter (K := Qp) p)).ker := by
  rw [upperRamificationGroupInfinite_cyclotomic_eq_ker p r hu0 hu1]
  ext g
  simp only [MonoidHom.mem_ker, MonoidHom.comp_apply]
  constructor
  · intro h
    rw [← cyclotomicLayerCharacter_restrict, h, map_one]
  · intro h
    apply cyclotomicLayerCharacter_injective p (r + 1)
    rw [map_one, cyclotomicLayerCharacter_restrict]
    exact h

/-- The actual character image of each positive upper group is the full
kernel of reduction on the original p-adic unit group. -/
theorem upperRamificationGroupInfinite_cyclotomic_map_character
    (r : ℕ) {u : ℝ} (hu0 : (r : ℝ) < u) (hu1 : u ≤ (r : ℝ) + 1) :
    (upperRamificationGroupInfinite Qp Cyc u).map (cyclotomicExtensionCharacter p) =
      (Units.map (PadicInt.toZModPow (r + 1)).toMonoidHom).ker := by
  rw [upperRamificationGroupInfinite_cyclotomic_eq_character_ker p r hu0 hu1]
  change ((Units.map (PadicInt.toZModPow (r + 1)).toMonoidHom).ker.comap
    (cyclotomicExtensionCharacter p)).map (cyclotomicExtensionCharacter p) = _
  rw [Subgroup.map_comap_eq, MonoidHom.range_eq_top.mpr
    (cyclotomicExtensionCharacter_surjective_padic p), top_inf_eq]

/-- The full actual upper index on a positive unit interval is the
prime-power totient of the original finite layer. -/
theorem upperRamificationGroupInfinite_cyclotomic_index
    (r : ℕ) {u : ℝ} (hu0 : (r : ℝ) < u) (hu1 : u ≤ (r : ℝ) + 1) :
    (upperRamificationGroupInfinite Qp Cyc u).index = (p ^ (r + 1)).totient := by
  rw [upperRamificationGroupInfinite_cyclotomic_eq_ker p r hu0 hu1]
  change ((⊥ : Subgroup (cyclotomicLayer (K := Qp) p (r + 1) ≃ₐ[Qp]
    cyclotomicLayer (K := Qp) p (r + 1))).comap (cyclotomicLayerRestriction p (r + 1))).index = _
  rw [Subgroup.index_comap_of_surjective _ (cyclotomicLayerRestriction_surjective p (r + 1)),
    Subgroup.index_bot, card_cyclotomicLayer_galois]

/-- All actual upper groups of the infinite rational cyclotomic extension
have finite index. -/
theorem upperRamificationGroupInfinite_cyclotomic_finiteIndex
    {u : ℝ} (hu : -1 ≤ u) : (upperRamificationGroupInfinite Qp Cyc u).FiniteIndex := by
  by_cases hu0 : u ≤ 0
  · rw [upperRamificationGroupInfinite_cyclotomic_of_nonpos p hu hu0]
    infer_instance
  · obtain ⟨r, hr0, hr1⟩ := exists_cyclotomic_upper_interval (lt_of_not_ge hu0)
    rw [upperRamificationGroupInfinite_cyclotomic_eq_ker p r hr0 hr1]
    infer_instance

/-- APF for the original infinite rational cyclotomic extension, as an
abstract separable field extension. -/
theorem isAPF_cyclotomicExtension_padic : IsAPF Qp Cyc := by
  rw [isAPF_iff_upperInfinite_finiteIndex]
  exact fun _ hu ↦ upperRamificationGroupInfinite_cyclotomic_finiteIndex p hu

/-- The intrinsic inertia-relative index has the same explicit positive
profile because the actual rational cyclotomic inertia is full. -/
theorem apfIndex_cyclotomicExtension_padic
    (r : ℕ) {u : ℝ} (hu0 : (r : ℝ) < u) (hu1 : u ≤ (r : ℝ) + 1) :
    apfIndex Qp Cyc u = (p ^ (r + 1)).totient := by
  rw [apfIndex_eq_upperInfiniteRelIndex Qp Cyc
    (by linarith [Nat.cast_nonneg (α := ℝ) r]),
    upperRamificationGroupInfinite_cyclotomic_zero p, Subgroup.relIndex_top_right]
  exact upperRamificationGroupInfinite_cyclotomic_index p r hu0 hu1

/-- Shifting a positive upper parameter by one multiplies the actual
rational cyclotomic index by `p`, at every prime. -/
theorem upperRamificationGroupInfinite_cyclotomic_index_add_one
    {u : ℝ} (hu : 0 < u) :
    (upperRamificationGroupInfinite Qp Cyc (u + 1)).index =
      p * (upperRamificationGroupInfinite Qp Cyc u).index := by
  obtain ⟨r, hr0, hr1⟩ := exists_cyclotomic_upper_interval hu
  rw [upperRamificationGroupInfinite_cyclotomic_index p r hr0 hr1,
    upperRamificationGroupInfinite_cyclotomic_index p (r + 1)
      (by push_cast; linarith) (by push_cast; linarith),
    Nat.totient_prime_pow_succ (Fact.out : p.Prime),
    Nat.totient_prime_pow_succ (Fact.out : p.Prime), pow_succ]
  ring

/-- The same exact growth holds for the public intrinsic APF index. -/
theorem apfIndex_cyclotomicExtension_padic_add_one {u : ℝ} (hu : 0 < u) :
    apfIndex Qp Cyc (u + 1) = p * apfIndex Qp Cyc u := by
  rw [apfIndex_eq_upperInfiniteRelIndex Qp Cyc (by linarith : 0 ≤ u + 1),
    apfIndex_eq_upperInfiniteRelIndex Qp Cyc hu.le,
    upperRamificationGroupInfinite_cyclotomic_zero p,
    Subgroup.relIndex_top_right, Subgroup.relIndex_top_right]
  exact upperRamificationGroupInfinite_cyclotomic_index_add_one p hu

/-- Strict APF for the original infinite rational cyclotomic extension
follows from the proved growth of its actual intrinsic index. -/
theorem isStrictlyAPF_cyclotomicExtension_padic : IsStrictlyAPF Qp Cyc := by
  let := isAPF_cyclotomicExtension_padic p
  apply isStrictlyAPF_of_apfIndex_boundedGrowth Qp Cyc
    (ℓ := 1) (C := (p : ℝ)) (U := 1) (by norm_num)
    (Nat.cast_pos.mpr (Fact.out : p.Prime).pos)
  intro u hu
  have h := apfIndex_cyclotomicExtension_padic_add_one p (by linarith : 0 < u)
  exact le_of_eq (by exact_mod_cast h)

section Compositum

variable {K : Type*} [Field K] [CharZero K]
    [Algebra (Padic p) K] [FiniteDimensional (Padic p) K]

omit [Algebra (Padic p) K] [FiniteDimensional (Padic p) K] in
/-- Every root of the indicated prime-power equation lies in the original
finite cyclotomic layer, independently of the chosen primitive root. -/
theorem mem_cyclotomicLayer_of_pow_eq_one (n : ℕ) {ζ : AlgebraicClosure K}
    (hζ : ζ ^ (p ^ n) = 1) : ζ ∈ cyclotomicLayer (K := K) p n := by
  have : NeZero (p ^ n) := ⟨pow_ne_zero n (Fact.out : p.Prime).ne_zero⟩
  obtain ⟨j, _, rfl⟩ := (isPrimitiveRoot_rootOfUnity (K := K) p n).eq_pow_of_pow_eq_one hζ
  exact (cyclotomicLayer (K := K) p n).toSubalgebra.pow_mem
    (rootOfUnity_mem_cyclotomicLayer p n) j

/-- One actual rational closure embedding sends the entire original
rational cyclotomic field into the original cyclotomic field over `K`. -/
def rationalCyclotomicEmbedding : Cyc →ₐ[Qp] cyclotomicExtension (K := K) p := by
  let e := IsAlgClosure.equiv Qp (AlgebraicClosure Qp) (AlgebraicClosure K)
  let f := e.toAlgHom.comp (cyclotomicExtension (K := Qp) p).val
  apply f.codRestrict ((cyclotomicExtension (K := K) p).restrictScalars Qp).toSubalgebra
  intro x
  obtain ⟨n, hn⟩ := (mem_cyclotomicExtension_iff p (x : AlgebraicClosure Qp)).mp x.property
  have hroot : e (rootOfUnity (K := Qp) p n) ∈ cyclotomicExtension (K := K) p := by
    apply cyclotomicLayer_le_cyclotomicExtension p n
    apply mem_cyclotomicLayer_of_pow_eq_one p n
    rw [← map_pow, rootOfUnity_pow, map_one]
  have hle : cyclotomicLayer (K := Qp) p n ≤
      ((cyclotomicExtension (K := K) p).restrictScalars Qp).comap e.toAlgHom :=
    IntermediateField.adjoin_simple_le_iff.mpr hroot
  exact hle hn

/-- The embedded rational cyclotomic field contains every original chosen
root over `K`; the two choices need not agree term by term. -/
theorem cyclotomicRootOfUnity_mem_rationalCyclotomicEmbedding (n : ℕ) :
    cyclotomicRootOfUnity (K := K) p n ∈
      (rationalCyclotomicEmbedding (K := K) p).fieldRange := by
  have : NeZero (p ^ n) := ⟨pow_ne_zero n (Fact.out : p.Prime).ne_zero⟩
  have hprim := (isPrimitiveRoot_cyclotomicRootOfUnity (K := Qp) p n).map_of_injective
    (rationalCyclotomicEmbedding (K := K) p).injective
  obtain ⟨j, _, hj⟩ := hprim.eq_pow_of_pow_eq_one
    (isPrimitiveRoot_cyclotomicRootOfUnity (K := K) p n).pow_eq_one
  rw [← hj]
  exact (rationalCyclotomicEmbedding (K := K) p).fieldRange.toSubalgebra.pow_mem
    ⟨cyclotomicRootOfUnity (K := Qp) p n, rfl⟩ j

local instance (priority := 100) rationalCyclotomicEmbeddingAlgebra :
    Algebra Cyc (cyclotomicExtension (K := K) p) :=
  (rationalCyclotomicEmbedding (K := K) p).toRingHom.toAlgebra

local instance (priority := 100) rationalCyclotomicEmbeddingTower :
    IsScalarTower Qp Cyc (cyclotomicExtension (K := K) p) :=
  IsScalarTower.of_algHom (rationalCyclotomicEmbedding (K := K) p)

local instance rationalCyclotomicBase_isAlgebraic :
    Algebra.IsAlgebraic Qp (cyclotomicExtension (K := K) p) :=
  Algebra.IsAlgebraic.trans Qp K (cyclotomicExtension (K := K) p)

/-- The original cyclotomic field over `K` is the actual compositum of
the embedded rational cyclotomic field and the original image of `K`. -/
theorem rationalCyclotomicEmbedding_adjoin_base :
    IntermediateField.adjoin Cyc
      ((IsScalarTower.toAlgHom Qp K (cyclotomicExtension (K := K) p)).fieldRange :
        Set (cyclotomicExtension (K := K) p)) = ⊤ := by
  let A := IntermediateField.adjoin Cyc
    ((IsScalarTower.toAlgHom Qp K (cyclotomicExtension (K := K) p)).fieldRange :
      Set (cyclotomicExtension (K := K) p))
  let D : IntermediateField K (AlgebraicClosure K) :=
    { A.toSubfield.map (cyclotomicExtension (K := K) p).val.toRingHom with
      algebraMap_mem' := fun k ↦ ⟨algebraMap K (cyclotomicExtension (K := K) p) k,
        IntermediateField.subset_adjoin Cyc _ ⟨k, rfl⟩, rfl⟩ }
  have hroots (n : ℕ) : cyclotomicRootOfUnity (K := K) p n ∈ A := by
    obtain ⟨z, hz⟩ := cyclotomicRootOfUnity_mem_rationalCyclotomicEmbedding (K := K) p n
    have hzA := A.algebraMap_mem z
    change rationalCyclotomicEmbedding p z ∈ A at hzA
    change rationalCyclotomicEmbedding p z = _ at hz
    rwa [hz] at hzA
  have hD : cyclotomicExtension (K := K) p ≤ D := by
    apply iSup_le
    intro n
    apply IntermediateField.adjoin_simple_le_iff.mpr
    exact ⟨cyclotomicRootOfUnity (K := K) p n, hroots n, rfl⟩
  apply top_unique
  intro x _
  obtain ⟨y, hy, hxy⟩ := hD x.property
  have heq : y = x := Subtype.ext hxy
  exact heq ▸ hy

set_option maxHeartbeats 1000000 in
-- The finite compositum proof elaborates several intermediate-field scalar towers.
/-- The actual compositum has finite degree over the embedded rational
cyclotomic extension, because the original base is finite over `Qp`. -/
theorem rationalCyclotomicEmbedding_finiteDimensional :
    FiniteDimensional Cyc (cyclotomicExtension (K := K) p) := by
  let L := (IsScalarTower.toAlgHom Qp K (cyclotomicExtension (K := K) p)).fieldRange
  let : FiniteDimensional Qp L := Module.Finite.equiv
    (IsScalarTower.toAlgHom Qp K (cyclotomicExtension (K := K) p)).equivFieldRange.toLinearEquiv
  let A := IntermediateField.adjoin Cyc (L : Set (cyclotomicExtension (K := K) p))
  let : Module.Free Cyc A := Module.Free.of_divisionRing Cyc A
  have hr := IntermediateField.adjoin_rank_le_of_isAlgebraic_right Cyc L
  have hfinite : FiniteDimensional Cyc A :=
    (Module.rank_lt_aleph0_iff (R := Cyc) (M := A)).mp
      (hr.trans_lt (Module.rank_lt_aleph0 Qp L))
  let := hfinite
  apply Module.Finite.of_surjective A.val.toLinearMap
  intro x
  refine ⟨⟨x, ?_⟩, rfl⟩
  change x ∈ IntermediateField.adjoin Cyc (L : Set (cyclotomicExtension (K := K) p))
  rw [rationalCyclotomicEmbedding_adjoin_base (K := K) p]
  trivial

/-- The original cyclotomic field over a finite base remains strictly APF
over the rational base, by the proved actual finite compositum. -/
theorem isStrictlyAPF_cyclotomicExtension_over_padic :
    IsStrictlyAPF Qp (cyclotomicExtension (K := K) p) := by
  let := rationalCyclotomicEmbedding_finiteDimensional (K := K) p
  exact (isStrictlyAPF_finite_extension_iff Qp (cyclotomicExtension (K := K) p) Cyc).mpr
    (isStrictlyAPF_cyclotomicExtension_padic p)

end Compositum

section ValuedBase

variable (K : Type*) [NontriviallyNormedField K] [CharZero K]
    [IsUltrametricDist K] [CompleteSpace K]
    [NormedAlgebra (Padic p) K] [FiniteDimensional (Padic p) K]

/-- The original cyclotomic extension of every finite compatible normed
extension of `Qp` is strictly APF, at every prime. -/
theorem isStrictlyAPF_cyclotomicExtension :
    letI := cyclotomicBase_isCompleteDiscreteValuedField p K
    IsStrictlyAPF K (cyclotomicExtension (K := K) p) := by
  let := cyclotomicBase_isCompleteDiscreteValuedField p K
  let := rationalCyclotomicBase_isAlgebraic (K := K) p
  exact (isStrictlyAPF_finiteBase_iff_of_normedAlgebra Qp K
    (cyclotomicExtension (K := K) p)).mp
      (isStrictlyAPF_cyclotomicExtension_over_padic (K := K) p)

/-- Public APF for the original cyclotomic field over its original finite
normed base, with no normality or finiteness restriction on the top. -/
theorem isAPF_cyclotomicExtension :
    letI := cyclotomicBase_isCompleteDiscreteValuedField p K
    IsAPF K (cyclotomicExtension (K := K) p) := by
  let := cyclotomicBase_isCompleteDiscreteValuedField p K
  exact (isStrictlyAPF_cyclotomicExtension p K).toIsAPF

end ValuedBase

section CharacterTransport

variable (F : Type*) [NontriviallyNormedField F] [IsCompleteDiscreteValuedField F]
    [PerfectField (IsLocalRing.ResidueField
      (NormedField.valuation (K := F)).valuationSubring)]

omit [PerfectField (IsLocalRing.ResidueField
  (NormedField.valuation (K := F)).valuationSubring)] in
/-- Actual upper character images are preserved by an algebra isomorphism
of the top fields. The characters are the canonical characters on those fields. -/
theorem cyclotomicCharacter_map_upper_autCongr
    {E E' : Type*} [Field E] [Field E'] [Algebra F E] [Algebra F E']
    [∀ n, HasEnoughRootsOfUnity E (p ^ n)] [∀ n, HasEnoughRootsOfUnity E' (p ^ n)]
    (e : E ≃ₐ[F] E') {u : ℝ} (hu : -1 ≤ u) :
    (upperRamificationGroupInfinite F E u).map ((_root_.cyclotomicCharacter E p).comp
        (MulSemiringAction.toRingAut (E ≃ₐ[F] E) E)) =
      (upperRamificationGroupInfinite F E' u).map ((_root_.cyclotomicCharacter E' p).comp
        (MulSemiringAction.toRingAut (E' ≃ₐ[F] E') E')) := by
  have hχ : ((_root_.cyclotomicCharacter E p).comp
      (MulSemiringAction.toRingAut (E ≃ₐ[F] E) E)) =
      (((_root_.cyclotomicCharacter E' p).comp
        (MulSemiringAction.toRingAut (E' ≃ₐ[F] E') E')).comp e.autCongr.toMonoidHom) := by
    apply MonoidHom.ext
    intro g
    exact cyclotomicCharacter_eq_of_intertwines p e.toRingHom g.toRingEquiv
      (e.autCongr g).toRingEquiv (fun x ↦ by simp)
  rw [hχ, ← Subgroup.map_map, upperRamificationGroupInfinite_map_autCongr F e hu]

variable [CharZero F]

/-- Ordinary upper restriction to the original cyclotomic subfield preserves
the canonical character image at every allowed upper parameter. -/
theorem cyclotomicExtension_map_upper_from_algebraicClosure
    {u : ℝ} (hu : -1 ≤ u) :
    (upperRamificationGroupInfinite F (cyclotomicExtension (K := F) p) u).map
        (cyclotomicExtensionCharacter p) =
      (upperRamificationGroupInfinite F (AlgebraicClosure F) u).map
        ((_root_.cyclotomicCharacter (AlgebraicClosure F) p).comp
          (MulSemiringAction.toRingAut
            (AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F) (AlgebraicClosure F))) := by
  rw [← restrictNormalHom_map_upperRamificationGroupInfinite F (AlgebraicClosure F)
    (cyclotomicExtension (K := F) p) u hu, Subgroup.map_map]
  congr 1
  apply MonoidHom.ext
  intro g
  exact cyclotomicCharacter_restrict_cyclotomicExtension p g

end CharacterTransport

/-- In any actual algebraic closure of the rational base, the canonical
character sends the actual positive upper group onto the whole indicated
principal-unit kernel. The proof uses ordinary restriction to the image of
the original rational cyclotomic field. -/
theorem cyclotomicCharacter_map_upperRamificationGroupInfinite
    (Ω : Type*) [Field Ω] [Algebra Qp Ω] [IsAlgClosure Qp Ω]
    (r : ℕ) {u : ℝ} (hu0 : (r : ℝ) < u) (hu1 : u ≤ (r : ℝ) + 1) :
    (upperRamificationGroupInfinite Qp Ω u).map
      ((_root_.cyclotomicCharacter Ω p).comp
        (MulSemiringAction.toRingAut (Ω ≃ₐ[Qp] Ω) Ω)) =
      (Units.map (PadicInt.toZModPow (r + 1)).toMonoidHom).ker := by
  let : IsAlgClosed Ω := IsAlgClosure.isAlgClosed Qp
  let : CharZero Ω := charZero_of_injective_algebraMap (algebraMap Qp Ω).injective
  have hu : -1 ≤ u := by linarith [Nat.cast_nonneg (α := ℝ) r]
  let i : Cyc →ₐ[Qp] Ω :=
    (IsAlgClosure.equiv Qp (AlgebraicClosure Qp) Ω).toAlgHom.comp
      (cyclotomicExtension (K := Qp) p).val
  let e := i.equivFieldRange
  let : IsGalois Qp i.fieldRange := IsGalois.of_algEquiv e
  let f : (Ω ≃ₐ[Qp] Ω) →* (Cyc ≃ₐ[Qp] Cyc) :=
    e.symm.autCongr.toMonoidHom.comp (AlgEquiv.restrictNormalHom i.fieldRange)
  have hf : (upperRamificationGroupInfinite Qp Ω u).map f =
      upperRamificationGroupInfinite Qp Cyc u := by
    rw [show f = e.symm.autCongr.toMonoidHom.comp
        (AlgEquiv.restrictNormalHom i.fieldRange) from rfl,
      ← Subgroup.map_map,
      restrictNormalHom_map_upperRamificationGroupInfinite Qp Ω i.fieldRange u hu,
      upperRamificationGroupInfinite_map_autCongr Qp e.symm hu]
  have hχ : ((_root_.cyclotomicCharacter Ω p).comp
      (MulSemiringAction.toRingAut (Ω ≃ₐ[Qp] Ω) Ω)) =
      (cyclotomicExtensionCharacter p).comp f := by
    apply MonoidHom.ext
    intro g
    change _root_.cyclotomicCharacter Ω p g.toRingEquiv =
      _root_.cyclotomicCharacter Cyc p (f g).toRingEquiv
    apply (cyclotomicCharacter_eq_of_intertwines p i.toRingHom
      (f g).toRingEquiv g.toRingEquiv ?_).symm
    intro x
    change (e (e.symm ((g.restrictNormal i.fieldRange) (e x))) : Ω) = g (i x)
    rw [e.apply_symm_apply]
    exact AlgEquiv.restrictNormal_commutes g i.fieldRange (e x)
  rw [hχ, ← Subgroup.map_map, hf,
    upperRamificationGroupInfinite_cyclotomic_map_character p r hu0 hu1]

section CommonClosureCharacter

variable (K : Type*) [NontriviallyNormedField K] [CharZero K]
    [IsUltrametricDist K] [CompleteSpace K]
    [NormedAlgebra (Padic p) K] [FiniteDimensional (Padic p) K]
    [Algebra K (SeparableClosure (Padic p))]
    [IsScalarTower (Padic p) K (SeparableClosure (Padic p))]

/-- Actual finite base change identifies the upper character image with
the character image of the old upper group intersected with the actual
fixing subgroup of the embedded original base. -/
theorem cyclotomicCharacter_map_upper_finiteBase {u : ℝ} (hu : -1 ≤ u) :
    letI := cyclotomicBase_isCompleteDiscreteValuedField p K
    (upperRamificationGroupInfinite K (SeparableClosure K) (apfPsi Qp K u)).map
        ((_root_.cyclotomicCharacter (SeparableClosure K) p).comp
          (MulSemiringAction.toRingAut
            (SeparableClosure K ≃ₐ[K] SeparableClosure K) (SeparableClosure K))) =
      ((IsScalarTower.toAlgHom Qp K (SeparableClosure Qp)).fieldRange.fixingSubgroup ⊓
        upperRamificationGroupInfinite Qp (SeparableClosure Qp) u).map
        ((_root_.cyclotomicCharacter (SeparableClosure Qp) p).comp
          (MulSemiringAction.toRingAut
            (SeparableClosure Qp ≃ₐ[Qp] SeparableClosure Qp) (SeparableClosure Qp))) := by
  let := cyclotomicBase_isCompleteDiscreteValuedField p K
  let := normedAlgebra_residueField_perfectField Qp K
  let ρ := AbstractFiniteBase.closureHom Qp K
  have hχ : ((_root_.cyclotomicCharacter (SeparableClosure K) p).comp
      (MulSemiringAction.toRingAut
        (SeparableClosure K ≃ₐ[K] SeparableClosure K) (SeparableClosure K))) =
      (((_root_.cyclotomicCharacter (SeparableClosure Qp) p).comp
        (MulSemiringAction.toRingAut
          (SeparableClosure Qp ≃ₐ[Qp] SeparableClosure Qp) (SeparableClosure Qp))).comp ρ) := by
    apply MonoidHom.ext
    intro g
    exact cyclotomicCharacter_eq_of_intertwines p
      (AbstractFiniteBase.closureEquiv Qp K).toRingHom g.toRingEquiv (ρ g).toRingEquiv
      (fun x ↦ (AbstractFiniteBase.closureHom_apply Qp K g x).symm)
  have hupper : (upperRamificationGroupInfinite Qp (SeparableClosure Qp) u).comap ρ =
      upperRamificationGroupInfinite K (SeparableClosure K) (apfPsi Qp K u) :=
    AbstractFiniteBase.comap_upper Qp K hu
  rw [hχ, ← Subgroup.map_map, ← hupper,
    Subgroup.map_comap_eq, AbstractFiniteBase.closureHom_range Qp K]

/-- The same finite-base identity computes the character image of the
original cyclotomic subfield, with its original base and scalar maps. -/
theorem cyclotomicExtension_map_upper_finiteBase {u : ℝ} (hu : -1 ≤ u) :
    letI := cyclotomicBase_isCompleteDiscreteValuedField p K
    (upperRamificationGroupInfinite K (cyclotomicExtension (K := K) p) (apfPsi Qp K u)).map
        (cyclotomicExtensionCharacter p) =
      ((IsScalarTower.toAlgHom Qp K (SeparableClosure Qp)).fieldRange.fixingSubgroup ⊓
        upperRamificationGroupInfinite Qp (SeparableClosure Qp) u).map
        ((_root_.cyclotomicCharacter (SeparableClosure Qp) p).comp
          (MulSemiringAction.toRingAut
            (SeparableClosure Qp ≃ₐ[Qp] SeparableClosure Qp) (SeparableClosure Qp))) := by
  let := cyclotomicBase_isCompleteDiscreteValuedField p K
  let := normedAlgebra_residueField_perfectField Qp K
  have hv := IsAPF.apfPsi_mem_Ici Qp K hu
  rw [cyclotomicExtension_map_upper_from_algebraicClosure p K hv,
    ← cyclotomicCharacter_map_upper_autCongr p K
      (IsAlgClosure.equiv K (SeparableClosure K) (AlgebraicClosure K)) hv]
  exact cyclotomicCharacter_map_upper_finiteBase p K hu

end CommonClosureCharacter

section EventualCharacterImage

variable (K : Type*) [NontriviallyNormedField K] [CharZero K]
    [IsUltrametricDist K] [CompleteSpace K]
    [NormedAlgebra (Padic p) K] [FiniteDimensional (Padic p) K]

/-- After a genuine finite cutoff, the actual upper character image over
the original finite base is the full rational principal-unit kernel at the
actual finite-base inverse-Herbrand parameter. -/
theorem exists_cyclotomicExtension_upper_principal_finiteBase :
    letI := cyclotomicBase_isCompleteDiscreteValuedField p K
    ∃ U : ℝ, 1 ≤ U ∧ ∀ u : ℝ, U ≤ u → ∀ r : ℕ,
      (r : ℝ) < u → u ≤ (r : ℝ) + 1 →
      (upperRamificationGroupInfinite K (cyclotomicExtension (K := K) p) (apfPsi Qp K u)).map
          (cyclotomicExtensionCharacter p) =
        (Units.map (PadicInt.toZModPow (r + 1)).toMonoidHom).ker := by
  let := cyclotomicBase_isCompleteDiscreteValuedField p K
  obtain ⟨i⟩ := nonempty_separableClosure_embeddings Qp K
  let : Algebra K (SeparableClosure Qp) := i.toRingHom.toAlgebra
  let : IsScalarTower Qp K (SeparableClosure Qp) := IsScalarTower.of_algHom i
  let S := i.fieldRange
  let : FiniteDimensional Qp S := Module.Finite.equiv i.equivFieldRange.toLinearEquiv
  obtain ⟨U, _, hfix⟩ := exists_absoluteUpper_le_fixingSubgroup_of_finite Qp S
  refine ⟨max U 1, le_max_right _ _, fun u hu r hr0 hr1 ↦ ?_⟩
  rw [cyclotomicExtension_map_upper_finiteBase p K
    (by linarith [(le_max_right U 1).trans hu] : -1 ≤ u)]
  have hle : upperRamificationGroupInfinite Qp (SeparableClosure Qp) u ≤ S.fixingSubgroup :=
    hfix u ((le_max_left _ _).trans hu)
  have hi : IsScalarTower.toAlgHom Qp K (SeparableClosure Qp) = i := by
    ext x
    rfl
  rw [hi, inf_eq_right.mpr hle]
  exact cyclotomicCharacter_map_upperRamificationGroupInfinite p (SeparableClosure Qp)
    r hr0 hr1

/-- The actual full upper index over the original finite base differs from
the rational index by exactly the fixed actual cyclotomic image index. -/
theorem exists_cyclotomicExtension_upper_index_finiteBase :
    letI := cyclotomicBase_isCompleteDiscreteValuedField p K
    ∃ U : ℝ, 1 ≤ U ∧ ∀ u : ℝ, U ≤ u →
      (upperRamificationGroupInfinite K (cyclotomicExtension (K := K) p)
          (apfPsi Qp K u)).index * (cyclotomicExtensionCharacter (K := K) p).range.index =
        (upperRamificationGroupInfinite Qp Cyc u).index := by
  let := cyclotomicBase_isCompleteDiscreteValuedField p K
  obtain ⟨U, hU, himage⟩ := exists_cyclotomicExtension_upper_principal_finiteBase p K
  refine ⟨U, hU, fun u hu ↦ ?_⟩
  obtain ⟨r, hr0, hr1⟩ := exists_cyclotomic_upper_interval (by linarith : 0 < u)
  have hmap := (himage u hu r hr0 hr1).trans
    (upperRamificationGroupInfinite_cyclotomic_map_character p r hr0 hr1).symm
  have h := congrArg Subgroup.index hmap
  rw [Subgroup.index_map_of_injective _ (cyclotomicExtensionCharacter_injective p),
    Subgroup.index_map_of_bijective ⟨cyclotomicExtensionCharacter_injective p,
      cyclotomicExtensionCharacter_surjective_padic p⟩] at h
  exact h

/-- In the original finite base's upper parameter, shifting by its actual
ramification index eventually multiplies the full cyclotomic upper index by
exactly `p`. This includes the dyadic case and arbitrary finite residue degree. -/
theorem exists_upperRamificationGroupInfinite_cyclotomic_index_add_ramificationIdx :
    letI := cyclotomicBase_isCompleteDiscreteValuedField p K
    ∃ V : ℝ, 0 ≤ V ∧ ∀ v : ℝ, V ≤ v →
      (upperRamificationGroupInfinite K (cyclotomicExtension (K := K) p)
        (v + ((IsLocalRing.maximalIdeal
          (NormedField.valuation (K := K)).valuationSubring).ramificationIdx
            (NormedField.valuation (K := Qp)).valuationSubring : ℝ))).index =
        p * (upperRamificationGroupInfinite K (cyclotomicExtension (K := K) p) v).index := by
  let := cyclotomicBase_isCompleteDiscreteValuedField p K
  obtain ⟨A, hA, hindex⟩ := exists_cyclotomicExtension_upper_index_finiteBase p K
  obtain ⟨T, _, hshift⟩ := exists_apfPsi_normed_ramificationIdx_shift Qp K
  let U := max A T
  have hU : 1 ≤ U := hA.trans (le_max_left _ _)
  refine ⟨apfPsi Qp K U,
    (by linarith : 0 ≤ U).trans (IsAPF.le_apfPsi Qp K U), fun v hv ↦ ?_⟩
  let u := apfPhi Qp K v
  have hpsi : apfPsi Qp K u = v := apfPsi_apfPhi Qp K v
  have hu : U ≤ u := (IsAPF.strictMono_apfPsi Qp K).le_iff_le.mp (by
    rw [hpsi]
    exact hv)
  have huA : A ≤ u := (le_max_left A T).trans hu
  have huT : T ≤ u := (le_max_right A T).trans hu
  have h1 := hindex u huA
  have h2 := hindex (u + 1) (by linarith : A ≤ u + 1)
  rw [upperRamificationGroupInfinite_cyclotomic_index_add_one p
    (by linarith : 0 < u), ← h1] at h2
  have hg := mul_right_cancel₀
    (Nat.ne_of_gt (cyclotomicExtensionCharacter_index_pos (K := K) p))
    (h2.trans (Nat.mul_assoc _ _ _).symm)
  have hs := hshift u huT 1 (by norm_num : (0 : ℝ) ≤ 1)
  simpa only [hs, mul_one, hpsi] using hg

end EventualCharacterImage

end FalseTateExtension

end
