/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FalseTateExtension.Cyclotomic.CharacterNaturality
public import FalseTateExtension.Cyclotomic.Filtration
public import FalseTateExtension.Cyclotomic.Inertia
public import FalseTateExtension.Cyclotomic.InfiniteCharacter
public import FontaineWintenberger.APF.BaseChange.Strict
public import FontaineWintenberger.APF.Finite.Slope
public import FontaineWintenberger.APF.Galois
public import FontaineWintenberger.APF.Strict
public import FontaineWintenberger.APF.Subextension
public import FontaineWintenberger.APF.Tower.Stages
public import FontaineWintenberger.Ramification.Infinite.Basic

/-!
# The upper ramification filtration of `ℚ_[p](ζ_{p^∞})/ℚ_[p]` and strict APF

Let `G = Gal(ℚ_[p](ζ_{p^∞})/ℚ_[p])` with cyclotomic character `χ : G ≃ ℤ_[p]ˣ`. For
`r < u ≤ r + 1` the upper ramification group `G^u` is the kernel of restriction to
`ℚ_[p](ζ_{p^{r+1}})`, that is `χ⁻¹(1 + p^{r+1} ℤ_[p])`, of index `φ(p^{r+1})`; `G^0 = G`.
Hence every `G^u` has finite index, Wintenberger's index `i(u) = (G^0 : G^u)` satisfies
`i(u + 1) = p · i(u)` for `u > 0`, and `ℚ_[p](ζ_{p^∞})/ℚ_[p]` is strictly arithmetically
profinite. For a finite extension `K/ℚ_[p]`, the field `K(ζ_{p^∞})` is finite over the image of
`ℚ_[p](ζ_{p^∞})`, so `K(ζ_{p^∞})/K` is strictly arithmetically profinite as well.

For the cyclotomic character of `Gal(K(ζ_{p^∞})/K)`, with `ψ = ψ_{K/ℚ_[p]}`, the image of the
upper group `Gal(K(ζ_{p^∞})/K)^{ψ(u)}` is `χ(Gal(K̄/K) ∩ Gal(ℚ̄_p/ℚ_[p])^u)`; for `u` large and
`r < u ≤ r + 1` it is `1 + p^{r+1} ℤ_[p]`, and the index of `Gal(K(ζ_{p^∞})/K)^v` is
multiplied by `p` when `v` is shifted by `e(K/ℚ_[p])`.

## Main results

* `upperRamificationGroupInfinite_cyclotomic_eq_character_ker`: `G^u = χ⁻¹(1 + p^{r+1} ℤ_[p])`
  for `r < u ≤ r + 1`
* `upperRamificationGroupInfinite_cyclotomic_index`: `(G : G^u) = φ(p^{r+1})` for `r < u ≤ r + 1`
* `apfIndex_cyclotomicExtension_padic_add_one`: `i(u + 1) = p · i(u)` for `u > 0`
* `isStrictlyAPF_cyclotomicExtension_padic`: `ℚ_[p](ζ_{p^∞})/ℚ_[p]` is strictly APF
* `isStrictlyAPF_cyclotomicExtension`: `K(ζ_{p^∞})/K` is strictly APF for `K/ℚ_[p]` finite
* `cyclotomicCharacter_map_upperRamificationGroupInfinite`: the cyclotomic character of
  `Gal(Ω/ℚ_[p])` maps `Gal(Ω/ℚ_[p])^u` onto `1 + p^{r+1} ℤ_[p]` for `r < u ≤ r + 1`
* `exists_upperRamificationGroupInfinite_cyclotomic_index_add_ramificationIdx`: for `v` large,
  `(G_K : G_K^{v + e(K/ℚ_[p])}) = p · (G_K : G_K^v)` where `G_K = Gal(K(ζ_{p^∞})/K)`

## Notation

The local notation `Cyc` denotes `cyclotomicExtension (K := ℚ_[p]) p`.

## References

* [J.-P. Serre, *Local Fields*](https://doi.org/10.1007/978-1-4757-5673-9), Chapter IV, §4,
  Proposition 18.
* [J.-P. Wintenberger, *Le corps des normes de certaines extensions infinies de corps locaux;
  applications*](https://doi.org/10.24033/asens.1440), §1.2.
* [T. Liu, *On lattices in semi-stable representations: a proof of a conjecture of
  Breuil*](https://doi.org/10.1112/S0010437X0700317X), §5.1.
-/

@[expose] public section

noncomputable section

open FontaineWintenberger

namespace FalseTateExtension

variable (p : ℕ) [Fact p.Prime]

local notation "Cyc" => cyclotomicExtension (K := ℚ_[p]) p

/-- For `u ≥ -1`, `g ∈ Gal(ℚ_[p](ζ_{p^∞})/ℚ_[p])^u` if and only if the restriction of `g` to
`ℚ_[p](ζ_{p^{n+1}})` lies in `Gal(ℚ_[p](ζ_{p^{n+1}})/ℚ_[p])^u` for every `n`. -/
theorem mem_upperRamificationGroupInfinite_cyclotomic_iff
    {u : ℝ} (hu : -1 ≤ u) (g : Cyc ≃ₐ[ℚ_[p]] Cyc) :
    g ∈ upperRamificationGroupInfinite ℚ_[p] Cyc u ↔
      ∀ n, cyclotomicRestrictionToLayer p (n + 1) g ∈
        upperRamificationGroup
          (R := spectralIntegerRing ℚ_[p] (cyclotomicLayer (K := ℚ_[p]) p (n + 1)))
          (cyclotomicLayer (K := ℚ_[p]) p (n + 1) ≃ₐ[ℚ_[p]]
            cyclotomicLayer (K := ℚ_[p]) p (n + 1)) u := by
  rw [mem_upperRamificationGroupInfinite_iff_cofinal ℚ_[p] Cyc
    (cyclotomicFiniteLayer (K := ℚ_[p]) p)
    (fun D ↦ exists_le_cyclotomicFiniteLayer p D.toIntermediateField) hu]
  apply forall_congr'
  intro n
  rw [restrictNormal_cyclotomicFiniteLayer,
    ← upperRamificationGroup_map_autCongr ℚ_[p] (cyclotomicFiniteLayerEquiv (K := ℚ_[p]) p n) hu,
    Subgroup.mem_map_equiv]
  simp only [MulEquiv.symm_apply_apply]

/-- For `r < u ≤ r + 1`, `Gal(ℚ_[p](ζ_{p^∞})/ℚ_[p])^u` is the kernel of restriction to
`ℚ_[p](ζ_{p^{r+1}})`. -/
theorem upperRamificationGroupInfinite_cyclotomic_eq_ker
    (r : ℕ) {u : ℝ} (hu0 : (r : ℝ) < u) (hu1 : u ≤ (r : ℝ) + 1) :
    upperRamificationGroupInfinite ℚ_[p] Cyc u = (cyclotomicRestrictionToLayer p (r + 1)).ker := by
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
    · have hres : cyclotomicRestrictionToLayer p (n + 1) g = 1 := by
        rw [cyclotomicRestrictionToLayer_comp p (by omega : n + 1 ≤ r + 1), MonoidHom.comp_apply,
          hg, map_one]
      rw [hres]
      exact Subgroup.one_mem _
    · rw [upperRamificationGroup_cyclotomic_eq_comap_unitReduction p n r (by omega) hu0 hu1,
        Subgroup.mem_comap, MonoidHom.mem_ker, cyclotomicLayerCharacter_restrict]
      apply Units.ext
      change ZMod.castHom (pow_dvd_pow p (by omega : r + 1 ≤ n + 1)) (ZMod (p ^ (r + 1)))
          (PadicInt.toZModPow (n + 1) (cyclotomicExtensionCharacter p g : ℤ_[p])) = 1
      have hcomp := congrArg
        (fun f : ℤ_[p] →+* ZMod (p ^ (r + 1)) ↦
          f (cyclotomicExtensionCharacter p g : ℤ_[p]))
        (PadicInt.zmod_cast_comp_toZModPow (r + 1) (n + 1) (by omega))
      simp only [RingHom.comp_apply] at hcomp
      rw [hcomp]
      have hchar := cyclotomicLayerCharacter_restrict p (r + 1) g
      rw [hg, map_one] at hchar
      exact congrArg Units.val hchar.symm

/-- `G^0 = G` for `G = Gal(ℚ_[p](ζ_{p^∞})/ℚ_[p])`. -/
theorem upperRamificationGroupInfinite_cyclotomic_zero :
    upperRamificationGroupInfinite ℚ_[p] Cyc 0 = ⊤ := by
  apply top_unique
  intro g _
  rw [mem_upperRamificationGroupInfinite_cyclotomic_iff p (by norm_num)]
  intro n
  rw [upperRamificationGroup_cyclotomic_zero]
  trivial

/-- `G^u = G` for `-1 ≤ u ≤ 0`, where `G = Gal(ℚ_[p](ζ_{p^∞})/ℚ_[p])`. -/
theorem upperRamificationGroupInfinite_cyclotomic_of_nonpos
    {u : ℝ} (hu : -1 ≤ u) (hu0 : u ≤ 0) :
    upperRamificationGroupInfinite ℚ_[p] Cyc u = ⊤ := by
  apply top_unique
  rw [← upperRamificationGroupInfinite_cyclotomic_zero p]
  exact upperRamificationGroupInfinite_antitoneOn ℚ_[p] Cyc hu (by norm_num) hu0

/-- Every real `u > 0` lies in an interval `(r, r + 1]` with `r : ℕ`. -/
theorem exists_cyclotomic_upper_interval {u : ℝ} (hu : 0 < u) :
    ∃ r : ℕ, (r : ℝ) < u ∧ u ≤ (r : ℝ) + 1 := by
  have hc : 0 < Nat.ceil u := Nat.lt_ceil.mpr (by simpa using hu)
  refine ⟨Nat.ceil u - 1, Nat.lt_ceil.mp (by omega), ?_⟩
  have h := Nat.le_ceil u
  have hn : Nat.ceil u - 1 + 1 = Nat.ceil u := by omega
  have hcast : ((Nat.ceil u - 1 : ℕ) : ℝ) + 1 = (Nat.ceil u : ℝ) := by exact_mod_cast hn
  linarith

/-- For `r < u ≤ r + 1`, `Gal(ℚ_[p](ζ_{p^∞})/ℚ_[p])^u = χ⁻¹(1 + p^{r+1} ℤ_[p])`. -/
theorem upperRamificationGroupInfinite_cyclotomic_eq_character_ker
    (r : ℕ) {u : ℝ} (hu0 : (r : ℝ) < u) (hu1 : u ≤ (r : ℝ) + 1) :
    upperRamificationGroupInfinite ℚ_[p] Cyc u =
      ((Units.map (PadicInt.toZModPow (r + 1)).toMonoidHom).comp
        (cyclotomicExtensionCharacter (K := ℚ_[p]) p)).ker := by
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

/-- For `r < u ≤ r + 1`, `χ(Gal(ℚ_[p](ζ_{p^∞})/ℚ_[p])^u) = 1 + p^{r+1} ℤ_[p]`. -/
theorem upperRamificationGroupInfinite_cyclotomic_map_character
    (r : ℕ) {u : ℝ} (hu0 : (r : ℝ) < u) (hu1 : u ≤ (r : ℝ) + 1) :
    (upperRamificationGroupInfinite ℚ_[p] Cyc u).map (cyclotomicExtensionCharacter p) =
      (Units.map (PadicInt.toZModPow (r + 1)).toMonoidHom).ker := by
  rw [upperRamificationGroupInfinite_cyclotomic_eq_character_ker p r hu0 hu1]
  change ((Units.map (PadicInt.toZModPow (r + 1)).toMonoidHom).ker.comap
    (cyclotomicExtensionCharacter p)).map (cyclotomicExtensionCharacter p) = _
  rw [Subgroup.map_comap_eq, MonoidHom.range_eq_top.mpr
    (cyclotomicExtensionCharacter_surjective_padic p), top_inf_eq]

/-- For `r < u ≤ r + 1`, `(G : G^u) = φ(p^{r+1})` where `G = Gal(ℚ_[p](ζ_{p^∞})/ℚ_[p])`. -/
theorem upperRamificationGroupInfinite_cyclotomic_index
    (r : ℕ) {u : ℝ} (hu0 : (r : ℝ) < u) (hu1 : u ≤ (r : ℝ) + 1) :
    (upperRamificationGroupInfinite ℚ_[p] Cyc u).index = (p ^ (r + 1)).totient := by
  rw [upperRamificationGroupInfinite_cyclotomic_eq_ker p r hu0 hu1]
  change ((⊥ : Subgroup (cyclotomicLayer (K := ℚ_[p]) p (r + 1) ≃ₐ[ℚ_[p]]
    cyclotomicLayer (K := ℚ_[p]) p (r + 1))).comap
      (cyclotomicRestrictionToLayer p (r + 1))).index = _
  rw [Subgroup.index_comap_of_surjective _ (cyclotomicRestrictionToLayer_surjective p (r + 1)),
    Subgroup.index_bot, card_cyclotomicLayer_galois]

/-- For `u ≥ -1`, `Gal(ℚ_[p](ζ_{p^∞})/ℚ_[p])^u` has finite index. -/
theorem upperRamificationGroupInfinite_cyclotomic_finiteIndex
    {u : ℝ} (hu : -1 ≤ u) : (upperRamificationGroupInfinite ℚ_[p] Cyc u).FiniteIndex := by
  by_cases hu0 : u ≤ 0
  · rw [upperRamificationGroupInfinite_cyclotomic_of_nonpos p hu hu0]
    infer_instance
  · obtain ⟨r, hr0, hr1⟩ := exists_cyclotomic_upper_interval (lt_of_not_ge hu0)
    rw [upperRamificationGroupInfinite_cyclotomic_eq_ker p r hr0 hr1]
    infer_instance

/-- `ℚ_[p](ζ_{p^∞})/ℚ_[p]` is arithmetically profinite. -/
instance isAPF_cyclotomicExtension_padic : IsAPF ℚ_[p] Cyc := by
  rw [isAPF_iff_upperInfinite_finiteIndex]
  exact fun _ hu ↦ upperRamificationGroupInfinite_cyclotomic_finiteIndex p hu

/-- Wintenberger's index `i(u) = (G^0 : G^u)` of `ℚ_[p](ζ_{p^∞})/ℚ_[p]` is `φ(p^{r+1})` for
`r < u ≤ r + 1`. -/
theorem apfIndex_cyclotomicExtension_padic
    (r : ℕ) {u : ℝ} (hu0 : (r : ℝ) < u) (hu1 : u ≤ (r : ℝ) + 1) :
    apfIndex ℚ_[p] Cyc u = (p ^ (r + 1)).totient := by
  rw [apfIndex_eq_upperInfiniteRelIndex ℚ_[p] Cyc
    (by linarith [Nat.cast_nonneg (α := ℝ) r]),
    upperRamificationGroupInfinite_cyclotomic_zero p, Subgroup.relIndex_top_right]
  exact upperRamificationGroupInfinite_cyclotomic_index p r hu0 hu1

/-- For `u > 0`, `(G : G^{u+1}) = p · (G : G^u)` where `G = Gal(ℚ_[p](ζ_{p^∞})/ℚ_[p])`. -/
theorem upperRamificationGroupInfinite_cyclotomic_index_add_one
    {u : ℝ} (hu : 0 < u) :
    (upperRamificationGroupInfinite ℚ_[p] Cyc (u + 1)).index =
      p * (upperRamificationGroupInfinite ℚ_[p] Cyc u).index := by
  obtain ⟨r, hr0, hr1⟩ := exists_cyclotomic_upper_interval hu
  rw [upperRamificationGroupInfinite_cyclotomic_index p r hr0 hr1,
    upperRamificationGroupInfinite_cyclotomic_index p (r + 1)
      (by push_cast; linarith) (by push_cast; linarith),
    Nat.totient_prime_pow_succ (Fact.out : p.Prime),
    Nat.totient_prime_pow_succ (Fact.out : p.Prime), pow_succ]
  ring

/-- Wintenberger's index of `ℚ_[p](ζ_{p^∞})/ℚ_[p]` satisfies `i(u + 1) = p · i(u)` for
`u > 0`. -/
theorem apfIndex_cyclotomicExtension_padic_add_one {u : ℝ} (hu : 0 < u) :
    apfIndex ℚ_[p] Cyc (u + 1) = p * apfIndex ℚ_[p] Cyc u := by
  rw [apfIndex_eq_upperInfiniteRelIndex ℚ_[p] Cyc (by linarith : 0 ≤ u + 1),
    apfIndex_eq_upperInfiniteRelIndex ℚ_[p] Cyc hu.le,
    upperRamificationGroupInfinite_cyclotomic_zero p,
    Subgroup.relIndex_top_right, Subgroup.relIndex_top_right]
  exact upperRamificationGroupInfinite_cyclotomic_index_add_one p hu

/-- `ℚ_[p](ζ_{p^∞})/ℚ_[p]` is strictly arithmetically profinite. -/
instance isStrictlyAPF_cyclotomicExtension_padic : IsStrictlyAPF ℚ_[p] Cyc := by
  let := isAPF_cyclotomicExtension_padic p
  apply isStrictlyAPF_of_apfIndex_boundedGrowth ℚ_[p] Cyc
    (ℓ := 1) (C := (p : ℝ)) (U := 1) (by norm_num)
    (Nat.cast_pos.mpr (Fact.out : p.Prime).pos)
  intro u hu
  have h := apfIndex_cyclotomicExtension_padic_add_one p (by linarith : 0 < u)
  exact le_of_eq (by exact_mod_cast h)

section Compositum

variable {K : Type*} [Field K] [CharZero K]
    [Algebra (ℚ_[p]) K] [FiniteDimensional (ℚ_[p]) K]

omit [Algebra (ℚ_[p]) K] [FiniteDimensional (ℚ_[p]) K] in
/-- Every `p^n`-th root of unity in `K̄` lies in `K(ζ_{p^n})`. -/
theorem mem_cyclotomicLayer_of_pow_eq_one (n : ℕ) {ζ : AlgebraicClosure K}
    (hζ : ζ ^ (p ^ n) = 1) : ζ ∈ cyclotomicLayer (K := K) p n := by
  have : NeZero (p ^ n) := ⟨pow_ne_zero n (Fact.out : p.Prime).ne_zero⟩
  obtain ⟨j, _, rfl⟩ := (isPrimitiveRoot_zeta (K := K) p n).eq_pow_of_pow_eq_one hζ
  exact (cyclotomicLayer (K := K) p n).toSubalgebra.pow_mem
    (zeta_mem_cyclotomicLayer p n) j

/-- A `ℚ_[p]`-algebra embedding `ℚ_[p](ζ_{p^∞}) →ₐ[ℚ_[p]] K(ζ_{p^∞})`, induced by an
isomorphism of algebraic closures `ℚ̄_p ≃ K̄`. -/
def rationalCyclotomicEmbedding : Cyc →ₐ[ℚ_[p]] cyclotomicExtension (K := K) p := by
  let e := IsAlgClosure.equiv ℚ_[p] (AlgebraicClosure ℚ_[p]) (AlgebraicClosure K)
  let f := e.toAlgHom.comp (cyclotomicExtension (K := ℚ_[p]) p).val
  apply f.codRestrict ((cyclotomicExtension (K := K) p).restrictScalars ℚ_[p]).toSubalgebra
  intro x
  obtain ⟨n, hn⟩ := (mem_cyclotomicExtension_iff p (x : AlgebraicClosure ℚ_[p])).mp x.property
  have hroot : e (zeta (K := ℚ_[p]) p n) ∈ cyclotomicExtension (K := K) p := by
    apply cyclotomicLayer_le_cyclotomicExtension p n
    apply mem_cyclotomicLayer_of_pow_eq_one p n
    rw [← map_pow, zeta_pow_eq_one, map_one]
  have hle : cyclotomicLayer (K := ℚ_[p]) p n ≤
      ((cyclotomicExtension (K := K) p).restrictScalars ℚ_[p]).comap e.toAlgHom :=
    IntermediateField.adjoin_simple_le_iff.mpr hroot
  exact hle hn

/-- The root of unity `ζ_{p^n} ∈ K(ζ_{p^∞})` lies in the image of `ℚ_[p](ζ_{p^∞})`. -/
theorem zetaCycExt_mem_rationalCyclotomicEmbedding (n : ℕ) :
    zetaCycExt (K := K) p n ∈
      (rationalCyclotomicEmbedding (K := K) p).fieldRange := by
  have : NeZero (p ^ n) := ⟨pow_ne_zero n (Fact.out : p.Prime).ne_zero⟩
  have hprim := (isPrimitiveRoot_zetaCycExt (K := ℚ_[p]) p n).map_of_injective
    (rationalCyclotomicEmbedding (K := K) p).injective
  obtain ⟨j, _, hj⟩ := hprim.eq_pow_of_pow_eq_one
    (isPrimitiveRoot_zetaCycExt (K := K) p n).pow_eq_one
  rw [← hj]
  exact (rationalCyclotomicEmbedding (K := K) p).fieldRange.toSubalgebra.pow_mem
    ⟨zetaCycExt (K := ℚ_[p]) p n, rfl⟩ j

/-- `K(ζ_{p^∞})` as an algebra over `ℚ_[p](ζ_{p^∞})` via `rationalCyclotomicEmbedding`. -/
local instance (priority := 100) rationalCyclotomicEmbeddingAlgebra :
    Algebra Cyc (cyclotomicExtension (K := K) p) :=
  (rationalCyclotomicEmbedding (K := K) p).toRingHom.toAlgebra

/-- The tower `ℚ_[p] ⊆ ℚ_[p](ζ_{p^∞}) ⊆ K(ζ_{p^∞})`. -/
local instance (priority := 100) rationalCyclotomicEmbeddingTower :
    IsScalarTower ℚ_[p] Cyc (cyclotomicExtension (K := K) p) :=
  IsScalarTower.of_algHom (rationalCyclotomicEmbedding (K := K) p)

/-- `K(ζ_{p^∞})` is algebraic over `ℚ_[p]`. -/
local instance rationalCyclotomicBase_isAlgebraic :
    Algebra.IsAlgebraic ℚ_[p] (cyclotomicExtension (K := K) p) :=
  Algebra.IsAlgebraic.trans ℚ_[p] K (cyclotomicExtension (K := K) p)

/-- `K(ζ_{p^∞})` is generated over the image of `ℚ_[p](ζ_{p^∞})` by `K`. -/
theorem rationalCyclotomicEmbedding_adjoin_base :
    IntermediateField.adjoin Cyc
      ((IsScalarTower.toAlgHom ℚ_[p] K (cyclotomicExtension (K := K) p)).fieldRange :
        Set (cyclotomicExtension (K := K) p)) = ⊤ := by
  let A := IntermediateField.adjoin Cyc
    ((IsScalarTower.toAlgHom ℚ_[p] K (cyclotomicExtension (K := K) p)).fieldRange :
      Set (cyclotomicExtension (K := K) p))
  let D : IntermediateField K (AlgebraicClosure K) :=
    { A.toSubfield.map (cyclotomicExtension (K := K) p).val.toRingHom with
      algebraMap_mem' := fun k ↦ ⟨algebraMap K (cyclotomicExtension (K := K) p) k,
        IntermediateField.subset_adjoin Cyc _ ⟨k, rfl⟩, rfl⟩ }
  have hroots (n : ℕ) : zetaCycExt (K := K) p n ∈ A := by
    obtain ⟨z, hz⟩ := zetaCycExt_mem_rationalCyclotomicEmbedding (K := K) p n
    have hzA := A.algebraMap_mem z
    change rationalCyclotomicEmbedding p z ∈ A at hzA
    change rationalCyclotomicEmbedding p z = _ at hz
    rwa [hz] at hzA
  have hD : cyclotomicExtension (K := K) p ≤ D := by
    apply iSup_le
    intro n
    apply IntermediateField.adjoin_simple_le_iff.mpr
    exact ⟨zetaCycExt (K := K) p n, hroots n, rfl⟩
  apply top_unique
  intro x _
  obtain ⟨y, hy, hxy⟩ := hD x.property
  have heq : y = x := Subtype.ext hxy
  exact heq ▸ hy

/-- In a tower `K / E / F`, if `K` is generated over `E` by an intermediate field of `K / F`
that is finite over `F`, then `K` is finite over `E`. -/
theorem finiteDimensional_of_adjoin_intermediateField_eq_top
    {F E K : Type*} [Field F] [Field E] [Field K] [Algebra F E] [Algebra F K] [Algebra E K]
    [IsScalarTower F E K] (L : IntermediateField F K) [FiniteDimensional F L]
    (h : IntermediateField.adjoin E (L : Set K) = ⊤) : FiniteDimensional E K :=
  have : FiniteDimensional E (IntermediateField.adjoin E (L : Set K)) :=
    Module.rank_lt_aleph0_iff.mp
      ((IntermediateField.adjoin_rank_le_of_isAlgebraic_right E L).trans_lt
        (Module.rank_lt_aleph0 F L))
  ((IntermediateField.equivOfEq h).trans
    IntermediateField.topEquiv).toLinearEquiv.finiteDimensional

/-- For `K/ℚ_[p]` finite, `K(ζ_{p^∞})` is finite over the image of `ℚ_[p](ζ_{p^∞})`. -/
theorem rationalCyclotomicEmbedding_finiteDimensional :
    FiniteDimensional Cyc (cyclotomicExtension (K := K) p) :=
  let : FiniteDimensional ℚ_[p]
      (IsScalarTower.toAlgHom ℚ_[p] K (cyclotomicExtension (K := K) p)).fieldRange :=
    Module.Finite.equiv (IsScalarTower.toAlgHom ℚ_[p] K
      (cyclotomicExtension (K := K) p)).equivFieldRange.toLinearEquiv
  finiteDimensional_of_adjoin_intermediateField_eq_top _
    (rationalCyclotomicEmbedding_adjoin_base (K := K) p)

/-- For `K/ℚ_[p]` finite, `K(ζ_{p^∞})/ℚ_[p]` is strictly arithmetically profinite. -/
theorem isStrictlyAPF_cyclotomicExtension_over_padic :
    IsStrictlyAPF ℚ_[p] (cyclotomicExtension (K := K) p) := by
  let := rationalCyclotomicEmbedding_finiteDimensional (K := K) p
  exact (isStrictlyAPF_finite_extension_iff ℚ_[p] (cyclotomicExtension (K := K) p) Cyc).mpr
    (isStrictlyAPF_cyclotomicExtension_padic p)

end Compositum

section ValuedBase

variable (K : Type*) [NontriviallyNormedField K] [CharZero K]
    [IsCompleteDiscreteValuedField K]
    [NormedAlgebra (ℚ_[p]) K] [FiniteDimensional (ℚ_[p]) K]

/-- For `K/ℚ_[p]` finite, `K(ζ_{p^∞})/K` is strictly arithmetically profinite. -/
instance isStrictlyAPF_cyclotomicExtension :
    IsStrictlyAPF K (cyclotomicExtension (K := K) p) := by
  let := rationalCyclotomicBase_isAlgebraic (K := K) p
  exact (isStrictlyAPF_finiteBase_iff_of_normedAlgebra ℚ_[p] K
    (cyclotomicExtension (K := K) p)).mp
      (isStrictlyAPF_cyclotomicExtension_over_padic (K := K) p)

/-- For `K/ℚ_[p]` finite, `K(ζ_{p^∞})/K` is arithmetically profinite. -/
instance isAPF_cyclotomicExtension :
    IsAPF K (cyclotomicExtension (K := K) p) := by
  exact (isStrictlyAPF_cyclotomicExtension p K).toIsAPF

end ValuedBase

section CharacterTransport

variable (F : Type*) [NontriviallyNormedField F] [IsCompleteDiscreteValuedField F]
    [PerfectField (𝓀[F])]

omit [PerfectField (𝓀[F])] in
/-- An `F`-algebra isomorphism `e : E ≃ₐ[F] E'` identifies the image of `Gal(E/F)^u` under the
cyclotomic character of `E` with the image of `Gal(E'/F)^u` under the cyclotomic character of
`E'`. -/
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

/-- For `u ≥ -1`, the image of `Gal(F(ζ_{p^∞})/F)^u` under the cyclotomic character equals the
image of `Gal(F̄/F)^u` under the cyclotomic character of `F̄`. -/
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

/-- For an algebraic closure `Ω` of `ℚ_[p]` and `r < u ≤ r + 1`, the cyclotomic character of `Ω`
maps `Gal(Ω/ℚ_[p])^u` onto `1 + p^{r+1} ℤ_[p]`. -/
theorem cyclotomicCharacter_map_upperRamificationGroupInfinite
    (Ω : Type*) [Field Ω] [Algebra ℚ_[p] Ω] [IsAlgClosure ℚ_[p] Ω]
    (r : ℕ) {u : ℝ} (hu0 : (r : ℝ) < u) (hu1 : u ≤ (r : ℝ) + 1) :
    (upperRamificationGroupInfinite ℚ_[p] Ω u).map
      ((_root_.cyclotomicCharacter Ω p).comp
        (MulSemiringAction.toRingAut (Ω ≃ₐ[ℚ_[p]] Ω) Ω)) =
      (Units.map (PadicInt.toZModPow (r + 1)).toMonoidHom).ker := by
  let : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ_[p]
  let : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ_[p] Ω).injective
  have hu : -1 ≤ u := by linarith [Nat.cast_nonneg (α := ℝ) r]
  let i : Cyc →ₐ[ℚ_[p]] Ω :=
    (IsAlgClosure.equiv ℚ_[p] (AlgebraicClosure ℚ_[p]) Ω).toAlgHom.comp
      (cyclotomicExtension (K := ℚ_[p]) p).val
  let e := i.equivFieldRange
  let : IsGalois ℚ_[p] i.fieldRange := IsGalois.of_algEquiv e
  let f : (Ω ≃ₐ[ℚ_[p]] Ω) →* (Cyc ≃ₐ[ℚ_[p]] Cyc) :=
    e.symm.autCongr.toMonoidHom.comp (AlgEquiv.restrictNormalHom i.fieldRange)
  have hf : (upperRamificationGroupInfinite ℚ_[p] Ω u).map f =
      upperRamificationGroupInfinite ℚ_[p] Cyc u := by
    rw [show f = e.symm.autCongr.toMonoidHom.comp
        (AlgEquiv.restrictNormalHom i.fieldRange) from rfl,
      ← Subgroup.map_map,
      restrictNormalHom_map_upperRamificationGroupInfinite ℚ_[p] Ω i.fieldRange u hu,
      upperRamificationGroupInfinite_map_autCongr ℚ_[p] e.symm hu]
  have hχ : ((_root_.cyclotomicCharacter Ω p).comp
      (MulSemiringAction.toRingAut (Ω ≃ₐ[ℚ_[p]] Ω) Ω)) =
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
    [IsCompleteDiscreteValuedField K]
    [NormedAlgebra (ℚ_[p]) K] [FiniteDimensional (ℚ_[p]) K]
    [Algebra K (SeparableClosure (ℚ_[p]))]
    [IsScalarTower (ℚ_[p]) K (SeparableClosure (ℚ_[p]))]

/-- For `u ≥ -1` and `ψ = ψ_{K/ℚ_[p]}`, the image of `Gal(K^sep/K)^{ψ(u)}` under the cyclotomic
character of `K^sep` equals the image of `Gal(ℚ_p^sep/K) ∩ Gal(ℚ_p^sep/ℚ_[p])^u` under the
cyclotomic character of `ℚ_p^sep`. -/
theorem cyclotomicCharacter_map_upper_finiteBase {u : ℝ} (hu : -1 ≤ u) :
    (upperRamificationGroupInfinite K (SeparableClosure K) (apfPsi ℚ_[p] K u)).map
        ((_root_.cyclotomicCharacter (SeparableClosure K) p).comp
          (MulSemiringAction.toRingAut
            (SeparableClosure K ≃ₐ[K] SeparableClosure K) (SeparableClosure K))) =
      ((IsScalarTower.toAlgHom ℚ_[p] K (SeparableClosure ℚ_[p])).fieldRange.fixingSubgroup ⊓
        upperRamificationGroupInfinite ℚ_[p] (SeparableClosure ℚ_[p]) u).map
        ((_root_.cyclotomicCharacter (SeparableClosure ℚ_[p]) p).comp
          (MulSemiringAction.toRingAut
            (SeparableClosure ℚ_[p] ≃ₐ[ℚ_[p]] SeparableClosure ℚ_[p])
              (SeparableClosure ℚ_[p]))) := by
  let := normedAlgebra_residueField_perfectField ℚ_[p] K
  let ρ := AbstractFiniteBase.closureHom ℚ_[p] K
  have hχ : ((_root_.cyclotomicCharacter (SeparableClosure K) p).comp
      (MulSemiringAction.toRingAut
        (SeparableClosure K ≃ₐ[K] SeparableClosure K) (SeparableClosure K))) =
      (((_root_.cyclotomicCharacter (SeparableClosure ℚ_[p]) p).comp
        (MulSemiringAction.toRingAut
          (SeparableClosure ℚ_[p] ≃ₐ[ℚ_[p]] SeparableClosure ℚ_[p])
              (SeparableClosure ℚ_[p]))).comp ρ) := by
    apply MonoidHom.ext
    intro g
    exact cyclotomicCharacter_eq_of_intertwines p
      (AbstractFiniteBase.closureEquiv ℚ_[p] K).toRingHom g.toRingEquiv (ρ g).toRingEquiv
      (fun x ↦ (AbstractFiniteBase.closureHom_apply ℚ_[p] K g x).symm)
  have hupper : (upperRamificationGroupInfinite ℚ_[p] (SeparableClosure ℚ_[p]) u).comap ρ =
      upperRamificationGroupInfinite K (SeparableClosure K) (apfPsi ℚ_[p] K u) :=
    AbstractFiniteBase.comap_upper ℚ_[p] K hu
  rw [hχ, ← Subgroup.map_map, ← hupper,
    Subgroup.map_comap_eq, AbstractFiniteBase.closureHom_range ℚ_[p] K]

/-- For `u ≥ -1` and `ψ = ψ_{K/ℚ_[p]}`, the image of `Gal(K(ζ_{p^∞})/K)^{ψ(u)}` under the
cyclotomic character equals the image of `Gal(ℚ_p^sep/K) ∩ Gal(ℚ_p^sep/ℚ_[p])^u` under the
cyclotomic character of `ℚ_p^sep`. -/
theorem cyclotomicExtension_map_upper_finiteBase {u : ℝ} (hu : -1 ≤ u) :
    (upperRamificationGroupInfinite K (cyclotomicExtension (K := K) p) (apfPsi ℚ_[p] K u)).map
        (cyclotomicExtensionCharacter p) =
      ((IsScalarTower.toAlgHom ℚ_[p] K (SeparableClosure ℚ_[p])).fieldRange.fixingSubgroup ⊓
        upperRamificationGroupInfinite ℚ_[p] (SeparableClosure ℚ_[p]) u).map
        ((_root_.cyclotomicCharacter (SeparableClosure ℚ_[p]) p).comp
          (MulSemiringAction.toRingAut
            (SeparableClosure ℚ_[p] ≃ₐ[ℚ_[p]] SeparableClosure ℚ_[p])
              (SeparableClosure ℚ_[p]))) := by
  let := normedAlgebra_residueField_perfectField ℚ_[p] K
  have hv := IsAPF.apfPsi_mem_Ici ℚ_[p] K hu
  rw [cyclotomicExtension_map_upper_from_algebraicClosure p K hv,
    ← cyclotomicCharacter_map_upper_autCongr p K
      (IsAlgClosure.equiv K (SeparableClosure K) (AlgebraicClosure K)) hv]
  exact cyclotomicCharacter_map_upper_finiteBase p K hu

end CommonClosureCharacter

section EventualCharacterImage

variable (K : Type*) [NontriviallyNormedField K] [CharZero K]
    [IsCompleteDiscreteValuedField K]
    [NormedAlgebra (ℚ_[p]) K] [FiniteDimensional (ℚ_[p]) K]

/-- There is `U ≥ 1` such that for all `u ≥ U` and `r < u ≤ r + 1`,
`χ(Gal(K(ζ_{p^∞})/K)^{ψ(u)}) = 1 + p^{r+1} ℤ_[p]`, where `ψ = ψ_{K/ℚ_[p]}`. -/
theorem exists_cyclotomicExtension_upper_principal_finiteBase :
    ∃ U : ℝ, 1 ≤ U ∧ ∀ u : ℝ, U ≤ u → ∀ r : ℕ,
      (r : ℝ) < u → u ≤ (r : ℝ) + 1 →
      (upperRamificationGroupInfinite K (cyclotomicExtension (K := K) p) (apfPsi ℚ_[p] K u)).map
          (cyclotomicExtensionCharacter p) =
        (Units.map (PadicInt.toZModPow (r + 1)).toMonoidHom).ker := by
  obtain ⟨i⟩ := nonempty_separableClosure_embeddings ℚ_[p] K
  let : Algebra K (SeparableClosure ℚ_[p]) := i.toRingHom.toAlgebra
  let : IsScalarTower ℚ_[p] K (SeparableClosure ℚ_[p]) := IsScalarTower.of_algHom i
  let S := i.fieldRange
  let : FiniteDimensional ℚ_[p] S := Module.Finite.equiv i.equivFieldRange.toLinearEquiv
  obtain ⟨U, _, hfix⟩ := exists_absoluteUpper_le_fixingSubgroup_of_finite ℚ_[p] S
  refine ⟨max U 1, le_max_right _ _, fun u hu r hr0 hr1 ↦ ?_⟩
  rw [cyclotomicExtension_map_upper_finiteBase p K
    (by linarith [(le_max_right U 1).trans hu] : -1 ≤ u)]
  have hle : upperRamificationGroupInfinite ℚ_[p] (SeparableClosure ℚ_[p]) u ≤ S.fixingSubgroup :=
    hfix u ((le_max_left _ _).trans hu)
  have hi : IsScalarTower.toAlgHom ℚ_[p] K (SeparableClosure ℚ_[p]) = i := by
    ext x
    rfl
  rw [hi, inf_eq_right.mpr hle]
  exact cyclotomicCharacter_map_upperRamificationGroupInfinite p (SeparableClosure ℚ_[p])
    r hr0 hr1

/-- There is `U ≥ 1` such that for all `u ≥ U`,
`(G_K : G_K^{ψ(u)}) · (ℤ_[p]ˣ : χ(G_K)) = (G : G^u)`, where `G_K = Gal(K(ζ_{p^∞})/K)`,
`G = Gal(ℚ_[p](ζ_{p^∞})/ℚ_[p])` and `ψ = ψ_{K/ℚ_[p]}`. -/
theorem exists_cyclotomicExtension_upper_index_finiteBase :
    ∃ U : ℝ, 1 ≤ U ∧ ∀ u : ℝ, U ≤ u →
      (upperRamificationGroupInfinite K (cyclotomicExtension (K := K) p)
          (apfPsi ℚ_[p] K u)).index * (cyclotomicExtensionCharacter (K := K) p).range.index =
        (upperRamificationGroupInfinite ℚ_[p] Cyc u).index := by
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

/-- There is `V ≥ 0` such that for all `v ≥ V`,
`(G_K : G_K^{v + e(K/ℚ_[p])}) = p · (G_K : G_K^v)`, where `G_K = Gal(K(ζ_{p^∞})/K)`. -/
theorem exists_upperRamificationGroupInfinite_cyclotomic_index_add_ramificationIdx :
    ∃ V : ℝ, 0 ≤ V ∧ ∀ v : ℝ, V ≤ v →
      (upperRamificationGroupInfinite K (cyclotomicExtension (K := K) p)
        (v + ((IsLocalRing.maximalIdeal
          𝒪[K]).ramificationIdx
            𝒪[ℚ_[p]] : ℝ))).index =
        p * (upperRamificationGroupInfinite K (cyclotomicExtension (K := K) p) v).index := by
  obtain ⟨A, hA, hindex⟩ := exists_cyclotomicExtension_upper_index_finiteBase p K
  obtain ⟨T, _, hshift⟩ := exists_apfPsi_normed_ramificationIdx_shift ℚ_[p] K
  let U := max A T
  have hU : 1 ≤ U := hA.trans (le_max_left _ _)
  refine ⟨apfPsi ℚ_[p] K U,
    (by linarith : 0 ≤ U).trans (IsAPF.le_apfPsi ℚ_[p] K U), fun v hv ↦ ?_⟩
  let u := apfPhi ℚ_[p] K v
  have hpsi : apfPsi ℚ_[p] K u = v := apfPsi_apfPhi ℚ_[p] K v
  have hu : U ≤ u := (IsAPF.strictMono_apfPsi ℚ_[p] K).le_iff_le.mp (by
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
