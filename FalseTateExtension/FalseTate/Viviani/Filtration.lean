/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FalseTateExtension.FalseTate.Viviani.Preliminaries
public import FalseTateExtension.Kummer.APF
public import FalseTateExtension.FalseTate.FiniteGaloisGroup
public import FontaineWintenberger.APF.Finite.ConstantIndex
public import FontaineWintenberger.Ramification.Herbrand.Interval
public import FontaineWintenberger.Ramification.Upper.Transport
public import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# Viviani's ramification filtration

The upper and lower ramification groups and the Herbrand functions of `ℚ_p(π^{1/p^{n+1}},
ζ_{p^{n+1}})/ℚ_p`, `p ≠ 2`: the upper group on `(r, r + 1]` and on `(r + 1, r + 1 + 1/(p-1)]` is the
product of the translation subgroup of level `r + 1` with a principal-unit subgroup; the inverse
Herbrand function at the breaks is `(2p^{2i} + p - 1)/(p + 1)` and `(p-1)(p^{2i+1} + 1)/(p + 1)`.

## References

* Viviani, *Ramification groups and Artin conductors of radical extensions of ℚ*, Corollary 6.10,
  with the correction of FalseTateLift, Remark 5.2.
-/

@[expose] public section

noncomputable section

namespace FalseTateExtension

open IsDiscreteValuationRing FontaineWintenberger

variable (p : ℕ) [Fact p.Prime]

section Upper

variable {p} (π : 𝒪[ℚ_[p]])
  [hp₂ : Fact (p ≠ 2)] [hπ : Fact (Irreducible π)]

local notation "D(" n ")" => falseTateLayer p (π : ℚ_[p]) (n + (1 : ℕ)) (n + (1 : ℕ))
local notation "O(" n ")" => spectralIntegerRing ℚ_[p] D(n)
local notation "G(" n ")" => D(n) ≃ₐ[ℚ_[p]] D(n)

local instance vivianiCyclotomicAlgebra (n : ℕ) :
    Algebra (cyclotomicLayer (K := ℚ_[p]) p (n + 1)) D(n) :=
  (finiteCyclotomicInclusion p (π : ℚ_[p]) (n + 1)).toRingHom.toAlgebra

local instance vivianiCyclotomicScalarTower (n : ℕ) :
    IsScalarTower ℚ_[p] (cyclotomicLayer (K := ℚ_[p]) p (n + 1)) D(n) :=
  IsScalarTower.of_algebraMap_eq (congrFun rfl)

/-- The image of the upper group under the checked finite
affine isomorphism. This retains its spectral integer ring. -/
def finiteUpperAffineGroup (n : ℕ) (u : ℝ) :
    Subgroup (FullFiniteAffineGroup p (n + 1)) := by
  let e : G(n) ≃* FullFiniteAffineGroup p (n + 1) :=
    finiteDiagonalGaloisEquiv_padic p π (n + 1)
  let U : Subgroup G(n) := upperRamificationGroup (R := O(n)) G(n) u
  exact U.map e.toMonoidHom

instance finiteUpperAffineGroup_normal (n : ℕ) (u : ℝ) :
    (finiteUpperAffineGroup π n u).Normal :=
  Subgroup.Normal.map inferInstance _
    (finiteDiagonalGaloisEquiv_padic p π (n + 1)).surjective

/-- The pure radical fixer becomes precisely the pure-unit factor. -/
theorem finiteRadicalFixing_map_affine (n : ℕ) :
    ((finiteRadicalInclusion p (π : ℚ_[p]) (n + 1)).fieldRange.fixingSubgroup : Subgroup G(n)).map
      (finiteDiagonalGaloisEquiv_padic p π (n + 1)).toMonoidHom =
    (SemidirectProduct.inr : (ZMod (p ^ (n + 1)))ˣ →*
      FullFiniteAffineGroup p (n + 1)).range := by
  ext x
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact (finiteDiagonalGaloisEquiv_padic_mem_units p π (n + 1) g).mpr hg
  · intro hx
    obtain ⟨g, rfl⟩ := (finiteDiagonalGaloisEquiv_padic p π (n + 1)).surjective x
    exact ⟨g, (finiteDiagonalGaloisEquiv_padic_mem_units p π (n + 1) g).mp hx, rfl⟩

/-- The index of the nonnormal radical subfield measures
the translation intersection of the upper group. -/
theorem finiteUpperAffine_translation_index (n : ℕ) {u : ℝ} (hu : 0 ≤ u) :
    ((finiteUpperAffineGroup π n u).comap SemidirectProduct.inl).index =
      p ^ radicalTranslationDepth p (n + 1) u := by
  have := falseTateLayer_isGalois p (π : ℚ_[p]) (n + 1)
  let M := (finiteRadicalInclusion p (π : ℚ_[p]) (n + 1)).fieldRange
  have hi := apfIndex_eq_subgroupRelIndex_of_finiteGalois ℚ_[p] D(n) M hu
  have hz : upperRamificationGroup (R := O(n)) G(n) 0 = ⊤ := by
    simpa only [upperRamificationGroup_zero, lowerRamificationGroup_zero] using
      lowerRamificationGroup_falseTateLayer_zero p π n
  simp only [hz, inf_top_eq, Subgroup.relIndex_top_right] at hi
  calc
    _ = ((SemidirectProduct.inr : (ZMod (p ^ (n + 1)))ˣ →*
        FullFiniteAffineGroup p (n + 1)).range ⊔ finiteUpperAffineGroup π n u).index :=
      (finiteAffine_units_sup_index (n + 1) _).symm
    _ = ((M.fixingSubgroup ⊔ upperRamificationGroup (R := O(n)) G(n) u).map
        (finiteDiagonalGaloisEquiv_padic p π (n + 1)).toMonoidHom).index := by
      rw [Subgroup.map_sup, finiteRadicalFixing_map_affine π]
      rfl
    _ = (M.fixingSubgroup ⊔ upperRamificationGroup (R := O(n)) G(n) u).index :=
      Subgroup.index_map_equiv _ (finiteDiagonalGaloisEquiv_padic p π (n + 1))
    _ = apfIndex ℚ_[p] M u := hi.symm
    _ = apfIndex ℚ_[p] (radicalLayer p (π : ℚ_[p]) (n + 1)) u :=
      (apfIndex_algEquiv ℚ_[p] (radicalLayer p (π : ℚ_[p]) (n + 1))
        (finiteRadicalInclusion p (π : ℚ_[p]) (n + 1)).equivFieldRange u).symm
    _ = _ := radicalLayer_apfIndex_eq_pow_translationDepth p π (n + 1) hu

/-- Cyclic subgroup uniqueness turns the index into the
translation subgroup, without a separate assumed depth certificate. -/
theorem finiteUpperAffine_translation (n : ℕ) {u : ℝ} (hu : 0 ≤ u) :
    (finiteUpperAffineGroup π n u).comap SemidirectProduct.inl =
      finiteTranslationSubgroup p (n + 1) (radicalTranslationDepth p (n + 1) u) := by
  apply IsCyclic.subgroup_eq_iff_index_eq.mpr
  rw [finiteUpperAffine_translation_index π n hu,
    finiteTranslationSubgroup_index p _ _ (radicalTranslationDepth_le p _ _)]

/-- The unit projection is exactly the upper group of the finite
cyclotomic field, by restriction with its own spectral integers. -/
theorem finiteUpperAffine_unit_projection (n : ℕ) {u : ℝ} (hu : -1 ≤ u) :
    (finiteUpperAffineGroup π n u).map SemidirectProduct.rightHom =
      (upperRamificationGroup (R := spectralIntegerRing ℚ_[p]
        (cyclotomicLayer (K := ℚ_[p]) p (n + 1)))
          (cyclotomicLayer (K := ℚ_[p]) p (n + 1) ≃ₐ[ℚ_[p]]
            cyclotomicLayer (K := ℚ_[p]) p (n + 1)) u).map
        (cyclotomicLayerCharacter p (n + 1)) := by
  have := falseTateLayer_isGalois p (π : ℚ_[p]) (n + 1)
  have hc : SemidirectProduct.rightHom.comp
      (finiteDiagonalGaloisEquiv_padic p π (n + 1)).toMonoidHom =
      (cyclotomicLayerCharacter p (n + 1)).comp
        (diagonalCyclotomicRestriction p (π : ℚ_[p]) (n + 1)) := by
    apply MonoidHom.ext
    intro g
    exact (cyclotomicLayerCharacterOver_diagonalRestriction p (π : ℚ_[p]) (n + 1) g).symm
  have hr := restrictNormalHom_map_upperRamificationGroup_tower ℚ_[p]
    (cyclotomicLayer (K := ℚ_[p]) p (n + 1)) D(n) u hu
  change (upperRamificationGroup (R := O(n)) G(n) u).map
    (diagonalCyclotomicRestriction p (π : ℚ_[p]) (n + 1)) = _ at hr
  rw [finiteUpperAffineGroup, Subgroup.map_map, hc, ← Subgroup.map_map, hr]

/-- Every positive finite cyclotomic interval has its exact principal-unit
projection, including its right endpoint. -/
theorem finiteUpperAffine_unit_interval (n r : ℕ) (hr : r ≤ n)
    {u : ℝ} (hu0 : (r : ℝ) < u) (hu1 : u ≤ (r : ℝ) + 1) :
    (finiteUpperAffineGroup π n u).map SemidirectProduct.rightHom =
      finiteUnitSubgroup p (n + 1) (r + 1) := by
  rw [finiteUpperAffine_unit_projection π n (by
    linarith [Nat.cast_nonneg (α := ℝ) r]),
    upperRamificationGroup_cyclotomic_eq_comap_unitReduction p n r hr hu0 hu1,
    Subgroup.map_comap_eq_self_of_surjective (cyclotomicLayerCharacter_surjective p (n + 1))]
  exact (finiteUnitSubgroup_eq_kernel p (n + 1) (r + 1) (by omega)).symm

/-- After the final cyclotomic break the unit projection is trivial. -/
theorem finiteUpperAffine_unit_tail (n : ℕ) {u : ℝ} (hu : (n : ℝ) < u) :
    (finiteUpperAffineGroup π n u).map SemidirectProduct.rightHom = ⊥ := by
  rw [finiteUpperAffine_unit_projection π n (by
    linarith [Nat.cast_nonneg (α := ℝ) n]),
    upperRamificationGroup_cyclotomic_eq_bot p n hu, Subgroup.map_bot]

/-- The finite upper group in affine coordinates on every positive
cyclotomic interval, with its strict-threshold translation depth. -/
theorem finiteUpperAffine_eq_interval (n r : ℕ) (hr : r ≤ n)
    {u : ℝ} (hu0 : (r : ℝ) < u) (hu1 : u ≤ (r : ℝ) + 1) :
    finiteUpperAffineGroup π n u =
      finiteAffineSubgroup p (n + 1) (radicalTranslationDepth p (n + 1) u)
        (finiteUnitSubgroup p (n + 1) (r + 1)) := by
  ext g
  rw [mem_finiteAffine_normal_iff (n + 1),
    finiteUpperAffine_translation π n (by
      linarith [Nat.cast_nonneg (α := ℝ) r]),
    finiteUpperAffine_unit_interval π n r hr hu0 hu1]
  rfl

/-- The finite upper group after the final cyclotomic break is its
translation subgroup with the same base depth. -/
theorem finiteUpperAffine_eq_tail (n : ℕ) {u : ℝ} (hu : (n : ℝ) < u) :
    finiteUpperAffineGroup π n u =
      finiteAffineSubgroup p (n + 1) (radicalTranslationDepth p (n + 1) u) ⊥ := by
  ext g
  rw [mem_finiteAffine_normal_iff (n + 1),
    finiteUpperAffine_translation π n (by
      linarith [Nat.cast_nonneg (α := ℝ) n]),
    finiteUpperAffine_unit_tail π n hu]
  rfl

include hp₂ hπ in
/-- The upper index on each closed cyclotomic interval. -/
theorem upperRamificationGroup_falseTate_index (n r : ℕ) (hr : r ≤ n)
    {u : ℝ} (hu0 : (r : ℝ) < u) (hu1 : u ≤ (r : ℝ) + 1) :
    (upperRamificationGroup (R := O(n)) G(n) u).index =
      (p ^ (r + 1)).totient * p ^ radicalTranslationDepth p (n + 1) u := by
  have he : (finiteUpperAffineGroup π n u).index =
      (upperRamificationGroup (R := O(n)) G(n) u).index :=
    Subgroup.index_map_equiv _ (finiteDiagonalGaloisEquiv_padic p π (n + 1))
  rw [← he, finiteAffine_normal_index,
    finiteUpperAffine_translation_index π n (by linarith [Nat.cast_nonneg (α := ℝ) r]),
    finiteUpperAffine_unit_interval π n r hr hu0 hu1,
    finiteUnitSubgroup_eq_kernel p _ _ (by omega),
    ZMod.index_ker_unitsMap_prime_pow p n (r + 1) (by omega)]

include hp₂ hπ in
/-- The upper index after the final cyclotomic break. -/
theorem upperRamificationGroup_falseTate_index_tail (n : ℕ) {u : ℝ} (hu : (n : ℝ) < u) :
    (upperRamificationGroup (R := O(n)) G(n) u).index =
      (p ^ (n + 1)).totient * p ^ radicalTranslationDepth p (n + 1) u := by
  have he : (finiteUpperAffineGroup π n u).index =
      (upperRamificationGroup (R := O(n)) G(n) u).index :=
    Subgroup.index_map_equiv _ (finiteDiagonalGaloisEquiv_padic p π (n + 1))
  rw [← he, finiteAffine_normal_index,
    finiteUpperAffine_translation_index π n (by linarith [Nat.cast_nonneg (α := ℝ) n]),
    finiteUpperAffine_unit_tail π n hu, Subgroup.index_bot]
  have : NeZero (p ^ (n + 1)) := ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
  simp only [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient]

/-- The upper group at every fractional Kummer break, including both final
breaks and the single first-layer break, with the finite truncation. -/
theorem finiteUpperAffine_fractional (n i : ℕ) (hi : 1 ≤ i) (hin : i ≤ n + 1) :
    finiteUpperAffineGroup π n ((i : ℝ) + 1 / ((p : ℝ) - 1)) =
      finiteAffineSubgroup p (n + 1) (i - 1) (finiteUnitSubgroup p (n + 1) (i + 1)) := by
  have hδ := viviani_fraction_pos_lt_one p
  by_cases h : i ≤ n
  · rw [finiteUpperAffine_eq_interval π n i h (by linarith) (by linarith),
      radicalTranslationDepth_fractional p (n + 1) i hi hin]
  · have hieq : i = n + 1 := by omega
    rw [finiteUpperAffine_eq_tail π n (by exact_mod_cast
      (show (n : ℝ) < (i : ℝ) + 1 / ((p : ℝ) - 1) by
        have : (n : ℝ) < i := by exact_mod_cast (show n < i by omega)
        linarith)), radicalTranslationDepth_fractional p (n + 1) i hi hin,
      finiteUnitSubgroup_eq_bot p (n + 1) (i + 1) (by omega)]

/-- The integer-break upper group; i=0 includes upper index one. -/
theorem finiteUpperAffine_integer (n i : ℕ) (hi : i ≤ n) :
    finiteUpperAffineGroup π n ((i : ℝ) + 1) =
      finiteAffineSubgroup p (n + 1) i (finiteUnitSubgroup p (n + 1) (i + 1)) := by
  rw [finiteUpperAffine_eq_interval π n i hi (by linarith) le_rfl,
    radicalTranslationDepth_integer p (n + 1) i (by omega)]

local notation "δ" => 1 / ((p : ℝ) - 1)
local notation "Ψ(" n ")" => inverseHerbrandFunction (R := O(n)) G(n)

include hp₂ hπ in
/-- Full inertia identifies the index with the full upper index. -/
theorem apfIndex_falseTateLayer_eq_upperIndex (n : ℕ) {u : ℝ} (hu : 0 ≤ u) :
    apfIndex ℚ_[p] D(n) u = (upperRamificationGroup (R := O(n)) G(n) u).index := by
  have := falseTateLayer_isGalois p (π : ℚ_[p]) (n + 1)
  have hz : upperRamificationGroup (R := O(n)) G(n) 0 = ⊤ := by
    simpa only [upperRamificationGroup_zero, lowerRamificationGroup_zero] using
      lowerRamificationGroup_falseTateLayer_zero p π n
  rw [apfIndex_eq_upperRelIndex ℚ_[p] D(n) hu, hz, Subgroup.relIndex_top_right]

include hp₂ hπ in
theorem viviani_inverse_affine (n : ℕ) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    (c : ℕ) (hc : ∀ u ∈ Set.Ioc a b,
      (upperRamificationGroup (R := O(n)) G(n) u).index = c) :
    Ψ(n) b - Ψ(n) a = (b - a) * c := by
  have := falseTateLayer_isGalois p (π : ℚ_[p]) (n + 1)
  rw [← apfPsi_eq_inverseHerbrandFunction ℚ_[p] D(n) (by linarith : -1 ≤ a),
    ← apfPsi_eq_inverseHerbrandFunction ℚ_[p] D(n) (by linarith : -1 ≤ b)]
  exact apfPsi_sub_apfPsi_of_apfIndex_eq ℚ_[p] D(n) ha hab c fun u hu =>
    (apfIndex_falseTateLayer_eq_upperIndex π n (ha.trans hu.1.le)).trans (hc u hu)

include hp₂ hπ in
theorem upperRamificationGroup_falseTate_index_initial (n : ℕ) {u : ℝ}
    (hu : 0 < u) (hu1 : u ≤ 1) :
    (upperRamificationGroup (R := O(n)) G(n) u).index = p - 1 := by
  have hδ := viviani_fraction_pos_lt_one p
  rw [upperRamificationGroup_falseTate_index π n 0 (Nat.zero_le n)
    (by simpa using hu) (by simpa using hu1),
    radicalTranslationDepth_initial p (n + 1) (by linarith), pow_zero, mul_one,
    Nat.zero_add, pow_one, Nat.totient_prime (Fact.out : p.Prime)]

include hp₂ hπ in
/-- Constant upper index from a fractional break to the following integer. -/
theorem upperRamificationGroup_falseTate_index_fractional_integer
    (n i : ℕ) (hi : i ≤ n) {u : ℝ} (hu0 : (i : ℝ) + δ < u) (hu1 : u ≤ (i : ℝ) + 1) :
    (upperRamificationGroup (R := O(n)) G(n) u).index = (p - 1) * p ^ (2 * i) := by
  have hδ := viviani_fraction_pos_lt_one p
  rw [upperRamificationGroup_falseTate_index π n i hi (by linarith) hu1,
    radicalTranslationDepth_interval p (n + 1) i hu0 (by linarith),
    Nat.min_eq_right (by omega : i ≤ n + 1),
    Nat.totient_prime_pow_succ (Fact.out : p.Prime),
    show 2 * i = i + i by omega, pow_add]
  ring

include hp₂ hπ in
/-- Constant upper index from an integer to the next fractional break. -/
theorem upperRamificationGroup_falseTate_index_integer_fractional
    (n i : ℕ) (hi : i + 1 ≤ n) {u : ℝ} (hu0 : (i : ℝ) + 1 < u)
    (hu1 : u ≤ (i : ℝ) + 1 + δ) :
    (upperRamificationGroup (R := O(n)) G(n) u).index = (p - 1) * p ^ (2 * i + 1) := by
  have hδ := viviani_fraction_pos_lt_one p
  rw [upperRamificationGroup_falseTate_index π n (i + 1) hi
    (by exact_mod_cast hu0) (by push_cast; linarith),
    radicalTranslationDepth_interval p (n + 1) i (by linarith) hu1,
    Nat.min_eq_right (by omega : i ≤ n + 1),
    Nat.totient_prime_pow_succ (Fact.out : p.Prime),
    show 2 * i + 1 = (i + 1) + i by omega, pow_add]
  ring

include hp₂ hπ in
/-- On the final fractional interval both cyclotomic and radical truncation
are retained; this also includes n=0, the first layer. -/
theorem upperRamificationGroup_falseTate_index_final (n : ℕ) {u : ℝ}
    (hu0 : (n : ℝ) + δ < u) (hu1 : u ≤ (n : ℝ) + 1 + δ) :
    (upperRamificationGroup (R := O(n)) G(n) u).index = (p - 1) * p ^ (2 * n) := by
  have hδ := viviani_fraction_pos_lt_one p
  rw [upperRamificationGroup_falseTate_index_tail π n (by linarith),
    radicalTranslationDepth_interval p (n + 1) n hu0 hu1,
    Nat.min_eq_right (Nat.le_succ n), Nat.totient_prime_pow_succ (Fact.out : p.Prime),
    show 2 * n = n + n by omega, pow_add]
  ring

include hp₂ hπ in
/-- The first integer upper parameter has lower parameter p-1. -/
theorem inverseHerbrandFunction_falseTate_one (n : ℕ) : Ψ(n) 1 = (p : ℝ) - 1 := by
  have h := viviani_inverse_affine π n (a := 0) (b := 1) le_rfl zero_le_one
    (p - 1) (fun u hu => upperRamificationGroup_falseTate_index_initial π n hu.1 hu.2)
  rw [inverseHerbrandFunction_of_nonpos G(n) (by norm_num) le_rfl,
    sub_zero, sub_zero, one_mul] at h
  simpa only [Nat.cast_sub (Fact.out : p.Prime).one_le, Nat.cast_one] using h

include hp₂ hπ in
/-- Every fractional lower break before the last one. The auxiliary i=0
value is included to make the uniform recurrence start without an empty-row case. -/
theorem inverseHerbrandFunction_falseTate_fractional (n i : ℕ) (hi : i ≤ n) :
    Ψ(n) ((i : ℝ) + δ) =
      (2 * (p : ℝ) ^ (2 * i) + (p : ℝ) - 1) / ((p : ℝ) + 1) := by
  have hδ := viviani_fraction_pos_lt_one p
  have hp : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hpm : (p : ℝ) - 1 ≠ 0 := by linarith
  have hpp : (p : ℝ) + 1 ≠ 0 := by positivity
  induction i with
  | zero =>
    have h := viviani_inverse_affine π n (a := 0) (b := δ) le_rfl hδ.1.le
      (p - 1) (fun u hu => upperRamificationGroup_falseTate_index_initial π n
        hu.1 (hu.2.trans hδ.2.le))
    rw [inverseHerbrandFunction_of_nonpos G(n) (by norm_num) le_rfl, sub_zero,
      sub_zero, Nat.cast_sub (Fact.out : p.Prime).one_le, Nat.cast_one] at h
    simpa only [Nat.cast_zero, zero_add, Nat.mul_zero, pow_zero] using
      (show Ψ(n) δ = (2 * (p : ℝ) ^ (2 * 0) + (p : ℝ) - 1) / ((p : ℝ) + 1) from by
        rw [h]
        field_simp
        ring)
  | succ i ih =>
    have hi' : i ≤ n := by omega
    have h₁ := viviani_inverse_affine π n
      (a := (i : ℝ) + δ) (b := (i : ℝ) + 1)
      (add_nonneg (Nat.cast_nonneg i) hδ.1.le) (by linarith) ((p - 1) * p ^ (2 * i))
      (fun u hu => upperRamificationGroup_falseTate_index_fractional_integer π n i hi' hu.1 hu.2)
    have h₂ := viviani_inverse_affine π n
      (a := (i : ℝ) + 1) (b := (i : ℝ) + 1 + δ)
      (by positivity) (by linarith) ((p - 1) * p ^ (2 * i + 1))
      (fun u hu => upperRamificationGroup_falseTate_index_integer_fractional π n i hi hu.1 hu.2)
    simp only [Nat.cast_mul, Nat.cast_pow,
      Nat.cast_sub (Fact.out : p.Prime).one_le, Nat.cast_one] at h₁ h₂
    calc
      _ = Ψ(n) ((i : ℝ) + δ) +
          (1 - δ) * (((p : ℝ) - 1) * (p : ℝ) ^ (2 * i)) +
          δ * (((p : ℝ) - 1) * (p : ℝ) ^ (2 * i + 1)) := by
        push_cast
        linarith
      _ = _ := by
        rw [ih hi', show 2 * (i + 1) = 2 * i + 2 by omega]
        simp only [pow_add, pow_two, pow_one]
        field_simp [hpm, hpp]
        ring

include hp₂ hπ in
/-- The integer-break formula has exponent 2i+1. -/
theorem inverseHerbrandFunction_falseTate_integer (n i : ℕ) (hi : i ≤ n) :
    Ψ(n) ((i : ℝ) + 1) =
      ((p : ℝ) - 1) * ((p : ℝ) ^ (2 * i + 1) + 1) / ((p : ℝ) + 1) := by
  have hδ := viviani_fraction_pos_lt_one p
  have hp : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hpm : (p : ℝ) - 1 ≠ 0 := by linarith
  have hpp : (p : ℝ) + 1 ≠ 0 := by positivity
  have h := viviani_inverse_affine π n
    (a := (i : ℝ) + δ) (b := (i : ℝ) + 1)
    (add_nonneg (Nat.cast_nonneg i) hδ.1.le) (by linarith)
    ((p - 1) * p ^ (2 * i))
    (fun u hu => upperRamificationGroup_falseTate_index_fractional_integer π n i hi hu.1 hu.2)
  simp only [Nat.cast_mul, Nat.cast_pow,
    Nat.cast_sub (Fact.out : p.Prime).one_le, Nat.cast_one] at h
  calc
    _ = Ψ(n) ((i : ℝ) + δ) +
        (1 - δ) * (((p : ℝ) - 1) * (p : ℝ) ^ (2 * i)) := by linarith
    _ = _ := by
      rw [inverseHerbrandFunction_falseTate_fractional π n i hi, pow_succ]
      field_simp [hpm, hpp]
      ring

include hp₂ hπ in
/-- The final lower break, valid also in the first layer n=0. -/
theorem inverseHerbrandFunction_falseTate_final (n : ℕ) :
    Ψ(n) ((n : ℝ) + 1 + δ) =
      ((p : ℝ) ^ (2 * (n + 1)) + (p : ℝ) ^ (2 * n) + (p : ℝ) - 1) / ((p : ℝ) + 1) := by
  have hδ := viviani_fraction_pos_lt_one p
  have h := viviani_inverse_affine π n
    (a := (n : ℝ) + δ) (b := (n : ℝ) + 1 + δ)
    (add_nonneg (Nat.cast_nonneg n) hδ.1.le) (by linarith)
    ((p - 1) * p ^ (2 * n))
    (fun u hu => upperRamificationGroup_falseTate_index_final π n hu.1 hu.2)
  simp only [Nat.cast_mul, Nat.cast_pow,
    Nat.cast_sub (Fact.out : p.Prime).one_le, Nat.cast_one] at h
  calc
    _ = Ψ(n) ((n : ℝ) + δ) + ((p : ℝ) - 1) * (p : ℝ) ^ (2 * n) := by linarith
    _ = _ := by
      rw [inverseHerbrandFunction_falseTate_fractional π n n le_rfl,
        show 2 * (n + 1) = 2 * n + 2 by omega]
      simp only [pow_add, pow_two]
      field_simp
      ring

include hp₂ hπ in
/-- The real lower groups at the fractional table entries. -/
theorem lowerRamificationGroupReal_falseTate_fractional (n i : ℕ)
    (hi : 1 ≤ i) (hin : i ≤ n) :
    (lowerRamificationGroupReal G(n) (IsLocalRing.maximalIdeal O(n))
      ((2 * (p : ℝ) ^ (2 * i) + (p : ℝ) - 1) / ((p : ℝ) + 1))).map
        (finiteDiagonalGaloisEquiv_padic p π (n + 1)).toMonoidHom =
      finiteAffineSubgroup p (n + 1) (i - 1) (finiteUnitSubgroup p (n + 1) (i + 1)) := by
  rw [← inverseHerbrandFunction_falseTate_fractional π n i hin]
  exact finiteUpperAffine_fractional π n i hi (by omega)

include hp₂ hπ in
/-- The real lower groups at the integer table entries. -/
theorem lowerRamificationGroupReal_falseTate_integer (n i : ℕ) (hi : i ≤ n) :
    (lowerRamificationGroupReal G(n) (IsLocalRing.maximalIdeal O(n))
      (((p : ℝ) - 1) * ((p : ℝ) ^ (2 * i + 1) + 1) / ((p : ℝ) + 1))).map
        (finiteDiagonalGaloisEquiv_padic p π (n + 1)).toMonoidHom =
      finiteAffineSubgroup p (n + 1) i (finiteUnitSubgroup p (n + 1) (i + 1)) := by
  rw [← inverseHerbrandFunction_falseTate_integer π n i hi]
  exact finiteUpperAffine_integer π n i hi

include hp₂ hπ in
/-- The final lower group is the order-p translation subgroup. -/
theorem lowerRamificationGroupReal_falseTate_final (n : ℕ) :
    (lowerRamificationGroupReal G(n) (IsLocalRing.maximalIdeal O(n))
      (((p : ℝ) ^ (2 * (n + 1)) + (p : ℝ) ^ (2 * n) + (p : ℝ) - 1) /
        ((p : ℝ) + 1))).map
        (finiteDiagonalGaloisEquiv_padic p π (n + 1)).toMonoidHom =
      finiteAffineSubgroup p (n + 1) n ⊥ := by
  rw [← inverseHerbrandFunction_falseTate_final π n]
  have h := finiteUpperAffine_fractional π n (n + 1) (by omega) le_rfl
  simp only [Nat.cast_add, Nat.cast_one, Nat.add_sub_cancel,
    finiteUnitSubgroup_eq_bot p (n + 1) (n + 1 + 1) (by omega)] at h
  exact h

include hp₂ hπ in
theorem herbrandFunction_falseTate_fractional (n i : ℕ) (hi : i ≤ n) :
    herbrandFunction (R := O(n)) G(n)
      ((2 * (p : ℝ) ^ (2 * i) + (p : ℝ) - 1) / ((p : ℝ) + 1)) = (i : ℝ) + δ := by
  have hδ := viviani_fraction_pos_lt_one p
  rw [← inverseHerbrandFunction_falseTate_fractional π n i hi,
    herbrandFunction_inverseHerbrandFunction G(n) (by linarith [Nat.cast_nonneg (α := ℝ) i])]

include hp₂ hπ in
theorem herbrandFunction_falseTate_integer (n i : ℕ) (hi : i ≤ n) :
    herbrandFunction (R := O(n)) G(n)
      (((p : ℝ) - 1) * ((p : ℝ) ^ (2 * i + 1) + 1) / ((p : ℝ) + 1)) = (i : ℝ) + 1 := by
  rw [← inverseHerbrandFunction_falseTate_integer π n i hi,
    herbrandFunction_inverseHerbrandFunction G(n) (by linarith [Nat.cast_nonneg (α := ℝ) i])]

include hp₂ hπ in
theorem herbrandFunction_falseTate_final (n : ℕ) :
    herbrandFunction (R := O(n)) G(n)
      (((p : ℝ) ^ (2 * (n + 1)) + (p : ℝ) ^ (2 * n) + (p : ℝ) - 1) /
        ((p : ℝ) + 1)) = (n : ℝ) + 1 + δ := by
  have hδ := viviani_fraction_pos_lt_one p
  rw [← inverseHerbrandFunction_falseTate_final π n,
    herbrandFunction_inverseHerbrandFunction G(n) (by linarith [Nat.cast_nonneg (α := ℝ) n])]

/-- The complete initial positive upper interval, retaining its right endpoint. -/
theorem finiteUpperAffine_initial (n : ℕ) {u : ℝ} (hu : 0 < u) (hu1 : u ≤ 1) :
    finiteUpperAffineGroup π n u =
      finiteAffineSubgroup p (n + 1) 0 (finiteUnitSubgroup p (n + 1) 1) := by
  have hδ := viviani_fraction_pos_lt_one p
  rw [finiteUpperAffine_eq_interval π n 0 (Nat.zero_le n)
    (by simpa using hu) (by simpa using hu1),
    radicalTranslationDepth_initial p (n + 1) (by linarith), Nat.zero_add]

/-- Every open-left, closed-right upper interval after a fractional break. -/
theorem finiteUpperAffine_fractional_integer (n i : ℕ) (hi : i ≤ n)
    {u : ℝ} (hu0 : (i : ℝ) + δ < u) (hu1 : u ≤ (i : ℝ) + 1) :
    finiteUpperAffineGroup π n u =
      finiteAffineSubgroup p (n + 1) i (finiteUnitSubgroup p (n + 1) (i + 1)) := by
  have hδ := viviani_fraction_pos_lt_one p
  rw [finiteUpperAffine_eq_interval π n i hi (by linarith) hu1,
    radicalTranslationDepth_interval p (n + 1) i hu0 (by linarith),
    Nat.min_eq_right (by omega : i ≤ n + 1)]

/-- Every open-left, closed-right upper interval after an integer break. -/
theorem finiteUpperAffine_integer_fractional (n i : ℕ) (hi : i + 1 ≤ n)
    {u : ℝ} (hu0 : (i : ℝ) + 1 < u) (hu1 : u ≤ (i : ℝ) + 1 + δ) :
    finiteUpperAffineGroup π n u =
      finiteAffineSubgroup p (n + 1) i (finiteUnitSubgroup p (n + 1) (i + 2)) := by
  have hδ := viviani_fraction_pos_lt_one p
  rw [finiteUpperAffine_eq_interval π n (i + 1) hi
    (by exact_mod_cast hu0) (by push_cast; linarith),
    radicalTranslationDepth_interval p (n + 1) i (by linarith) hu1,
    Nat.min_eq_right (by omega : i ≤ n + 1)]

/-- The final entire fractional upper interval, including the first layer. -/
theorem finiteUpperAffine_final_interval (n : ℕ) {u : ℝ}
    (hu0 : (n : ℝ) + δ < u) (hu1 : u ≤ (n : ℝ) + 1 + δ) :
    finiteUpperAffineGroup π n u = finiteAffineSubgroup p (n + 1) n ⊥ := by
  have hδ := viviani_fraction_pos_lt_one p
  rw [finiteUpperAffine_eq_tail π n (by linarith),
    radicalTranslationDepth_interval p (n + 1) n hu0 hu1, Nat.min_eq_right (Nat.le_succ n)]

/-- The finite upper groups vanish strictly after the final break. -/
theorem finiteUpperAffine_eq_bot (n : ℕ) {u : ℝ} (hu : (n : ℝ) + 1 + δ < u) :
    finiteUpperAffineGroup π n u = ⊥ := by
  have hδ := viviani_fraction_pos_lt_one p
  rw [finiteUpperAffine_eq_tail π n (by linarith),
    radicalTranslationDepth_tail p (n + 1) (by push_cast; exact hu),
    finiteAffineSubgroup_self_bot]

include hp₂ hπ in
theorem lowerRamificationGroupReal_falseTate_nonpos (n : ℕ) {t : ℝ} (ht : t ≤ 0) :
    lowerRamificationGroupReal G(n) (IsLocalRing.maximalIdeal O(n)) t = ⊤ := by
  have hz : lowerRamificationGroupReal G(n) (IsLocalRing.maximalIdeal O(n)) 0 = ⊤ := by
    simpa only [lowerRamificationGroupReal_zero, lowerRamificationGroup_zero] using
      lowerRamificationGroup_falseTateLayer_zero p π n
  apply top_le_iff.mp
  rw [← hz]
  exact lowerRamificationGroupReal_antitone G(n) _ ht

include hp₂ hπ in
theorem upperRamificationGroup_falseTate_nonpos (n : ℕ) {u : ℝ}
    (hu : -1 ≤ u) (hu0 : u ≤ 0) : upperRamificationGroup (R := O(n)) G(n) u = ⊤ := by
  rw [upperRamificationGroup, inverseHerbrandFunction_of_nonpos G(n) hu hu0]
  exact lowerRamificationGroupReal_falseTate_nonpos π n hu0

omit hp₂ hπ in
theorem viviani_lower_parameter (n : ℕ) {a b t : ℝ}
    (ha : -1 ≤ a) (hb : -1 ≤ b) (ht0 : Ψ(n) a < t) (ht1 : t ≤ Ψ(n) b) :
    a < herbrandFunction (R := O(n)) G(n) t ∧
      herbrandFunction (R := O(n)) G(n) t ≤ b :=
  herbrandFunction_mem_Ioc_of_inverseHerbrandFunction G(n) ha hb ht0 ht1

theorem viviani_lower_map (n : ℕ) {t : ℝ} (ht : -1 ≤ t) :
    (lowerRamificationGroupReal G(n) (IsLocalRing.maximalIdeal O(n)) t).map
      (finiteDiagonalGaloisEquiv_padic p π (n + 1)).toMonoidHom =
      finiteUpperAffineGroup π n (herbrandFunction (R := O(n)) G(n) t) := by
  rw [finiteUpperAffineGroup, upperRamificationGroup_herbrandFunction G(n) ht]

/-- The initial lower interval is exactly 0<t≤p-1. -/
theorem lowerRamificationGroupReal_falseTate_initial (n : ℕ) {t : ℝ}
    (ht0 : 0 < t) (ht1 : t ≤ (p : ℝ) - 1) :
    (lowerRamificationGroupReal G(n) (IsLocalRing.maximalIdeal O(n)) t).map
      (finiteDiagonalGaloisEquiv_padic p π (n + 1)).toMonoidHom =
      finiteAffineSubgroup p (n + 1) 0 (finiteUnitSubgroup p (n + 1) 1) := by
  have h := viviani_lower_parameter π n (a := 0) (b := 1)
    (by norm_num) (by norm_num)
    (by simpa only [inverseHerbrandFunction_of_nonpos G(n) (by norm_num) le_rfl] using ht0)
    (by simpa only [inverseHerbrandFunction_falseTate_one π n] using ht1)
  rw [viviani_lower_map π n (by linarith)]
  exact finiteUpperAffine_initial π n h.1 h.2

/-- The lower intervals corresponding to the fractional-to-integer rows. -/
theorem lowerRamificationGroupReal_falseTate_fractional_integer (n i : ℕ) (hi : i ≤ n)
    {t : ℝ}
    (ht0 : (2 * (p : ℝ) ^ (2 * i) + (p : ℝ) - 1) / ((p : ℝ) + 1) < t)
    (ht1 : t ≤ ((p : ℝ) - 1) * ((p : ℝ) ^ (2 * i + 1) + 1) / ((p : ℝ) + 1)) :
    (lowerRamificationGroupReal G(n) (IsLocalRing.maximalIdeal O(n)) t).map
      (finiteDiagonalGaloisEquiv_padic p π (n + 1)).toMonoidHom =
      finiteAffineSubgroup p (n + 1) i (finiteUnitSubgroup p (n + 1) (i + 1)) := by
  have hδ := viviani_fraction_pos_lt_one p
  have h0 : Ψ(n) ((i : ℝ) + δ) < t := by
    simpa only [inverseHerbrandFunction_falseTate_fractional π n i hi] using ht0
  have h1 : t ≤ Ψ(n) ((i : ℝ) + 1) := by
    simpa only [inverseHerbrandFunction_falseTate_integer π n i hi] using ht1
  have h := viviani_lower_parameter π n
    (by linarith [Nat.cast_nonneg (α := ℝ) i])
    (by linarith [Nat.cast_nonneg (α := ℝ) i]) h0 h1
  rw [viviani_lower_map π n
    ((inverseHerbrandFunction_mem_Ici (R := O(n)) G(n) _).trans h0.le)]
  exact finiteUpperAffine_fractional_integer π n i hi h.1 h.2

/-- The lower intervals corresponding to the integer-to-fractional rows. -/
theorem lowerRamificationGroupReal_falseTate_integer_fractional (n i : ℕ) (hi : i + 1 ≤ n)
    {t : ℝ}
    (ht0 : ((p : ℝ) - 1) * ((p : ℝ) ^ (2 * i + 1) + 1) / ((p : ℝ) + 1) < t)
    (ht1 : t ≤ (2 * (p : ℝ) ^ (2 * (i + 1)) + (p : ℝ) - 1) / ((p : ℝ) + 1)) :
    (lowerRamificationGroupReal G(n) (IsLocalRing.maximalIdeal O(n)) t).map
      (finiteDiagonalGaloisEquiv_padic p π (n + 1)).toMonoidHom =
      finiteAffineSubgroup p (n + 1) i (finiteUnitSubgroup p (n + 1) (i + 2)) := by
  have hδ := viviani_fraction_pos_lt_one p
  have h0 : Ψ(n) ((i : ℝ) + 1) < t := by
    simpa only [inverseHerbrandFunction_falseTate_integer π n i (by omega)] using ht0
  have h1 : t ≤ Ψ(n) ((i : ℝ) + 1 + δ) := by
    have hψ := inverseHerbrandFunction_falseTate_fractional π n (i + 1) hi
    simp only [Nat.cast_add, Nat.cast_one] at hψ
    rw [hψ]
    exact ht1
  have h := viviani_lower_parameter π n
    (by linarith [Nat.cast_nonneg (α := ℝ) i])
    (by linarith [Nat.cast_nonneg (α := ℝ) i]) h0 h1
  rw [viviani_lower_map π n
    ((inverseHerbrandFunction_mem_Ici (R := O(n)) G(n) _).trans h0.le)]
  exact finiteUpperAffine_integer_fractional π n i hi h.1 h.2

/-- The final lower interval, before the last group vanishes. -/
theorem lowerRamificationGroupReal_falseTate_final_interval (n : ℕ) {t : ℝ}
    (ht0 : (2 * (p : ℝ) ^ (2 * n) + (p : ℝ) - 1) / ((p : ℝ) + 1) < t)
    (ht1 : t ≤ ((p : ℝ) ^ (2 * (n + 1)) + (p : ℝ) ^ (2 * n) + (p : ℝ) - 1) /
      ((p : ℝ) + 1)) :
    (lowerRamificationGroupReal G(n) (IsLocalRing.maximalIdeal O(n)) t).map
      (finiteDiagonalGaloisEquiv_padic p π (n + 1)).toMonoidHom =
      finiteAffineSubgroup p (n + 1) n ⊥ := by
  have hδ := viviani_fraction_pos_lt_one p
  have h0 : Ψ(n) ((n : ℝ) + δ) < t := by
    simpa only [inverseHerbrandFunction_falseTate_fractional π n n le_rfl] using ht0
  have h1 : t ≤ Ψ(n) ((n : ℝ) + 1 + δ) := by
    simpa only [inverseHerbrandFunction_falseTate_final π n] using ht1
  have h := viviani_lower_parameter π n
    (by linarith [Nat.cast_nonneg (α := ℝ) n])
    (by linarith [Nat.cast_nonneg (α := ℝ) n]) h0 h1
  rw [viviani_lower_map π n
    ((inverseHerbrandFunction_mem_Ici (R := O(n)) G(n) _).trans h0.le)]
  exact finiteUpperAffine_final_interval π n h.1 h.2

include hp₂ hπ in
/-- The upper group is trivial strictly after the final upper break. -/
theorem upperRamificationGroup_falseTate_eq_bot (n : ℕ) {u : ℝ}
    (hu : (n : ℝ) + 1 + δ < u) : upperRamificationGroup (R := O(n)) G(n) u = ⊥ := by
  apply Subgroup.map_injective
    (f := (finiteDiagonalGaloisEquiv_padic p π (n + 1)).toMonoidHom)
    (finiteDiagonalGaloisEquiv_padic p π (n + 1)).injective
  rw [Subgroup.map_bot]
  exact finiteUpperAffine_eq_bot π n hu

include hp₂ hπ in
/-- The lower group is trivial strictly after the final lower break. -/
theorem lowerRamificationGroupReal_falseTate_eq_bot (n : ℕ) {t : ℝ}
    (ht : ((p : ℝ) ^ (2 * (n + 1)) + (p : ℝ) ^ (2 * n) + (p : ℝ) - 1) /
      ((p : ℝ) + 1) < t) :
    lowerRamificationGroupReal G(n) (IsLocalRing.maximalIdeal O(n)) t = ⊥ := by
  have hδ := viviani_fraction_pos_lt_one p
  have h0 : Ψ(n) ((n : ℝ) + 1 + δ) < t := by
    simpa only [inverseHerbrandFunction_falseTate_final π n] using ht
  have htm : -1 ≤ t := (inverseHerbrandFunction_mem_Ici (R := O(n)) G(n) _).trans h0.le
  have hu : (n : ℝ) + 1 + δ < herbrandFunction (R := O(n)) G(n) t := by
    have ha : -1 ≤ (n : ℝ) + 1 + δ := by linarith [Nat.cast_nonneg (α := ℝ) n]
    apply ((strictMonoOn_inverseHerbrandFunction (R := O(n)) G(n)).lt_iff_lt
      ha (herbrandFunction_mem_Ici G(n) htm)).mp
    simpa only [inverseHerbrandFunction_herbrandFunction G(n) htm] using h0
  rw [← upperRamificationGroup_herbrandFunction G(n) htm]
  exact upperRamificationGroup_falseTate_eq_bot π n hu

/-- Negative upper parameters through zero give the full affine group. -/
theorem finiteUpperAffine_nonpos (n : ℕ) {u : ℝ} (hu : -1 ≤ u) (hu0 : u ≤ 0) :
    finiteUpperAffineGroup π n u = ⊤ := by
  rw [finiteUpperAffineGroup, upperRamificationGroup_falseTate_nonpos π n hu hu0,
    Subgroup.map_top, MonoidHom.range_eq_top.mpr
      (finiteDiagonalGaloisEquiv_padic p π (n + 1)).surjective]

omit hp₂ in
/-- The first-layer upper break equals the first strict radical threshold. -/
theorem viviani_first_break : 1 + δ = (p : ℝ) / ((p : ℝ) - 1) := by
  have hp : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  field_simp
  ring

/-- The positive first-layer upper group is precisely the translation
factor, through and including p/(p-1). -/
theorem finiteUpperAffine_first_layer {u : ℝ}
    (hu : 0 < u) (hu1 : u ≤ (p : ℝ) / ((p : ℝ) - 1)) :
    finiteUpperAffineGroup π 0 u =
      (SemidirectProduct.inl :
        Multiplicative (ZMod (p ^ 1)) →* FullFiniteAffineGroup p 1).range := by
  have hb : u ≤ 1 + δ := by rw [viviani_first_break]; exact hu1
  rw [finiteUpperAffine_eq_tail π 0 (by simpa using hu),
    radicalTranslationDepth_initial p 1 hb, finiteAffineSubgroup_zero_bot]

/-- The full first-layer upper filtration, with the right endpoint. -/
theorem finiteUpperAffine_first_layer_filtration {u : ℝ} (hu : -1 ≤ u) :
    finiteUpperAffineGroup π 0 u =
      if u ≤ 0 then ⊤ else if u ≤ (p : ℝ) / ((p : ℝ) - 1) then
        (SemidirectProduct.inl : Multiplicative (ZMod (p ^ 1)) →* FullFiniteAffineGroup p 1).range
        else ⊥ := by
  by_cases hu0 : u ≤ 0
  · rw [ite_eq_left hu0]
    exact finiteUpperAffine_nonpos π 0 hu hu0
  · rw [ite_eq_right hu0]
    by_cases hb : u ≤ (p : ℝ) / ((p : ℝ) - 1)
    · rw [ite_eq_left hb]
      exact finiteUpperAffine_first_layer π (lt_of_not_ge hu0) hb
    · rw [ite_eq_right hb]
      apply finiteUpperAffine_eq_bot π 0
      simpa only [Nat.cast_zero, zero_add, viviani_first_break] using lt_of_not_ge hb

include hp₂ hπ in
/-- The first-layer inverse Herbrand function on its whole nontrivial interval. -/
theorem inverseHerbrandFunction_falseTate_first_layer {u : ℝ}
    (hu : 0 ≤ u) (hu1 : u ≤ (p : ℝ) / ((p : ℝ) - 1)) :
    Ψ(0) u = ((p : ℝ) - 1) * u := by
  have hb : u ≤ 1 + δ := by rw [viviani_first_break]; exact hu1
  have h := viviani_inverse_affine π 0 (a := 0) (b := u) le_rfl hu (p - 1) (by
    intro v hv
    rw [upperRamificationGroup_falseTate_index_tail π 0 (by simpa using hv.1),
      radicalTranslationDepth_initial p 1 (hv.2.trans hb)]
    simp [Nat.totient_prime (Fact.out : p.Prime)])
  rw [inverseHerbrandFunction_of_nonpos G(0) (by norm_num) le_rfl, sub_zero, sub_zero] at h
  simpa only [Nat.cast_sub (Fact.out : p.Prime).one_le, Nat.cast_one, mul_comm] using h

include hp₂ hπ in
/-- The positive first-layer lower break is p. -/
theorem inverseHerbrandFunction_falseTate_first_break :
    Ψ(0) ((p : ℝ) / ((p : ℝ) - 1)) = p := by
  have hp : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  rw [inverseHerbrandFunction_falseTate_first_layer π (by positivity) le_rfl]
  field_simp

/-- The positive first-layer lower group, including its final endpoint. -/
theorem lowerRamificationGroupReal_falseTate_first_layer {t : ℝ}
    (ht : 0 < t) (ht1 : t ≤ p) :
    (lowerRamificationGroupReal G(0) (IsLocalRing.maximalIdeal O(0)) t).map
      (finiteDiagonalGaloisEquiv_padic p π 1).toMonoidHom =
      (SemidirectProduct.inl :
        Multiplicative (ZMod (p ^ 1)) →* FullFiniteAffineGroup p 1).range := by
  have hp : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have h := viviani_lower_parameter π 0 (a := 0)
    (b := (p : ℝ) / ((p : ℝ) - 1)) (by norm_num)
    (by
      have hnonneg : (0 : ℝ) ≤ (p : ℝ) / ((p : ℝ) - 1) := by positivity
      linarith)
    (by simpa only [inverseHerbrandFunction_of_nonpos G(0) (by norm_num) le_rfl] using ht)
    (by simpa only [inverseHerbrandFunction_falseTate_first_break π] using ht1)
  rw [viviani_lower_map π 0 (by linarith)]
  exact finiteUpperAffine_first_layer π h.1 h.2

/-- The full first-layer lower filtration. -/
theorem lowerRamificationGroupReal_falseTate_first_layer_filtration (t : ℝ) :
    (lowerRamificationGroupReal G(0) (IsLocalRing.maximalIdeal O(0)) t).map
      (finiteDiagonalGaloisEquiv_padic p π 1).toMonoidHom =
      if t ≤ 0 then ⊤ else if t ≤ (p : ℝ) then
        (SemidirectProduct.inl : Multiplicative (ZMod (p ^ 1)) →* FullFiniteAffineGroup p 1).range
        else ⊥ := by
  by_cases ht0 : t ≤ 0
  · rw [ite_eq_left ht0, lowerRamificationGroupReal_falseTate_nonpos π 0 ht0,
      Subgroup.map_top, MonoidHom.range_eq_top.mpr
        (finiteDiagonalGaloisEquiv_padic p π 1).surjective]
  · rw [ite_eq_right ht0]
    by_cases ht1 : t ≤ (p : ℝ)
    · rw [ite_eq_left ht1]
      exact lowerRamificationGroupReal_falseTate_first_layer π (lt_of_not_ge ht0) ht1
    · rw [ite_eq_right ht1]
      have hfinal : ((p : ℝ) ^ (2 * (0 + 1)) + (p : ℝ) ^ (2 * 0) + (p : ℝ) - 1) /
          ((p : ℝ) + 1) = p := by field_simp; ring
      rw [lowerRamificationGroupReal_falseTate_eq_bot π 0 (by
        rw [hfinal]; exact lt_of_not_ge ht1), Subgroup.map_bot]

end Upper

end FalseTateExtension
end
