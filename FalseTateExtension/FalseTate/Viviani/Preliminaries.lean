/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FalseTateExtension.Kummer.APF
public import FalseTateExtension.FalseTate.TotalRamification
public import FontaineWintenberger.APF.Finite.ConstantIndex
public import FontaineWintenberger.Ramification.Herbrand.Interval
public import FontaineWintenberger.Ramification.Upper.Transport
public import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# Preliminaries for Viviani's filtration

The radical thresholds `r + 1 + 1/(p-1)` over `ℚ_p`, the number of thresholds below a real
parameter, the normal subgroups of the finite affine group `ℤ/p^n ⋊ (ℤ/p^n)ˣ` for `p ≠ 2`, and the
translation and principal-unit subgroups that appear in the ramification filtration.
-/

@[expose] public section

noncomputable section

namespace FalseTateExtension

open IsDiscreteValuationRing FontaineWintenberger

variable (p : ℕ) [Fact p.Prime]

/-- The normalized additive valuation of the rational base prime is one. -/
theorem addVal_padicUnitBall_p : addVal 𝒪[ℚ_[p]] (p : 𝒪[ℚ_[p]]) = 1 := by
  apply addVal_uniformizer
  have h := (MulEquiv.irreducible_iff (f := (padicValuationSubringEquiv p).symm)).mpr
    PadicInt.irreducible_p
  simpa only [map_natCast] using h

/-- The radical thresholds over the rational base have absolute scale one. -/
theorem radicalUpperBreak_padic (r : ℕ) :
    radicalUpperBreak (K := ℚ_[p]) p r = (r : ℝ) + 1 / ((p : ℝ) - 1) := by
  simp [radicalUpperBreak, absoluteRamificationIdx, addVal_padicUnitBall_p]

/-- The number of radical thresholds strictly below the upper parameter.
The strict inequality retains each right endpoint in the preceding group. -/
def radicalTranslationDepth (n : ℕ) (u : ℝ) : ℕ :=
  ((Finset.range n).filter (fun r : ℕ => (r : ℝ) + 1 + 1 / ((p : ℝ) - 1) < u)).card

omit [Fact p.Prime] in
theorem radicalTranslationDepth_zero (u : ℝ) : radicalTranslationDepth p 0 u = 0 := by
  simp [radicalTranslationDepth]

omit [Fact p.Prime] in
theorem radicalTranslationDepth_le (n : ℕ) (u : ℝ) :
    radicalTranslationDepth p n u ≤ n := by
  exact (Finset.card_filter_le ..).trans_eq (Finset.card_range n)

omit [Fact p.Prime] in
theorem radicalTranslationDepth_succ (n : ℕ) (u : ℝ) :
    radicalTranslationDepth p (n + 1) u = radicalTranslationDepth p n u +
      if u ≤ (n + 1 : ℝ) + 1 / ((p : ℝ) - 1) then 0 else 1 := by
  classical
  simp only [radicalTranslationDepth, Finset.range_add_one, Finset.filter_insert]
  by_cases h : u ≤ (n + 1 : ℝ) + 1 / ((p : ℝ) - 1)
  · rw [ite_eq_right (not_lt.mpr h), ite_eq_left h, Nat.add_zero]
  · rw [ite_eq_left (lt_of_not_ge h), ite_eq_right h, Finset.card_insert_of_notMem]
    exact fun hn => Nat.lt_irrefl n (Finset.mem_range.mp (Finset.mem_filter.mp hn).1)

/-- The complete index profile of the nonnormal radical fields,
including the zeroth layer, all finite truncations, and every right endpoint. -/
theorem radicalLayer_apfIndex_eq_pow_translationDepth
    (π : 𝒪[ℚ_[p]]) [hπ : Fact (Irreducible π)] (n : ℕ) {u : ℝ} (hu : 0 ≤ u) :
    apfIndex ℚ_[p] (radicalLayer p (π : ℚ_[p]) n) u = p ^ radicalTranslationDepth p n u := by
  induction n with
  | zero =>
    rw [radicalTranslationDepth_zero, pow_zero, radicalLayer_zero,
      apfIndex_algEquiv ℚ_[p] _ (IntermediateField.botEquiv ℚ_[p] _),
      apfIndex_eq_one_of_bound_eq_top ℚ_[p] ℚ_[p] (apfRamificationBound_self ℚ_[p]) hu]
  | succ n ih =>
    rw [radicalLayer_apfIndex_succ_threshold p π n hu, ih,
      radicalUpperBreak_padic, radicalTranslationDepth_succ]
    push_cast
    by_cases h : u ≤ (n + 1 : ℝ) + 1 / ((p : ℝ) - 1)
    · rw [ite_eq_left h, ite_eq_left h, mul_one, Nat.add_zero]
    · rw [ite_eq_right h, ite_eq_right h, pow_succ]

omit [Fact p.Prime] in
/-- The strict-threshold count on every interval, with finite truncation. -/
theorem radicalTranslationDepth_interval (n j : ℕ) {u : ℝ}
    (hlo : (j : ℝ) + 1 / ((p : ℝ) - 1) < u)
    (hhi : u ≤ (j : ℝ) + 1 + 1 / ((p : ℝ) - 1)) :
    radicalTranslationDepth p n u = min n j := by
  classical
  have hs : (Finset.range n).filter
      (fun r : ℕ => (r : ℝ) + 1 + 1 / ((p : ℝ) - 1) < u) = Finset.range (min n j) := by
    ext r
    simp only [Finset.mem_filter, Finset.mem_range, Nat.lt_min]
    constructor
    · rintro ⟨hrn, hru⟩
      exact ⟨hrn, by exact_mod_cast (show (r : ℝ) < j by linarith)⟩
    · rintro ⟨hrn, hrj⟩
      have hr : (r : ℝ) + 1 ≤ j := by exact_mod_cast (Nat.succ_le_of_lt hrj)
      exact ⟨hrn, by linarith⟩
  rw [radicalTranslationDepth, hs, Finset.card_range]

omit [Fact p.Prime] in
theorem radicalTranslationDepth_initial (n : ℕ) {u : ℝ}
    (hu : u ≤ 1 + 1 / ((p : ℝ) - 1)) : radicalTranslationDepth p n u = 0 := by
  classical
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro r hr
  have h := (Finset.mem_filter.mp hr).2
  linarith [Nat.cast_nonneg (α := ℝ) r]

omit [Fact p.Prime] in
theorem radicalTranslationDepth_tail (n : ℕ) {u : ℝ}
    (hu : (n : ℝ) + 1 / ((p : ℝ) - 1) < u) :
    radicalTranslationDepth p n u = n := by
  classical
  rw [radicalTranslationDepth, Finset.filter_eq_self.mpr, Finset.card_range]
  intro r hr
  have hr' : (r : ℝ) + 1 ≤ n := by
    exact_mod_cast (Nat.succ_le_of_lt (Finset.mem_range.mp hr))
  linarith

/-- The odd-prime fractional offset is strictly between zero and one. -/
theorem viviani_fraction_pos_lt_one [hp₂ : Fact (p ≠ 2)] :
    0 < 1 / ((p : ℝ) - 1) ∧ 1 / ((p : ℝ) - 1) < 1 := by
  have hp : 2 < p := lt_of_le_of_ne (Fact.out : p.Prime).two_le (Ne.symm hp₂.out)
  have hp' : (2 : ℝ) < p := by exact_mod_cast hp
  constructor
  · exact div_pos zero_lt_one (by linarith)
  · exact (div_lt_one (by linarith)).mpr (by linarith)

omit [Fact p.Prime] in
theorem radicalTranslationDepth_fractional (n i : ℕ) (hi : 1 ≤ i) (hin : i ≤ n) :
    radicalTranslationDepth p n ((i : ℝ) + 1 / ((p : ℝ) - 1)) = i - 1 := by
  have hi' : (i - 1 : ℕ) + 1 = i := Nat.sub_add_cancel hi
  have hc : ((i - 1 : ℕ) : ℝ) + 1 = i := by exact_mod_cast hi'
  rw [radicalTranslationDepth_interval p n (i - 1) (by linarith) (by linarith),
    Nat.min_eq_right (by omega : i - 1 ≤ n)]

theorem radicalTranslationDepth_integer [hp₂ : Fact (p ≠ 2)] (n i : ℕ) (hin : i ≤ n) :
    radicalTranslationDepth p n ((i : ℝ) + 1) = i := by
  have hδ := viviani_fraction_pos_lt_one p
  rw [radicalTranslationDepth_interval p n i (by linarith) (by linarith), Nat.min_eq_right hin]

/-- The subgroup of translations divisible by p^k, represented as
the range of the power homomorphism on the multiplicative type tag. -/
def finiteTranslationSubgroup (n k : ℕ) : Subgroup (Multiplicative (ZMod (p ^ n))) :=
  (powMonoidHom (p ^ k) : Multiplicative (ZMod (p ^ n)) →* _).range

theorem finiteTranslationSubgroup_index (n k : ℕ) (hk : k ≤ n) :
    (finiteTranslationSubgroup p n k).index = p ^ k := by
  have : NeZero (p ^ n) := ⟨pow_ne_zero n (Fact.out : p.Prime).ne_zero⟩
  rw [finiteTranslationSubgroup, IsCyclic.index_powMonoidHom_range]
  simp only [Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card]
  exact Nat.gcd_eq_right (Nat.pow_dvd_pow p hk)

omit [Fact p.Prime] in
theorem finiteTranslationSubgroup_zero (n : ℕ) : finiteTranslationSubgroup p n 0 = ⊤ := by
  ext b
  simp only [Subgroup.mem_top, iff_true]
  exact ⟨b, by simp [powMonoidHom]⟩

omit [Fact p.Prime] in
theorem finiteTranslationSubgroup_self (n : ℕ) : finiteTranslationSubgroup p n n = ⊥ := by
  ext b
  constructor
  · rintro ⟨a, rfl⟩
    apply Multiplicative.toAdd.injective
    change (p ^ n) • a.toAdd = 0
    simp [nsmul_eq_mul]
  · intro hb
    have hb' : b = 1 := hb
    rw [hb']
    exact Subgroup.one_mem _

/-- The principal-unit subgroup, truncated at the finite level.
At depth zero it is the full unit group; at depth n it is trivial. -/
def finiteUnitSubgroup (n r : ℕ) : Subgroup (ZMod (p ^ n))ˣ :=
  (ZMod.unitsMap (pow_dvd_pow p (Nat.min_le_right r n))).ker

omit [Fact p.Prime] in
theorem finiteUnitSubgroup_eq_kernel (n r : ℕ) (hr : r ≤ n) :
    finiteUnitSubgroup p n r = (ZMod.unitsMap (pow_dvd_pow p hr)).ker := by
  let f : {j : ℕ // j ≤ n} → Subgroup (ZMod (p ^ n))ˣ :=
    fun j => (ZMod.unitsMap (pow_dvd_pow p j.property)).ker
  exact congrArg f (show (⟨min r n, Nat.min_le_right r n⟩ : {j : ℕ // j ≤ n}) =
    ⟨r, hr⟩ from Subtype.ext (Nat.min_eq_left hr))

omit [Fact p.Prime] in
theorem finiteUnitSubgroup_eq_bot (n r : ℕ) (hr : n ≤ r) :
    finiteUnitSubgroup p n r = ⊥ := by
  let f : {j : ℕ // j ≤ n} → Subgroup (ZMod (p ^ n))ˣ :=
    fun j => (ZMod.unitsMap (pow_dvd_pow p j.property)).ker
  have he : finiteUnitSubgroup p n r = (ZMod.unitsMap (pow_dvd_pow p (le_refl n))).ker :=
    congrArg f (show (⟨min r n, Nat.min_le_right r n⟩ : {j : ℕ // j ≤ n}) =
      ⟨n, le_refl n⟩ from Subtype.ext (Nat.min_eq_right hr))
  rw [he, ZMod.unitsMap_self]
  exact MonoidHom.ker_id

omit [Fact p.Prime] in
/-- Each p-power translation subgroup is stable under every unit. -/
theorem finiteTranslationSubgroup_action (n k : ℕ) (u : (ZMod (p ^ n))ˣ)
    {b : Multiplicative (ZMod (p ^ n))} (hb : b ∈ finiteTranslationSubgroup p n k) :
    finiteAffineAction p n u b ∈ finiteTranslationSubgroup p n k := by
  obtain ⟨a, ha⟩ := hb
  refine ⟨finiteAffineAction p n u a, ?_⟩
  change a ^ (p ^ k) = b at ha
  change (finiteAffineAction p n u a) ^ (p ^ k) = finiteAffineAction p n u b
  rw [← map_pow, ha]

/-- The indicated subgroup of the finite affine group. -/
def finiteAffineSubgroup (n k : ℕ) (V : Subgroup (ZMod (p ^ n))ˣ) :
    Subgroup (FullFiniteAffineGroup p n) where
  carrier := {g | g.left ∈ finiteTranslationSubgroup p n k ∧ g.right ∈ V}
  one_mem' := ⟨Subgroup.one_mem _, V.one_mem⟩
  mul_mem' := by
    intro a b ha hb
    exact ⟨Subgroup.mul_mem _ ha.1 (finiteTranslationSubgroup_action p n k a.right hb.1),
      V.mul_mem ha.2 hb.2⟩
  inv_mem' := by
    intro a ha
    exact ⟨finiteTranslationSubgroup_action p n k a.right⁻¹ (Subgroup.inv_mem _ ha.1),
      V.inv_mem ha.2⟩

omit [Fact p.Prime] in
theorem finiteAffineSubgroup_zero_bot (n : ℕ) :
    finiteAffineSubgroup p n 0 ⊥ =
      (SemidirectProduct.inl : Multiplicative (ZMod (p ^ n)) →*
        FullFiniteAffineGroup p n).range := by
  ext g
  rw [SemidirectProduct.range_inl_eq_ker_rightHom, MonoidHom.mem_ker]
  change (g.left ∈ finiteTranslationSubgroup p n 0 ∧ g.right = 1) ↔ g.right = 1
  rw [finiteTranslationSubgroup_zero]
  exact and_iff_right (Subgroup.mem_top _)

omit [Fact p.Prime] in
theorem finiteAffineSubgroup_self_bot (n : ℕ) : finiteAffineSubgroup p n n ⊥ = ⊥ := by
  ext g
  change (g.left ∈ finiteTranslationSubgroup p n n ∧ g.right = 1) ↔ g = 1
  rw [finiteTranslationSubgroup_self]
  constructor
  · rintro ⟨hl, hr⟩
    exact SemidirectProduct.ext hl hr
  · rintro rfl
    exact ⟨rfl, rfl⟩

section NormalAffine

open scoped commutatorElement

variable {p} (n : ℕ)

/-- Conjugation by the unit two extracts the translation coordinate. -/
theorem finiteAffine_commutator_two [hp₂ : Fact (p ≠ 2)] (g : FullFiniteAffineGroup p n) :
    ⁅(SemidirectProduct.inr (unitTwo p n) : FullFiniteAffineGroup p n), g⁆ =
      SemidirectProduct.inl g.left := by
  apply SemidirectProduct.ext
  · simp only [commutatorElement_def, SemidirectProduct.mul_left,
      SemidirectProduct.mul_right, SemidirectProduct.inv_left, SemidirectProduct.inv_right,
      SemidirectProduct.left_inr, SemidirectProduct.right_inr, inv_one, map_one,
      one_mul, mul_one]
    apply congrArg Multiplicative.ofAdd
    change (unitTwo p n : ZMod (p ^ n)) * g.left.toAdd +
      ((unitTwo p n : ZMod (p ^ n)) * (g.right : ZMod (p ^ n)) *
        ((unitTwo p n)⁻¹ : (ZMod (p ^ n))ˣ)) *
        ((g.right⁻¹ : (ZMod (p ^ n))ˣ) * -g.left.toAdd) = g.left.toAdd
    rw [coe_unitTwo]
    have htwo : (2 : ZMod (p ^ n)) *
        ((unitTwo p n)⁻¹ : (ZMod (p ^ n))ˣ) = 1 := by
      simpa only [Units.val_mul, coe_unitTwo, Units.val_one] using
        congrArg (fun u : (ZMod (p ^ n))ˣ => (u : ZMod (p ^ n)))
          (mul_inv_cancel (unitTwo p n))
    have hu : (g.right : ZMod (p ^ n)) *
        (g.right⁻¹ : (ZMod (p ^ n))ˣ) = 1 := Units.mul_inv g.right
    calc
      _ = 2 * g.left.toAdd +
          (2 * ((unitTwo p n)⁻¹ : (ZMod (p ^ n))ˣ)) *
          ((g.right : ZMod (p ^ n)) * (g.right⁻¹ : (ZMod (p ^ n))ˣ)) *
          -g.left.toAdd := by ring
      _ = g.left.toAdd := by rw [htwo, hu]; ring
  · simp [commutatorElement_def, mul_comm]

/-- Every odd-prime normal affine subgroup contains the translation coordinate
of each of its elements, by the commutator with two. -/
theorem finiteAffine_normal_inl_left [hp₂ : Fact (p ≠ 2)]
    (N : Subgroup (FullFiniteAffineGroup p n)) [N.Normal]
    {g : FullFiniteAffineGroup p n} (hg : g ∈ N) :
    SemidirectProduct.inl g.left ∈ N := by
  rw [← finiteAffine_commutator_two n g, commutatorElement_def]
  exact N.mul_mem ((inferInstance : N.Normal).conj_mem g hg _) (N.inv_mem hg)

/-- Its unit coordinate also belongs to the same normal subgroup. -/
theorem finiteAffine_normal_inr_right [hp₂ : Fact (p ≠ 2)]
    (N : Subgroup (FullFiniteAffineGroup p n)) [N.Normal]
    {g : FullFiniteAffineGroup p n} (hg : g ∈ N) :
    SemidirectProduct.inr g.right ∈ N := by
  have he : (SemidirectProduct.inl g.left : FullFiniteAffineGroup p n)⁻¹ * g =
      SemidirectProduct.inr g.right := by
    apply SemidirectProduct.ext <;> simp
  rw [← he]
  exact N.mul_mem (N.inv_mem (finiteAffine_normal_inl_left n N hg)) hg

/-- The normal subgroup splits into its translation intersection and
its unit projection; no assumed semidirect filtration is used. -/
theorem mem_finiteAffine_normal_iff [hp₂ : Fact (p ≠ 2)]
    (N : Subgroup (FullFiniteAffineGroup p n)) [N.Normal]
    (g : FullFiniteAffineGroup p n) :
    g ∈ N ↔ g.left ∈ N.comap SemidirectProduct.inl ∧
      g.right ∈ N.map SemidirectProduct.rightHom := by
  constructor
  · intro hg
    exact ⟨finiteAffine_normal_inl_left n N hg, ⟨g, hg, rfl⟩⟩
  · rintro ⟨hb, h, hh, he⟩
    have hh' := finiteAffine_normal_inr_right n N hh
    change h.right = g.right at he
    rw [he] at hh'
    have hprod := N.mul_mem hb hh'
    simpa only [SemidirectProduct.inl_left_mul_inr_right] using hprod

/-- Multiplying a normal affine subgroup by all pure units keeps precisely
its translation intersection. -/
theorem mem_finiteAffine_units_sup_iff [hp₂ : Fact (p ≠ 2)]
    (N : Subgroup (FullFiniteAffineGroup p n)) [N.Normal]
    (g : FullFiniteAffineGroup p n) :
    g ∈ (SemidirectProduct.inr : (ZMod (p ^ n))ˣ →* FullFiniteAffineGroup p n).range ⊔ N ↔
      g.left ∈ N.comap SemidirectProduct.inl := by
  constructor
  · intro hg
    obtain ⟨a, ⟨v, rfl⟩, h, hh, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hg
    have hm := (inferInstance : N.Normal).conj_mem _
      (finiteAffine_normal_inl_left n N hh) (SemidirectProduct.inr v)
    change SemidirectProduct.inl ((SemidirectProduct.inr v * h).left) ∈ N
    simpa only [SemidirectProduct.mul_left, SemidirectProduct.left_inr,
      SemidirectProduct.right_inr, one_mul, SemidirectProduct.inl_aut, map_inv] using hm
  · intro hb
    have hleft : SemidirectProduct.inl g.left ∈
        (SemidirectProduct.inr : (ZMod (p ^ n))ˣ →* FullFiniteAffineGroup p n).range ⊔ N :=
      (show N ≤ _ from le_sup_right) hb
    have hright : SemidirectProduct.inr g.right ∈
        (SemidirectProduct.inr : (ZMod (p ^ n))ˣ →* FullFiniteAffineGroup p n).range ⊔ N :=
      (show (SemidirectProduct.inr : (ZMod (p ^ n))ˣ →*
        FullFiniteAffineGroup p n).range ≤ _ from le_sup_left) ⟨g.right, rfl⟩
    simpa only [SemidirectProduct.inl_left_mul_inr_right] using
      Subgroup.mul_mem _ hleft hright

/-- The pure-unit product index equals the translation-intersection index. -/
theorem finiteAffine_units_sup_index [hp₂ : Fact (p ≠ 2)]
    (N : Subgroup (FullFiniteAffineGroup p n)) [N.Normal] :
    ((SemidirectProduct.inr : (ZMod (p ^ n))ˣ →* FullFiniteAffineGroup p n).range ⊔ N).index =
      (N.comap SemidirectProduct.inl).index := by
  let P := (SemidirectProduct.inr : (ZMod (p ^ n))ˣ →* FullFiniteAffineGroup p n).range ⊔ N
  let T := N.comap (SemidirectProduct.inl :
    Multiplicative (ZMod (p ^ n)) →* FullFiniteAffineGroup p n)
  let e : P ≃ T × (ZMod (p ^ n))ˣ :=
    { toFun := fun g => ⟨⟨g.val.left, (mem_finiteAffine_units_sup_iff n N g).mp g.property⟩,
        g.val.right⟩
      invFun := fun x => ⟨⟨x.1.val, x.2⟩,
        (mem_finiteAffine_units_sup_iff n N _).mpr x.1.property⟩
      left_inv := fun g => Subtype.ext (SemidirectProduct.ext rfl rfl)
      right_inv := fun x => Prod.ext (Subtype.ext rfl) rfl }
  have hcP : Nat.card P = Nat.card T * Nat.card (ZMod (p ^ n))ˣ :=
    (Nat.card_congr e).trans (Nat.card_prod _ _)
  have hcG : Nat.card (FullFiniteAffineGroup p n) =
      Nat.card (Multiplicative (ZMod (p ^ n))) * Nat.card (ZMod (p ^ n))ˣ :=
    (Nat.card_congr SemidirectProduct.equivProd).trans (Nat.card_prod _ _)
  apply Nat.mul_left_cancel (Nat.card_pos (α := T))
  have h := P.card_mul_index
  rw [hcP, hcG] at h
  have h' : Nat.card T * P.index = Nat.card (Multiplicative (ZMod (p ^ n))) := by
    apply Nat.mul_right_cancel (Nat.card_pos (α := (ZMod (p ^ n))ˣ))
    simpa only [mul_assoc, mul_left_comm, mul_comm] using h
  exact h'.trans T.card_mul_index.symm

omit [Fact p.Prime] in
/-- The index product for a normal affine subgroup. -/
theorem finiteAffine_normal_index (N : Subgroup (FullFiniteAffineGroup p n)) [N.Normal] :
    N.index = (N.map SemidirectProduct.rightHom).index *
      (N.comap SemidirectProduct.inl).index := by
  let ρ : FullFiniteAffineGroup p n →* (ZMod (p ^ n))ˣ := SemidirectProduct.rightHom
  have hj := N.index_map ρ
  rw [MonoidHom.range_eq_top.mpr SemidirectProduct.rightHom_surjective,
    Subgroup.index_top, mul_one] at hj
  calc
    N.index = N.relIndex (N ⊔ ρ.ker) * (N ⊔ ρ.ker).index :=
      (Subgroup.relIndex_mul_index (show N ≤ N ⊔ ρ.ker from le_sup_left)).symm
    _ = N.relIndex ρ.ker * (N.map ρ).index := by rw [Subgroup.relIndex_sup_left, hj]
    _ = (N.map ρ).index * (N.comap SemidirectProduct.inl).index := by
      rw [Subgroup.index_comap, SemidirectProduct.range_inl_eq_ker_rightHom, mul_comm]

end NormalAffine

end FalseTateExtension
end
