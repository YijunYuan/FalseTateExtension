/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FalseTateExtension.Padic.FiniteGaloisStructure
public import FalseTateExtension.KummerProfile
public import FontaineWintenberger.Ramification.Upper.Transport
public import FontaineWintenberger.Ramification.Herbrand.Interval
public import FontaineWintenberger.APF.Finite.ConstantIndex
public import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# The corrected finite False Tate ramification filtration

The intrinsic pure-radical indices determine the translation component of
the actual upper groups, through the original finite affine isomorphism.
Ordinary finite cyclotomic restriction gives the unit component. Their true
indices integrate to the corrected inverse Herbrand table, which determines
the original lower groups and every open-left, closed-right interval. The
first layer is included separately, and literal integer parameters enter
through the proved implication from `padicValInt p a = 1` to a uniformizer.
-/

@[expose] public section

noncomputable section

namespace FalseTateExtension

open IsDiscreteValuationRing FontaineWintenberger

variable (p : ℕ) [Fact p.Prime]

local notation "Qp" => Padic p
local notation "OK" => Valuation.valuationSubring (NormedField.valuation (K := Qp))

/-- The normalized additive valuation of the rational base prime is one. -/
theorem addVal_padicUnitBall_p : addVal OK (p : OK) = 1 := by
  apply addVal_uniformizer
  have h := (MulEquiv.irreducible_iff (f := (padicUnitBallEquiv p).symm)).mpr
    PadicInt.irreducible_p
  simpa only [map_natCast] using h

/-- The actual radical thresholds over the rational base have absolute scale one. -/
theorem radicalUpperBreak_padic (r : ℕ) :
    radicalUpperBreak (K := Qp) p r = (r : ℝ) + 1 / ((p : ℝ) - 1) := by
  simp [radicalUpperBreak, addVal_padicUnitBall_p]

/-- The number of original radical thresholds strictly below the upper parameter.
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

/-- The complete intrinsic index profile of the original nonnormal radical fields,
including the zeroth layer, all finite truncations, and every right endpoint. -/
theorem radicalLayer_apfIndex_eq_pow_translationDepth
    {π : OK} (hπ : Irreducible π) (n : ℕ) {u : ℝ} (hu : 0 ≤ u) :
    apfIndex Qp (radicalLayer p (π : Qp) n) u = p ^ radicalTranslationDepth p n u := by
  induction n with
  | zero =>
    rw [radicalTranslationDepth_zero, pow_zero, radicalLayer_zero,
      apfIndex_algEquiv Qp _ (IntermediateField.botEquiv Qp _),
      apfIndex_eq_one_of_bound_eq_top Qp Qp (apfRamificationBound_self Qp) hu]
  | succ n ih =>
    rw [radicalLayer_apfIndex_succ_threshold p hπ n hu, ih,
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
theorem viviani_fraction_pos_lt_one (hp₂ : p ≠ 2) :
    0 < 1 / ((p : ℝ) - 1) ∧ 1 / ((p : ℝ) - 1) < 1 := by
  have hp : 2 < p := lt_of_le_of_ne (Fact.out : p.Prime).two_le (Ne.symm hp₂)
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

theorem radicalTranslationDepth_integer (hp₂ : p ≠ 2) (n i : ℕ) (hin : i ≤ n) :
    radicalTranslationDepth p n ((i : ℝ) + 1) = i := by
  have hδ := viviani_fraction_pos_lt_one p hp₂
  rw [radicalTranslationDepth_interval p n i (by linarith) (by linarith), Nat.min_eq_right hin]

section NormalAffine

open scoped commutatorElement

variable {p} (n : ℕ)

/-- Conjugation by the actual unit two extracts the translation coordinate. -/
theorem finiteAffine_commutator_two (hp₂ : p ≠ 2) (g : FullFiniteAffineGroup p n) :
    ⁅(SemidirectProduct.inr (finiteAffineTwo p hp₂ n) : FullFiniteAffineGroup p n), g⁆ =
      SemidirectProduct.inl g.left := by
  apply SemidirectProduct.ext
  · simp only [commutatorElement_def, SemidirectProduct.mul_left,
      SemidirectProduct.mul_right, SemidirectProduct.inv_left, SemidirectProduct.inv_right,
      SemidirectProduct.left_inr, SemidirectProduct.right_inr, inv_one, map_one,
      one_mul, mul_one]
    apply congrArg Multiplicative.ofAdd
    change (finiteAffineTwo p hp₂ n : ZMod (p ^ n)) * g.left.toAdd +
      ((finiteAffineTwo p hp₂ n : ZMod (p ^ n)) * (g.right : ZMod (p ^ n)) *
        ((finiteAffineTwo p hp₂ n)⁻¹ : (ZMod (p ^ n))ˣ)) *
        ((g.right⁻¹ : (ZMod (p ^ n))ˣ) * -g.left.toAdd) = g.left.toAdd
    rw [coe_finiteAffineTwo]
    have htwo : (2 : ZMod (p ^ n)) *
        ((finiteAffineTwo p hp₂ n)⁻¹ : (ZMod (p ^ n))ˣ) = 1 := by
      simpa only [Units.val_mul, coe_finiteAffineTwo, Units.val_one] using
        congrArg (fun u : (ZMod (p ^ n))ˣ => (u : ZMod (p ^ n)))
          (mul_inv_cancel (finiteAffineTwo p hp₂ n))
    have hu : (g.right : ZMod (p ^ n)) *
        (g.right⁻¹ : (ZMod (p ^ n))ˣ) = 1 := Units.mul_inv g.right
    calc
      _ = 2 * g.left.toAdd +
          (2 * ((finiteAffineTwo p hp₂ n)⁻¹ : (ZMod (p ^ n))ˣ)) *
          ((g.right : ZMod (p ^ n)) * (g.right⁻¹ : (ZMod (p ^ n))ˣ)) *
          -g.left.toAdd := by ring
      _ = g.left.toAdd := by rw [htwo, hu]; ring
  · simp [commutatorElement_def, mul_comm]

/-- Every odd-prime normal affine subgroup contains the translation coordinate
of each of its elements, by the actual commutator with two. -/
theorem finiteAffine_normal_inl_left (hp₂ : p ≠ 2)
    (N : Subgroup (FullFiniteAffineGroup p n)) [N.Normal]
    {g : FullFiniteAffineGroup p n} (hg : g ∈ N) :
    SemidirectProduct.inl g.left ∈ N := by
  rw [← finiteAffine_commutator_two n hp₂ g, commutatorElement_def]
  exact N.mul_mem ((inferInstance : N.Normal).conj_mem g hg _) (N.inv_mem hg)

/-- Its unit coordinate also belongs to the same actual normal subgroup. -/
theorem finiteAffine_normal_inr_right (hp₂ : p ≠ 2)
    (N : Subgroup (FullFiniteAffineGroup p n)) [N.Normal]
    {g : FullFiniteAffineGroup p n} (hg : g ∈ N) :
    SemidirectProduct.inr g.right ∈ N := by
  have he : (SemidirectProduct.inl g.left : FullFiniteAffineGroup p n)⁻¹ * g =
      SemidirectProduct.inr g.right := by
    apply SemidirectProduct.ext <;> simp
  rw [← he]
  exact N.mul_mem (N.inv_mem (finiteAffine_normal_inl_left n hp₂ N hg)) hg

/-- The normal subgroup splits into its actual translation intersection and
its actual unit projection; no assumed semidirect filtration is used. -/
theorem mem_finiteAffine_normal_iff (hp₂ : p ≠ 2)
    (N : Subgroup (FullFiniteAffineGroup p n)) [N.Normal]
    (g : FullFiniteAffineGroup p n) :
    g ∈ N ↔ g.left ∈ N.comap SemidirectProduct.inl ∧
      g.right ∈ N.map SemidirectProduct.rightHom := by
  constructor
  · intro hg
    exact ⟨finiteAffine_normal_inl_left n hp₂ N hg, ⟨g, hg, rfl⟩⟩
  · rintro ⟨hb, h, hh, he⟩
    have hh' := finiteAffine_normal_inr_right n hp₂ N hh
    change h.right = g.right at he
    rw [he] at hh'
    have hprod := N.mul_mem hb hh'
    simpa only [SemidirectProduct.inl_left_mul_inr_right] using hprod

/-- Multiplying a normal affine subgroup by all pure units keeps precisely
its original translation intersection. -/
theorem mem_finiteAffine_units_sup_iff (hp₂ : p ≠ 2)
    (N : Subgroup (FullFiniteAffineGroup p n)) [N.Normal]
    (g : FullFiniteAffineGroup p n) :
    g ∈ (SemidirectProduct.inr : (ZMod (p ^ n))ˣ →* FullFiniteAffineGroup p n).range ⊔ N ↔
      g.left ∈ N.comap SemidirectProduct.inl := by
  constructor
  · intro hg
    obtain ⟨a, ⟨v, rfl⟩, h, hh, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hg
    have hm := (inferInstance : N.Normal).conj_mem _
      (finiteAffine_normal_inl_left n hp₂ N hh) (SemidirectProduct.inr v)
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

/-- The actual pure-unit product index equals the translation-intersection index. -/
theorem finiteAffine_units_sup_index (hp₂ : p ≠ 2)
    (N : Subgroup (FullFiniteAffineGroup p n)) [N.Normal] :
    ((SemidirectProduct.inr : (ZMod (p ^ n))ˣ →* FullFiniteAffineGroup p n).range ⊔ N).index =
      (N.comap SemidirectProduct.inl).index := by
  let P := (SemidirectProduct.inr : (ZMod (p ^ n))ˣ →* FullFiniteAffineGroup p n).range ⊔ N
  let T := N.comap (SemidirectProduct.inl :
    Multiplicative (ZMod (p ^ n)) →* FullFiniteAffineGroup p n)
  let e : P ≃ T × (ZMod (p ^ n))ˣ :=
    { toFun := fun g => ⟨⟨g.val.left, (mem_finiteAffine_units_sup_iff n hp₂ N g).mp g.property⟩,
        g.val.right⟩
      invFun := fun x => ⟨⟨x.1.val, x.2⟩,
        (mem_finiteAffine_units_sup_iff n hp₂ N _).mpr x.1.property⟩
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
/-- The ordinary index product for an actual normal affine subgroup. -/
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

/-- The canonical subgroup of translations divisible by p^k, represented as
the range of the ordinary power homomorphism on the multiplicative type tag. -/
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

/-- The principal-unit subgroup, truncated at the actual finite level.
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

theorem finiteTranslationSubgroup_card (n k : ℕ) (hk : k ≤ n) :
    Nat.card (finiteTranslationSubgroup p n k) = p ^ (n - k) := by
  have : NeZero (p ^ n) := ⟨pow_ne_zero n (Fact.out : p.Prime).ne_zero⟩
  apply Nat.mul_right_cancel (pow_pos (Fact.out : p.Prime).pos k)
  rw [← finiteTranslationSubgroup_index p n k hk, Subgroup.card_mul_index]
  simp only [Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card]
  rw [finiteTranslationSubgroup_index p n k hk, ← pow_add, Nat.sub_add_cancel hk]

omit [Fact p.Prime] in
/-- Each canonical p-power translation subgroup is stable under every unit. -/
theorem finiteTranslationSubgroup_action (n k : ℕ) (u : (ZMod (p ^ n))ˣ)
    {b : Multiplicative (ZMod (p ^ n))} (hb : b ∈ finiteTranslationSubgroup p n k) :
    finiteAffineAction p n u b ∈ finiteTranslationSubgroup p n k := by
  obtain ⟨a, ha⟩ := hb
  refine ⟨finiteAffineAction p n u a, ?_⟩
  change a ^ (p ^ k) = b at ha
  change (finiteAffineAction p n u a) ^ (p ^ k) = finiteAffineAction p n u b
  rw [← map_pow, ha]

/-- The indicated subgroup of the existing canonical finite affine group. -/
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

section ActualUpper

variable {p} {π : Valuation.valuationSubring (NormedField.valuation (K := Padic p))}
  (hp₂ : p ≠ 2) (hπ : Irreducible π)

local notation "D(" n ")" => falseTateLayer p (π : Qp) (n + 1) (n + 1)
local notation "O(" n ")" => spectralIntegerRing Qp D(n)
local notation "G(" n ")" => D(n) ≃ₐ[Qp] D(n)

local instance vivianiCyclotomicAlgebra (n : ℕ) :
    Algebra (cyclotomicLayer (K := Qp) p (n + 1)) D(n) :=
  (finiteCyclotomicInclusion p (π : Qp) (n + 1)).toRingHom.toAlgebra

local instance vivianiCyclotomicScalarTower (n : ℕ) :
    IsScalarTower Qp (cyclotomicLayer (K := Qp) p (n + 1)) D(n) :=
  IsScalarTower.of_algebraMap_eq (congrFun rfl)

/-- The image of the original upper group under the checked actual finite
affine isomorphism. This retains its original spectral integer ring. -/
def finiteUpperAffineGroup (n : ℕ) (u : ℝ) :
    Subgroup (FullFiniteAffineGroup p (n + 1)) := by
  let e : G(n) ≃* FullFiniteAffineGroup p (n + 1) :=
    finiteDiagonalGaloisEquiv_padic p hp₂ hπ (n + 1)
  let U : Subgroup G(n) := upperRamificationGroup (R := O(n)) G(n) u
  exact U.map e.toMonoidHom

instance finiteUpperAffineGroup_normal (n : ℕ) (u : ℝ) :
    (finiteUpperAffineGroup hp₂ hπ n u).Normal :=
  Subgroup.Normal.map inferInstance _
    (finiteDiagonalGaloisEquiv_padic p hp₂ hπ (n + 1)).surjective

/-- The original pure radical fixer becomes precisely the pure-unit factor. -/
theorem finiteRadicalFixing_map_affine (n : ℕ) :
    ((finiteRadicalInclusion p (π : Qp) (n + 1)).fieldRange.fixingSubgroup : Subgroup G(n)).map
      (finiteDiagonalGaloisEquiv_padic p hp₂ hπ (n + 1)).toMonoidHom =
    (SemidirectProduct.inr : (ZMod (p ^ (n + 1)))ˣ →*
      FullFiniteAffineGroup p (n + 1)).range := by
  ext x
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact (finiteDiagonalGaloisEquiv_padic_mem_units p hp₂ hπ (n + 1) g).mpr hg
  · intro hx
    obtain ⟨g, rfl⟩ := (finiteDiagonalGaloisEquiv_padic p hp₂ hπ (n + 1)).surjective x
    exact ⟨g, (finiteDiagonalGaloisEquiv_padic_mem_units p hp₂ hπ (n + 1) g).mp hx, rfl⟩

/-- The intrinsic index of the original nonnormal radical subfield measures
the translation intersection of the actual upper group. -/
theorem finiteUpperAffine_translation_index (n : ℕ) {u : ℝ} (hu : 0 ≤ u) :
    ((finiteUpperAffineGroup hp₂ hπ n u).comap SemidirectProduct.inl).index =
      p ^ radicalTranslationDepth p (n + 1) u := by
  have := falseTateLayer_isGalois p (π : Qp) (fun h => hπ.ne_zero (Subtype.ext h)) (n + 1)
  let M := (finiteRadicalInclusion p (π : Qp) (n + 1)).fieldRange
  have hi := apfIndex_eq_subgroupRelIndex_of_finiteGalois Qp D(n) M hu
  have hz : upperRamificationGroup (R := O(n)) G(n) 0 = ⊤ := by
    simpa only [upperRamificationGroup_zero, lowerRamificationGroup_zero] using
      lowerRamificationGroup_falseTateLayer_zero p hp₂ hπ n
  simp only [hz, inf_top_eq, Subgroup.relIndex_top_right] at hi
  calc
    _ = ((SemidirectProduct.inr : (ZMod (p ^ (n + 1)))ˣ →*
        FullFiniteAffineGroup p (n + 1)).range ⊔ finiteUpperAffineGroup hp₂ hπ n u).index :=
      (finiteAffine_units_sup_index (n + 1) hp₂ _).symm
    _ = ((M.fixingSubgroup ⊔ upperRamificationGroup (R := O(n)) G(n) u).map
        (finiteDiagonalGaloisEquiv_padic p hp₂ hπ (n + 1)).toMonoidHom).index := by
      rw [Subgroup.map_sup, finiteRadicalFixing_map_affine]
      rfl
    _ = (M.fixingSubgroup ⊔ upperRamificationGroup (R := O(n)) G(n) u).index :=
      Subgroup.index_map_equiv _ (finiteDiagonalGaloisEquiv_padic p hp₂ hπ (n + 1))
    _ = apfIndex Qp M u := hi.symm
    _ = apfIndex Qp (radicalLayer p (π : Qp) (n + 1)) u :=
      (apfIndex_algEquiv Qp (radicalLayer p (π : Qp) (n + 1))
        (finiteRadicalInclusion p (π : Qp) (n + 1)).equivFieldRange u).symm
    _ = _ := radicalLayer_apfIndex_eq_pow_translationDepth p hπ (n + 1) hu

/-- Cyclic subgroup uniqueness turns the intrinsic index into the actual
translation subgroup, without a separate assumed depth certificate. -/
theorem finiteUpperAffine_translation (n : ℕ) {u : ℝ} (hu : 0 ≤ u) :
    (finiteUpperAffineGroup hp₂ hπ n u).comap SemidirectProduct.inl =
      finiteTranslationSubgroup p (n + 1) (radicalTranslationDepth p (n + 1) u) := by
  apply IsCyclic.subgroup_eq_iff_index_eq.mpr
  rw [finiteUpperAffine_translation_index hp₂ hπ n hu,
    finiteTranslationSubgroup_index p _ _ (radicalTranslationDepth_le p _ _)]

/-- The unit projection is exactly the upper group of the original finite
cyclotomic field, by ordinary restriction with its own spectral integers. -/
theorem finiteUpperAffine_unit_projection (n : ℕ) {u : ℝ} (hu : -1 ≤ u) :
    (finiteUpperAffineGroup hp₂ hπ n u).map SemidirectProduct.rightHom =
      (upperRamificationGroup (R := spectralIntegerRing Qp
        (cyclotomicLayer (K := Qp) p (n + 1)))
          (cyclotomicLayer (K := Qp) p (n + 1) ≃ₐ[Qp]
            cyclotomicLayer (K := Qp) p (n + 1)) u).map
        (cyclotomicLayerCharacter p (n + 1)) := by
  have := falseTateLayer_isGalois p (π : Qp) (fun h => hπ.ne_zero (Subtype.ext h)) (n + 1)
  have hc : SemidirectProduct.rightHom.comp
      (finiteDiagonalGaloisEquiv_padic p hp₂ hπ (n + 1)).toMonoidHom =
      (cyclotomicLayerCharacter p (n + 1)).comp
        (diagonalCyclotomicRestriction p (π : Qp) (n + 1)) := by
    apply MonoidHom.ext
    intro g
    exact (cyclotomicLayerCharacterOver_diagonalRestriction p (π : Qp) (n + 1) g).symm
  have hr := restrictNormalHom_map_upperRamificationGroup_tower Qp
    (cyclotomicLayer (K := Qp) p (n + 1)) D(n) u hu
  change (upperRamificationGroup (R := O(n)) G(n) u).map
    (diagonalCyclotomicRestriction p (π : Qp) (n + 1)) = _ at hr
  rw [finiteUpperAffineGroup, Subgroup.map_map, hc, ← Subgroup.map_map, hr]

/-- Every positive finite cyclotomic interval has its exact principal-unit
projection, including its right endpoint. -/
theorem finiteUpperAffine_unit_interval (n r : ℕ) (hr : r ≤ n)
    {u : ℝ} (hu0 : (r : ℝ) < u) (hu1 : u ≤ (r : ℝ) + 1) :
    (finiteUpperAffineGroup hp₂ hπ n u).map SemidirectProduct.rightHom =
      finiteUnitSubgroup p (n + 1) (r + 1) := by
  rw [finiteUpperAffine_unit_projection hp₂ hπ n (by
    linarith [Nat.cast_nonneg (α := ℝ) r]),
    upperRamificationGroup_cyclotomic_eq_comap_unitReduction p n r hr hu0 hu1,
    Subgroup.map_comap_eq_self_of_surjective (cyclotomicLayerCharacter_surjective p (n + 1))]
  exact (finiteUnitSubgroup_eq_kernel p (n + 1) (r + 1) (by omega)).symm

/-- After the final cyclotomic break the unit projection is trivial. -/
theorem finiteUpperAffine_unit_tail (n : ℕ) {u : ℝ} (hu : (n : ℝ) < u) :
    (finiteUpperAffineGroup hp₂ hπ n u).map SemidirectProduct.rightHom = ⊥ := by
  rw [finiteUpperAffine_unit_projection hp₂ hπ n (by
    linarith [Nat.cast_nonneg (α := ℝ) n]),
    upperRamificationGroup_cyclotomic_eq_bot p n hu, Subgroup.map_bot]

/-- The actual finite upper group in affine coordinates on every positive
cyclotomic interval, with its intrinsic strict-threshold translation depth. -/
theorem finiteUpperAffine_eq_interval (n r : ℕ) (hr : r ≤ n)
    {u : ℝ} (hu0 : (r : ℝ) < u) (hu1 : u ≤ (r : ℝ) + 1) :
    finiteUpperAffineGroup hp₂ hπ n u =
      finiteAffineSubgroup p (n + 1) (radicalTranslationDepth p (n + 1) u)
        (finiteUnitSubgroup p (n + 1) (r + 1)) := by
  ext g
  rw [mem_finiteAffine_normal_iff (n + 1) hp₂,
    finiteUpperAffine_translation hp₂ hπ n (by
      linarith [Nat.cast_nonneg (α := ℝ) r]),
    finiteUpperAffine_unit_interval hp₂ hπ n r hr hu0 hu1]
  rfl

/-- The actual finite upper group after the final cyclotomic break is its
canonical translation subgroup with the same original-base depth. -/
theorem finiteUpperAffine_eq_tail (n : ℕ) {u : ℝ} (hu : (n : ℝ) < u) :
    finiteUpperAffineGroup hp₂ hπ n u =
      finiteAffineSubgroup p (n + 1) (radicalTranslationDepth p (n + 1) u) ⊥ := by
  ext g
  rw [mem_finiteAffine_normal_iff (n + 1) hp₂,
    finiteUpperAffine_translation hp₂ hπ n (by
      linarith [Nat.cast_nonneg (α := ℝ) n]),
    finiteUpperAffine_unit_tail hp₂ hπ n hu]
  rfl

include hp₂ hπ in
/-- The original upper index on each closed cyclotomic interval. -/
theorem upperRamificationGroup_falseTate_index (n r : ℕ) (hr : r ≤ n)
    {u : ℝ} (hu0 : (r : ℝ) < u) (hu1 : u ≤ (r : ℝ) + 1) :
    (upperRamificationGroup (R := O(n)) G(n) u).index =
      (p ^ (r + 1)).totient * p ^ radicalTranslationDepth p (n + 1) u := by
  have he : (finiteUpperAffineGroup hp₂ hπ n u).index =
      (upperRamificationGroup (R := O(n)) G(n) u).index :=
    Subgroup.index_map_equiv _ (finiteDiagonalGaloisEquiv_padic p hp₂ hπ (n + 1))
  rw [← he, finiteAffine_normal_index,
    finiteUpperAffine_translation_index hp₂ hπ n (by linarith [Nat.cast_nonneg (α := ℝ) r]),
    finiteUpperAffine_unit_interval hp₂ hπ n r hr hu0 hu1,
    finiteUnitSubgroup_eq_kernel p _ _ (by omega),
    cyclotomicUnitReduction_ker_index p n (r + 1) (by omega)]

include hp₂ hπ in
/-- The original upper index after the final cyclotomic break. -/
theorem upperRamificationGroup_falseTate_index_tail (n : ℕ) {u : ℝ} (hu : (n : ℝ) < u) :
    (upperRamificationGroup (R := O(n)) G(n) u).index =
      (p ^ (n + 1)).totient * p ^ radicalTranslationDepth p (n + 1) u := by
  have he : (finiteUpperAffineGroup hp₂ hπ n u).index =
      (upperRamificationGroup (R := O(n)) G(n) u).index :=
    Subgroup.index_map_equiv _ (finiteDiagonalGaloisEquiv_padic p hp₂ hπ (n + 1))
  rw [← he, finiteAffine_normal_index,
    finiteUpperAffine_translation_index hp₂ hπ n (by linarith [Nat.cast_nonneg (α := ℝ) n]),
    finiteUpperAffine_unit_tail hp₂ hπ n hu, Subgroup.index_bot]
  have : NeZero (p ^ (n + 1)) := ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
  simp only [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient]

/-- The upper group at every fractional Kummer break, including both final
breaks and the single first-layer break, with the actual finite truncation. -/
theorem finiteUpperAffine_fractional (n i : ℕ) (hi : 1 ≤ i) (hin : i ≤ n + 1) :
    finiteUpperAffineGroup hp₂ hπ n ((i : ℝ) + 1 / ((p : ℝ) - 1)) =
      finiteAffineSubgroup p (n + 1) (i - 1) (finiteUnitSubgroup p (n + 1) (i + 1)) := by
  have hδ := viviani_fraction_pos_lt_one p hp₂
  by_cases h : i ≤ n
  · rw [finiteUpperAffine_eq_interval hp₂ hπ n i h (by linarith) (by linarith),
      radicalTranslationDepth_fractional p (n + 1) i hi hin]
  · have hieq : i = n + 1 := by omega
    rw [finiteUpperAffine_eq_tail hp₂ hπ n (by exact_mod_cast
      (show (n : ℝ) < (i : ℝ) + 1 / ((p : ℝ) - 1) by
        have : (n : ℝ) < i := by exact_mod_cast (show n < i by omega)
        linarith)), radicalTranslationDepth_fractional p (n + 1) i hi hin,
      finiteUnitSubgroup_eq_bot p (n + 1) (i + 1) (by omega)]

/-- The integer-break upper group; i=0 includes upper index one. -/
theorem finiteUpperAffine_integer (n i : ℕ) (hi : i ≤ n) :
    finiteUpperAffineGroup hp₂ hπ n ((i : ℝ) + 1) =
      finiteAffineSubgroup p (n + 1) i (finiteUnitSubgroup p (n + 1) (i + 1)) := by
  rw [finiteUpperAffine_eq_interval hp₂ hπ n i hi (by linarith) le_rfl,
    radicalTranslationDepth_integer p hp₂ (n + 1) i (by omega)]

local notation "δ" => 1 / ((p : ℝ) - 1)
local notation "Ψ(" n ")" => inverseHerbrandFunction (R := O(n)) G(n)

include hp₂ hπ in
/-- Full inertia identifies the intrinsic index with the original full upper index. -/
theorem apfIndex_falseTateLayer_eq_upperIndex (n : ℕ) {u : ℝ} (hu : 0 ≤ u) :
    apfIndex Qp D(n) u = (upperRamificationGroup (R := O(n)) G(n) u).index := by
  have := falseTateLayer_isGalois p (π : Qp) (fun h => hπ.ne_zero (Subtype.ext h)) (n + 1)
  have hz : upperRamificationGroup (R := O(n)) G(n) 0 = ⊤ := by
    simpa only [upperRamificationGroup_zero, lowerRamificationGroup_zero] using
      lowerRamificationGroup_falseTateLayer_zero p hp₂ hπ n
  rw [apfIndex_eq_upperRelIndex Qp D(n) hu, hz, Subgroup.relIndex_top_right]

include hp₂ hπ in
private theorem viviani_inverse_affine (n : ℕ) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    (c : ℕ) (hc : ∀ u ∈ Set.Ioc a b,
      (upperRamificationGroup (R := O(n)) G(n) u).index = c) :
    Ψ(n) b - Ψ(n) a = (b - a) * c := by
  have := falseTateLayer_isGalois p (π : Qp) (fun h => hπ.ne_zero (Subtype.ext h)) (n + 1)
  rw [← apfPsi_eq_inverseHerbrandFunction Qp D(n) (by linarith : -1 ≤ a),
    ← apfPsi_eq_inverseHerbrandFunction Qp D(n) (by linarith : -1 ≤ b)]
  exact apfPsi_sub_apfPsi_of_apfIndex_eq Qp D(n) ha hab c fun u hu =>
    (apfIndex_falseTateLayer_eq_upperIndex hp₂ hπ n (ha.trans hu.1.le)).trans (hc u hu)

include hp₂ hπ in
theorem upperRamificationGroup_falseTate_index_initial (n : ℕ) {u : ℝ}
    (hu : 0 < u) (hu1 : u ≤ 1) :
    (upperRamificationGroup (R := O(n)) G(n) u).index = p - 1 := by
  have hδ := viviani_fraction_pos_lt_one p hp₂
  rw [upperRamificationGroup_falseTate_index hp₂ hπ n 0 (Nat.zero_le n)
    (by simpa using hu) (by simpa using hu1),
    radicalTranslationDepth_initial p (n + 1) (by linarith), pow_zero, mul_one,
    Nat.zero_add, pow_one, Nat.totient_prime (Fact.out : p.Prime)]

include hp₂ hπ in
/-- Constant upper index from a fractional break to the following integer. -/
theorem upperRamificationGroup_falseTate_index_fractional_integer
    (n i : ℕ) (hi : i ≤ n) {u : ℝ} (hu0 : (i : ℝ) + δ < u) (hu1 : u ≤ (i : ℝ) + 1) :
    (upperRamificationGroup (R := O(n)) G(n) u).index = (p - 1) * p ^ (2 * i) := by
  have hδ := viviani_fraction_pos_lt_one p hp₂
  rw [upperRamificationGroup_falseTate_index hp₂ hπ n i hi (by linarith) hu1,
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
  have hδ := viviani_fraction_pos_lt_one p hp₂
  rw [upperRamificationGroup_falseTate_index hp₂ hπ n (i + 1) hi
    (by exact_mod_cast hu0) (by push_cast; linarith),
    radicalTranslationDepth_interval p (n + 1) i (by linarith) hu1,
    Nat.min_eq_right (by omega : i ≤ n + 1),
    Nat.totient_prime_pow_succ (Fact.out : p.Prime),
    show 2 * i + 1 = (i + 1) + i by omega, pow_add]
  ring

include hp₂ hπ in
/-- On the final fractional interval both cyclotomic and radical truncation
are retained; this also includes n=0, the first actual layer. -/
theorem upperRamificationGroup_falseTate_index_final (n : ℕ) {u : ℝ}
    (hu0 : (n : ℝ) + δ < u) (hu1 : u ≤ (n : ℝ) + 1 + δ) :
    (upperRamificationGroup (R := O(n)) G(n) u).index = (p - 1) * p ^ (2 * n) := by
  have hδ := viviani_fraction_pos_lt_one p hp₂
  rw [upperRamificationGroup_falseTate_index_tail hp₂ hπ n (by linarith),
    radicalTranslationDepth_interval p (n + 1) n hu0 hu1,
    Nat.min_eq_right (Nat.le_succ n), Nat.totient_prime_pow_succ (Fact.out : p.Prime),
    show 2 * n = n + n by omega, pow_add]
  ring

include hp₂ hπ in
/-- The first integer upper parameter has original lower parameter p-1. -/
theorem inverseHerbrandFunction_falseTate_one (n : ℕ) : Ψ(n) 1 = (p : ℝ) - 1 := by
  have h := viviani_inverse_affine hp₂ hπ n (a := 0) (b := 1) le_rfl zero_le_one
    (p - 1) (fun u hu => upperRamificationGroup_falseTate_index_initial hp₂ hπ n hu.1 hu.2)
  rw [inverseHerbrandFunction_of_nonpos G(n) (by norm_num) le_rfl,
    sub_zero, sub_zero, one_mul] at h
  simpa only [Nat.cast_sub (Fact.out : p.Prime).one_le, Nat.cast_one] using h

include hp₂ hπ in
/-- Every fractional lower break before the last one. The auxiliary i=0
value is included to make the uniform recurrence start without an empty-row case. -/
theorem inverseHerbrandFunction_falseTate_fractional (n i : ℕ) (hi : i ≤ n) :
    Ψ(n) ((i : ℝ) + δ) =
      (2 * (p : ℝ) ^ (2 * i) + (p : ℝ) - 1) / ((p : ℝ) + 1) := by
  have hδ := viviani_fraction_pos_lt_one p hp₂
  have hp : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hpm : (p : ℝ) - 1 ≠ 0 := by linarith
  have hpp : (p : ℝ) + 1 ≠ 0 := by positivity
  induction i with
  | zero =>
    have h := viviani_inverse_affine hp₂ hπ n (a := 0) (b := δ) le_rfl hδ.1.le
      (p - 1) (fun u hu => upperRamificationGroup_falseTate_index_initial hp₂ hπ n
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
    have h₁ := viviani_inverse_affine hp₂ hπ n
      (a := (i : ℝ) + δ) (b := (i : ℝ) + 1)
      (add_nonneg (Nat.cast_nonneg i) hδ.1.le) (by linarith) ((p - 1) * p ^ (2 * i))
      (fun u hu => upperRamificationGroup_falseTate_index_fractional_integer
        hp₂ hπ n i hi' hu.1 hu.2)
    have h₂ := viviani_inverse_affine hp₂ hπ n
      (a := (i : ℝ) + 1) (b := (i : ℝ) + 1 + δ)
      (by positivity) (by linarith) ((p - 1) * p ^ (2 * i + 1))
      (fun u hu => upperRamificationGroup_falseTate_index_integer_fractional
        hp₂ hπ n i hi hu.1 hu.2)
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
/-- The corrected integer-break formula has exponent 2i+1. -/
theorem inverseHerbrandFunction_falseTate_integer (n i : ℕ) (hi : i ≤ n) :
    Ψ(n) ((i : ℝ) + 1) =
      ((p : ℝ) - 1) * ((p : ℝ) ^ (2 * i + 1) + 1) / ((p : ℝ) + 1) := by
  have hδ := viviani_fraction_pos_lt_one p hp₂
  have hp : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hpm : (p : ℝ) - 1 ≠ 0 := by linarith
  have hpp : (p : ℝ) + 1 ≠ 0 := by positivity
  have h := viviani_inverse_affine hp₂ hπ n
    (a := (i : ℝ) + δ) (b := (i : ℝ) + 1)
    (add_nonneg (Nat.cast_nonneg i) hδ.1.le) (by linarith)
    ((p - 1) * p ^ (2 * i))
    (fun u hu => upperRamificationGroup_falseTate_index_fractional_integer
      hp₂ hπ n i hi hu.1 hu.2)
  simp only [Nat.cast_mul, Nat.cast_pow,
    Nat.cast_sub (Fact.out : p.Prime).one_le, Nat.cast_one] at h
  calc
    _ = Ψ(n) ((i : ℝ) + δ) +
        (1 - δ) * (((p : ℝ) - 1) * (p : ℝ) ^ (2 * i)) := by linarith
    _ = _ := by
      rw [inverseHerbrandFunction_falseTate_fractional hp₂ hπ n i hi, pow_succ]
      field_simp [hpm, hpp]
      ring

include hp₂ hπ in
/-- The final original lower break, valid also in the first layer n=0. -/
theorem inverseHerbrandFunction_falseTate_final (n : ℕ) :
    Ψ(n) ((n : ℝ) + 1 + δ) =
      ((p : ℝ) ^ (2 * (n + 1)) + (p : ℝ) ^ (2 * n) + (p : ℝ) - 1) / ((p : ℝ) + 1) := by
  have hδ := viviani_fraction_pos_lt_one p hp₂
  have h := viviani_inverse_affine hp₂ hπ n
    (a := (n : ℝ) + δ) (b := (n : ℝ) + 1 + δ)
    (add_nonneg (Nat.cast_nonneg n) hδ.1.le) (by linarith)
    ((p - 1) * p ^ (2 * n))
    (fun u hu => upperRamificationGroup_falseTate_index_final hp₂ hπ n hu.1 hu.2)
  simp only [Nat.cast_mul, Nat.cast_pow,
    Nat.cast_sub (Fact.out : p.Prime).one_le, Nat.cast_one] at h
  calc
    _ = Ψ(n) ((n : ℝ) + δ) + ((p : ℝ) - 1) * (p : ℝ) ^ (2 * n) := by linarith
    _ = _ := by
      rw [inverseHerbrandFunction_falseTate_fractional hp₂ hπ n n le_rfl,
        show 2 * (n + 1) = 2 * n + 2 by omega]
      simp only [pow_add, pow_two]
      field_simp
      ring

include hp₂ hπ in
/-- The original real lower groups at the fractional table entries. -/
theorem lowerRamificationGroupReal_falseTate_fractional (n i : ℕ)
    (hi : 1 ≤ i) (hin : i ≤ n) :
    (lowerRamificationGroupReal G(n) (IsLocalRing.maximalIdeal O(n))
      ((2 * (p : ℝ) ^ (2 * i) + (p : ℝ) - 1) / ((p : ℝ) + 1))).map
        (finiteDiagonalGaloisEquiv_padic p hp₂ hπ (n + 1)).toMonoidHom =
      finiteAffineSubgroup p (n + 1) (i - 1) (finiteUnitSubgroup p (n + 1) (i + 1)) := by
  rw [← inverseHerbrandFunction_falseTate_fractional hp₂ hπ n i hin]
  exact finiteUpperAffine_fractional hp₂ hπ n i hi (by omega)

include hp₂ hπ in
/-- The original real lower groups at the corrected integer table entries. -/
theorem lowerRamificationGroupReal_falseTate_integer (n i : ℕ) (hi : i ≤ n) :
    (lowerRamificationGroupReal G(n) (IsLocalRing.maximalIdeal O(n))
      (((p : ℝ) - 1) * ((p : ℝ) ^ (2 * i + 1) + 1) / ((p : ℝ) + 1))).map
        (finiteDiagonalGaloisEquiv_padic p hp₂ hπ (n + 1)).toMonoidHom =
      finiteAffineSubgroup p (n + 1) i (finiteUnitSubgroup p (n + 1) (i + 1)) := by
  rw [← inverseHerbrandFunction_falseTate_integer hp₂ hπ n i hi]
  exact finiteUpperAffine_integer hp₂ hπ n i hi

include hp₂ hπ in
/-- The final original lower group is the order-p translation subgroup. -/
theorem lowerRamificationGroupReal_falseTate_final (n : ℕ) :
    (lowerRamificationGroupReal G(n) (IsLocalRing.maximalIdeal O(n))
      (((p : ℝ) ^ (2 * (n + 1)) + (p : ℝ) ^ (2 * n) + (p : ℝ) - 1) /
        ((p : ℝ) + 1))).map
        (finiteDiagonalGaloisEquiv_padic p hp₂ hπ (n + 1)).toMonoidHom =
      finiteAffineSubgroup p (n + 1) n ⊥ := by
  rw [← inverseHerbrandFunction_falseTate_final hp₂ hπ n]
  have h := finiteUpperAffine_fractional hp₂ hπ n (n + 1) (by omega) le_rfl
  simp only [Nat.cast_add, Nat.cast_one, Nat.add_sub_cancel,
    finiteUnitSubgroup_eq_bot p (n + 1) (n + 1 + 1) (by omega)] at h
  exact h

include hp₂ hπ in
theorem herbrandFunction_falseTate_fractional (n i : ℕ) (hi : i ≤ n) :
    herbrandFunction (R := O(n)) G(n)
      ((2 * (p : ℝ) ^ (2 * i) + (p : ℝ) - 1) / ((p : ℝ) + 1)) = (i : ℝ) + δ := by
  have hδ := viviani_fraction_pos_lt_one p hp₂
  rw [← inverseHerbrandFunction_falseTate_fractional hp₂ hπ n i hi,
    herbrandFunction_inverseHerbrandFunction G(n) (by linarith [Nat.cast_nonneg (α := ℝ) i])]

include hp₂ hπ in
theorem herbrandFunction_falseTate_integer (n i : ℕ) (hi : i ≤ n) :
    herbrandFunction (R := O(n)) G(n)
      (((p : ℝ) - 1) * ((p : ℝ) ^ (2 * i + 1) + 1) / ((p : ℝ) + 1)) = (i : ℝ) + 1 := by
  rw [← inverseHerbrandFunction_falseTate_integer hp₂ hπ n i hi,
    herbrandFunction_inverseHerbrandFunction G(n) (by linarith [Nat.cast_nonneg (α := ℝ) i])]

include hp₂ hπ in
theorem herbrandFunction_falseTate_final (n : ℕ) :
    herbrandFunction (R := O(n)) G(n)
      (((p : ℝ) ^ (2 * (n + 1)) + (p : ℝ) ^ (2 * n) + (p : ℝ) - 1) /
        ((p : ℝ) + 1)) = (n : ℝ) + 1 + δ := by
  have hδ := viviani_fraction_pos_lt_one p hp₂
  rw [← inverseHerbrandFunction_falseTate_final hp₂ hπ n,
    herbrandFunction_inverseHerbrandFunction G(n) (by linarith [Nat.cast_nonneg (α := ℝ) n])]

/-- The complete initial positive upper interval, retaining its right endpoint. -/
theorem finiteUpperAffine_initial (n : ℕ) {u : ℝ} (hu : 0 < u) (hu1 : u ≤ 1) :
    finiteUpperAffineGroup hp₂ hπ n u =
      finiteAffineSubgroup p (n + 1) 0 (finiteUnitSubgroup p (n + 1) 1) := by
  have hδ := viviani_fraction_pos_lt_one p hp₂
  rw [finiteUpperAffine_eq_interval hp₂ hπ n 0 (Nat.zero_le n)
    (by simpa using hu) (by simpa using hu1),
    radicalTranslationDepth_initial p (n + 1) (by linarith), Nat.zero_add]

/-- Every open-left, closed-right upper interval after a fractional break. -/
theorem finiteUpperAffine_fractional_integer (n i : ℕ) (hi : i ≤ n)
    {u : ℝ} (hu0 : (i : ℝ) + δ < u) (hu1 : u ≤ (i : ℝ) + 1) :
    finiteUpperAffineGroup hp₂ hπ n u =
      finiteAffineSubgroup p (n + 1) i (finiteUnitSubgroup p (n + 1) (i + 1)) := by
  have hδ := viviani_fraction_pos_lt_one p hp₂
  rw [finiteUpperAffine_eq_interval hp₂ hπ n i hi (by linarith) hu1,
    radicalTranslationDepth_interval p (n + 1) i hu0 (by linarith),
    Nat.min_eq_right (by omega : i ≤ n + 1)]

/-- Every open-left, closed-right upper interval after an integer break. -/
theorem finiteUpperAffine_integer_fractional (n i : ℕ) (hi : i + 1 ≤ n)
    {u : ℝ} (hu0 : (i : ℝ) + 1 < u) (hu1 : u ≤ (i : ℝ) + 1 + δ) :
    finiteUpperAffineGroup hp₂ hπ n u =
      finiteAffineSubgroup p (n + 1) i (finiteUnitSubgroup p (n + 1) (i + 2)) := by
  have hδ := viviani_fraction_pos_lt_one p hp₂
  rw [finiteUpperAffine_eq_interval hp₂ hπ n (i + 1) hi
    (by exact_mod_cast hu0) (by push_cast; linarith),
    radicalTranslationDepth_interval p (n + 1) i (by linarith) hu1,
    Nat.min_eq_right (by omega : i ≤ n + 1)]

/-- The final entire fractional upper interval, including the first layer. -/
theorem finiteUpperAffine_final_interval (n : ℕ) {u : ℝ}
    (hu0 : (n : ℝ) + δ < u) (hu1 : u ≤ (n : ℝ) + 1 + δ) :
    finiteUpperAffineGroup hp₂ hπ n u = finiteAffineSubgroup p (n + 1) n ⊥ := by
  have hδ := viviani_fraction_pos_lt_one p hp₂
  rw [finiteUpperAffine_eq_tail hp₂ hπ n (by linarith),
    radicalTranslationDepth_interval p (n + 1) n hu0 hu1, Nat.min_eq_right (Nat.le_succ n)]

/-- The finite upper groups vanish strictly after the final actual break. -/
theorem finiteUpperAffine_eq_bot (n : ℕ) {u : ℝ} (hu : (n : ℝ) + 1 + δ < u) :
    finiteUpperAffineGroup hp₂ hπ n u = ⊥ := by
  have hδ := viviani_fraction_pos_lt_one p hp₂
  rw [finiteUpperAffine_eq_tail hp₂ hπ n (by linarith),
    radicalTranslationDepth_tail p (n + 1) (by push_cast; exact hu),
    finiteAffineSubgroup_self_bot]

include hp₂ hπ in
theorem lowerRamificationGroupReal_falseTate_nonpos (n : ℕ) {t : ℝ} (ht : t ≤ 0) :
    lowerRamificationGroupReal G(n) (IsLocalRing.maximalIdeal O(n)) t = ⊤ := by
  have hz : lowerRamificationGroupReal G(n) (IsLocalRing.maximalIdeal O(n)) 0 = ⊤ := by
    simpa only [lowerRamificationGroupReal_zero, lowerRamificationGroup_zero] using
      lowerRamificationGroup_falseTateLayer_zero p hp₂ hπ n
  apply top_le_iff.mp
  rw [← hz]
  exact lowerRamificationGroupReal_antitone G(n) _ ht

include hp₂ hπ in
theorem upperRamificationGroup_falseTate_nonpos (n : ℕ) {u : ℝ}
    (hu : -1 ≤ u) (hu0 : u ≤ 0) : upperRamificationGroup (R := O(n)) G(n) u = ⊤ := by
  rw [upperRamificationGroup, inverseHerbrandFunction_of_nonpos G(n) hu hu0]
  exact lowerRamificationGroupReal_falseTate_nonpos hp₂ hπ n hu0

private theorem viviani_lower_parameter (n : ℕ) {a b t : ℝ}
    (ha : -1 ≤ a) (hb : -1 ≤ b) (ht0 : Ψ(n) a < t) (ht1 : t ≤ Ψ(n) b) :
    a < herbrandFunction (R := O(n)) G(n) t ∧
      herbrandFunction (R := O(n)) G(n) t ≤ b :=
  herbrandFunction_mem_Ioc_of_inverseHerbrandFunction G(n) ha hb ht0 ht1

private theorem viviani_lower_map (n : ℕ) {t : ℝ} (ht : -1 ≤ t) :
    (lowerRamificationGroupReal G(n) (IsLocalRing.maximalIdeal O(n)) t).map
      (finiteDiagonalGaloisEquiv_padic p hp₂ hπ (n + 1)).toMonoidHom =
      finiteUpperAffineGroup hp₂ hπ n (herbrandFunction (R := O(n)) G(n) t) := by
  rw [finiteUpperAffineGroup, upperRamificationGroup_herbrandFunction G(n) ht]

/-- The initial original lower interval is exactly 0<t≤p-1. -/
theorem lowerRamificationGroupReal_falseTate_initial (n : ℕ) {t : ℝ}
    (ht0 : 0 < t) (ht1 : t ≤ (p : ℝ) - 1) :
    (lowerRamificationGroupReal G(n) (IsLocalRing.maximalIdeal O(n)) t).map
      (finiteDiagonalGaloisEquiv_padic p hp₂ hπ (n + 1)).toMonoidHom =
      finiteAffineSubgroup p (n + 1) 0 (finiteUnitSubgroup p (n + 1) 1) := by
  have h := viviani_lower_parameter (π := π) n (a := 0) (b := 1)
    (by norm_num) (by norm_num)
    (by simpa only [inverseHerbrandFunction_of_nonpos G(n) (by norm_num) le_rfl] using ht0)
    (by simpa only [inverseHerbrandFunction_falseTate_one hp₂ hπ n] using ht1)
  rw [viviani_lower_map hp₂ hπ n (by linarith)]
  exact finiteUpperAffine_initial hp₂ hπ n h.1 h.2

/-- The lower intervals corresponding to the fractional-to-integer rows. -/
theorem lowerRamificationGroupReal_falseTate_fractional_integer (n i : ℕ) (hi : i ≤ n)
    {t : ℝ}
    (ht0 : (2 * (p : ℝ) ^ (2 * i) + (p : ℝ) - 1) / ((p : ℝ) + 1) < t)
    (ht1 : t ≤ ((p : ℝ) - 1) * ((p : ℝ) ^ (2 * i + 1) + 1) / ((p : ℝ) + 1)) :
    (lowerRamificationGroupReal G(n) (IsLocalRing.maximalIdeal O(n)) t).map
      (finiteDiagonalGaloisEquiv_padic p hp₂ hπ (n + 1)).toMonoidHom =
      finiteAffineSubgroup p (n + 1) i (finiteUnitSubgroup p (n + 1) (i + 1)) := by
  have hδ := viviani_fraction_pos_lt_one p hp₂
  have h0 : Ψ(n) ((i : ℝ) + δ) < t := by
    simpa only [inverseHerbrandFunction_falseTate_fractional hp₂ hπ n i hi] using ht0
  have h1 : t ≤ Ψ(n) ((i : ℝ) + 1) := by
    simpa only [inverseHerbrandFunction_falseTate_integer hp₂ hπ n i hi] using ht1
  have h := viviani_lower_parameter (π := π) n
    (by linarith [Nat.cast_nonneg (α := ℝ) i])
    (by linarith [Nat.cast_nonneg (α := ℝ) i]) h0 h1
  rw [viviani_lower_map hp₂ hπ n
    ((inverseHerbrandFunction_mem_Ici (R := O(n)) G(n) _).trans h0.le)]
  exact finiteUpperAffine_fractional_integer hp₂ hπ n i hi h.1 h.2

/-- The lower intervals corresponding to the integer-to-fractional rows. -/
theorem lowerRamificationGroupReal_falseTate_integer_fractional (n i : ℕ) (hi : i + 1 ≤ n)
    {t : ℝ}
    (ht0 : ((p : ℝ) - 1) * ((p : ℝ) ^ (2 * i + 1) + 1) / ((p : ℝ) + 1) < t)
    (ht1 : t ≤ (2 * (p : ℝ) ^ (2 * (i + 1)) + (p : ℝ) - 1) / ((p : ℝ) + 1)) :
    (lowerRamificationGroupReal G(n) (IsLocalRing.maximalIdeal O(n)) t).map
      (finiteDiagonalGaloisEquiv_padic p hp₂ hπ (n + 1)).toMonoidHom =
      finiteAffineSubgroup p (n + 1) i (finiteUnitSubgroup p (n + 1) (i + 2)) := by
  have hδ := viviani_fraction_pos_lt_one p hp₂
  have h0 : Ψ(n) ((i : ℝ) + 1) < t := by
    simpa only [inverseHerbrandFunction_falseTate_integer hp₂ hπ n i (by omega)] using ht0
  have h1 : t ≤ Ψ(n) ((i : ℝ) + 1 + δ) := by
    have hψ := inverseHerbrandFunction_falseTate_fractional hp₂ hπ n (i + 1) hi
    simp only [Nat.cast_add, Nat.cast_one] at hψ
    rw [hψ]
    exact ht1
  have h := viviani_lower_parameter (π := π) n
    (by linarith [Nat.cast_nonneg (α := ℝ) i])
    (by linarith [Nat.cast_nonneg (α := ℝ) i]) h0 h1
  rw [viviani_lower_map hp₂ hπ n
    ((inverseHerbrandFunction_mem_Ici (R := O(n)) G(n) _).trans h0.le)]
  exact finiteUpperAffine_integer_fractional hp₂ hπ n i hi h.1 h.2

/-- The final original lower interval, before the last group vanishes. -/
theorem lowerRamificationGroupReal_falseTate_final_interval (n : ℕ) {t : ℝ}
    (ht0 : (2 * (p : ℝ) ^ (2 * n) + (p : ℝ) - 1) / ((p : ℝ) + 1) < t)
    (ht1 : t ≤ ((p : ℝ) ^ (2 * (n + 1)) + (p : ℝ) ^ (2 * n) + (p : ℝ) - 1) /
      ((p : ℝ) + 1)) :
    (lowerRamificationGroupReal G(n) (IsLocalRing.maximalIdeal O(n)) t).map
      (finiteDiagonalGaloisEquiv_padic p hp₂ hπ (n + 1)).toMonoidHom =
      finiteAffineSubgroup p (n + 1) n ⊥ := by
  have hδ := viviani_fraction_pos_lt_one p hp₂
  have h0 : Ψ(n) ((n : ℝ) + δ) < t := by
    simpa only [inverseHerbrandFunction_falseTate_fractional hp₂ hπ n n le_rfl] using ht0
  have h1 : t ≤ Ψ(n) ((n : ℝ) + 1 + δ) := by
    simpa only [inverseHerbrandFunction_falseTate_final hp₂ hπ n] using ht1
  have h := viviani_lower_parameter (π := π) n
    (by linarith [Nat.cast_nonneg (α := ℝ) n])
    (by linarith [Nat.cast_nonneg (α := ℝ) n]) h0 h1
  rw [viviani_lower_map hp₂ hπ n
    ((inverseHerbrandFunction_mem_Ici (R := O(n)) G(n) _).trans h0.le)]
  exact finiteUpperAffine_final_interval hp₂ hπ n h.1 h.2

include hp₂ hπ in
/-- The original upper group is trivial strictly after the final upper break. -/
theorem upperRamificationGroup_falseTate_eq_bot (n : ℕ) {u : ℝ}
    (hu : (n : ℝ) + 1 + δ < u) : upperRamificationGroup (R := O(n)) G(n) u = ⊥ := by
  apply Subgroup.map_injective
    (f := (finiteDiagonalGaloisEquiv_padic p hp₂ hπ (n + 1)).toMonoidHom)
    (finiteDiagonalGaloisEquiv_padic p hp₂ hπ (n + 1)).injective
  rw [Subgroup.map_bot]
  exact finiteUpperAffine_eq_bot hp₂ hπ n hu

include hp₂ hπ in
/-- The original lower group is trivial strictly after the final lower break. -/
theorem lowerRamificationGroupReal_falseTate_eq_bot (n : ℕ) {t : ℝ}
    (ht : ((p : ℝ) ^ (2 * (n + 1)) + (p : ℝ) ^ (2 * n) + (p : ℝ) - 1) /
      ((p : ℝ) + 1) < t) :
    lowerRamificationGroupReal G(n) (IsLocalRing.maximalIdeal O(n)) t = ⊥ := by
  have hδ := viviani_fraction_pos_lt_one p hp₂
  have h0 : Ψ(n) ((n : ℝ) + 1 + δ) < t := by
    simpa only [inverseHerbrandFunction_falseTate_final hp₂ hπ n] using ht
  have htm : -1 ≤ t := (inverseHerbrandFunction_mem_Ici (R := O(n)) G(n) _).trans h0.le
  have hu : (n : ℝ) + 1 + δ < herbrandFunction (R := O(n)) G(n) t := by
    have ha : -1 ≤ (n : ℝ) + 1 + δ := by linarith [Nat.cast_nonneg (α := ℝ) n]
    apply ((strictMonoOn_inverseHerbrandFunction (R := O(n)) G(n)).lt_iff_lt
      ha (herbrandFunction_mem_Ici G(n) htm)).mp
    simpa only [inverseHerbrandFunction_herbrandFunction G(n) htm] using h0
  rw [← upperRamificationGroup_herbrandFunction G(n) htm]
  exact upperRamificationGroup_falseTate_eq_bot hp₂ hπ n hu

/-- Negative upper parameters through zero give the full actual affine group. -/
theorem finiteUpperAffine_nonpos (n : ℕ) {u : ℝ} (hu : -1 ≤ u) (hu0 : u ≤ 0) :
    finiteUpperAffineGroup hp₂ hπ n u = ⊤ := by
  rw [finiteUpperAffineGroup, upperRamificationGroup_falseTate_nonpos hp₂ hπ n hu hu0,
    Subgroup.map_top, MonoidHom.range_eq_top.mpr
      (finiteDiagonalGaloisEquiv_padic p hp₂ hπ (n + 1)).surjective]

/-- The usual first-layer upper break equals the first strict radical threshold. -/
theorem viviani_first_break : 1 + δ = (p : ℝ) / ((p : ℝ) - 1) := by
  have hp : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  field_simp
  ring

/-- The positive first-layer upper group is precisely the original translation
factor, through and including p/(p-1). -/
theorem finiteUpperAffine_first_layer {u : ℝ}
    (hu : 0 < u) (hu1 : u ≤ (p : ℝ) / ((p : ℝ) - 1)) :
    finiteUpperAffineGroup hp₂ hπ 0 u =
      (SemidirectProduct.inl :
        Multiplicative (ZMod (p ^ 1)) →* FullFiniteAffineGroup p 1).range := by
  have hb : u ≤ 1 + δ := by rw [viviani_first_break]; exact hu1
  rw [finiteUpperAffine_eq_tail hp₂ hπ 0 (by simpa using hu),
    radicalTranslationDepth_initial p 1 hb, finiteAffineSubgroup_zero_bot]

/-- The full first-layer upper filtration, with the actual right endpoint. -/
theorem finiteUpperAffine_first_layer_filtration {u : ℝ} (hu : -1 ≤ u) :
    finiteUpperAffineGroup hp₂ hπ 0 u =
      if u ≤ 0 then ⊤ else if u ≤ (p : ℝ) / ((p : ℝ) - 1) then
        (SemidirectProduct.inl : Multiplicative (ZMod (p ^ 1)) →* FullFiniteAffineGroup p 1).range
        else ⊥ := by
  by_cases hu0 : u ≤ 0
  · rw [ite_eq_left hu0]
    exact finiteUpperAffine_nonpos hp₂ hπ 0 hu hu0
  · rw [ite_eq_right hu0]
    by_cases hb : u ≤ (p : ℝ) / ((p : ℝ) - 1)
    · rw [ite_eq_left hb]
      exact finiteUpperAffine_first_layer hp₂ hπ (lt_of_not_ge hu0) hb
    · rw [ite_eq_right hb]
      apply finiteUpperAffine_eq_bot hp₂ hπ 0
      simpa only [Nat.cast_zero, zero_add, viviani_first_break] using lt_of_not_ge hb

include hp₂ hπ in
/-- The first-layer inverse Herbrand function on its whole nontrivial interval. -/
theorem inverseHerbrandFunction_falseTate_first_layer {u : ℝ}
    (hu : 0 ≤ u) (hu1 : u ≤ (p : ℝ) / ((p : ℝ) - 1)) :
    Ψ(0) u = ((p : ℝ) - 1) * u := by
  have hb : u ≤ 1 + δ := by rw [viviani_first_break]; exact hu1
  have h := viviani_inverse_affine hp₂ hπ 0 (a := 0) (b := u) le_rfl hu (p - 1) (by
    intro v hv
    rw [upperRamificationGroup_falseTate_index_tail hp₂ hπ 0 (by simpa using hv.1),
      radicalTranslationDepth_initial p 1 (hv.2.trans hb)]
    simp [Nat.totient_prime (Fact.out : p.Prime)])
  rw [inverseHerbrandFunction_of_nonpos G(0) (by norm_num) le_rfl, sub_zero, sub_zero] at h
  simpa only [Nat.cast_sub (Fact.out : p.Prime).one_le, Nat.cast_one, mul_comm] using h

include hp₂ hπ in
/-- The actual positive first-layer lower break is p. -/
theorem inverseHerbrandFunction_falseTate_first_break :
    Ψ(0) ((p : ℝ) / ((p : ℝ) - 1)) = p := by
  have hp : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  rw [inverseHerbrandFunction_falseTate_first_layer hp₂ hπ (by positivity) le_rfl]
  field_simp

/-- The positive original first-layer lower group, including its final endpoint. -/
theorem lowerRamificationGroupReal_falseTate_first_layer {t : ℝ}
    (ht : 0 < t) (ht1 : t ≤ p) :
    (lowerRamificationGroupReal G(0) (IsLocalRing.maximalIdeal O(0)) t).map
      (finiteDiagonalGaloisEquiv_padic p hp₂ hπ 1).toMonoidHom =
      (SemidirectProduct.inl :
        Multiplicative (ZMod (p ^ 1)) →* FullFiniteAffineGroup p 1).range := by
  have hp : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have h := viviani_lower_parameter (π := π) 0 (a := 0)
    (b := (p : ℝ) / ((p : ℝ) - 1)) (by norm_num)
    (by
      have hnonneg : (0 : ℝ) ≤ (p : ℝ) / ((p : ℝ) - 1) := by positivity
      linarith)
    (by simpa only [inverseHerbrandFunction_of_nonpos G(0) (by norm_num) le_rfl] using ht)
    (by simpa only [inverseHerbrandFunction_falseTate_first_break hp₂ hπ] using ht1)
  rw [viviani_lower_map hp₂ hπ 0 (by linarith)]
  exact finiteUpperAffine_first_layer hp₂ hπ h.1 h.2

/-- The full original first-layer lower filtration. -/
theorem lowerRamificationGroupReal_falseTate_first_layer_filtration (t : ℝ) :
    (lowerRamificationGroupReal G(0) (IsLocalRing.maximalIdeal O(0)) t).map
      (finiteDiagonalGaloisEquiv_padic p hp₂ hπ 1).toMonoidHom =
      if t ≤ 0 then ⊤ else if t ≤ (p : ℝ) then
        (SemidirectProduct.inl : Multiplicative (ZMod (p ^ 1)) →* FullFiniteAffineGroup p 1).range
        else ⊥ := by
  by_cases ht0 : t ≤ 0
  · rw [ite_eq_left ht0, lowerRamificationGroupReal_falseTate_nonpos hp₂ hπ 0 ht0,
      Subgroup.map_top, MonoidHom.range_eq_top.mpr
        (finiteDiagonalGaloisEquiv_padic p hp₂ hπ 1).surjective]
  · rw [ite_eq_right ht0]
    by_cases ht1 : t ≤ (p : ℝ)
    · rw [ite_eq_left ht1]
      exact lowerRamificationGroupReal_falseTate_first_layer hp₂ hπ (lt_of_not_ge ht0) ht1
    · rw [ite_eq_right ht1]
      have hfinal : ((p : ℝ) ^ (2 * (0 + 1)) + (p : ℝ) ^ (2 * 0) + (p : ℝ) - 1) /
          ((p : ℝ) + 1) = p := by field_simp; ring
      rw [lowerRamificationGroupReal_falseTate_eq_bot hp₂ hπ 0 (by
        rw [hfinal]; exact lt_of_not_ge ht1), Subgroup.map_bot]

end ActualUpper

section IntegerParameter

/-- The literal integer hypothesis v_p(a)=1 supplies the actual rational
valuation-ring uniformizer used by every preceding coordinate bridge. -/
theorem irreducible_integerParameter (a : ℤ) (ha : padicValInt p a = 1) :
    Irreducible (a : OK) := by
  have haZ : a ≠ 0 := by
    rintro rfl
    simp only [padicValInt.zero] at ha
    omega
  have ha0 : (a : PadicInt p) ≠ 0 := Int.cast_ne_zero.mpr haZ
  have hv : (a : PadicInt p).valuation = 1 := by
    have h : ((a : PadicInt p).valuation : ℤ) = 1 := by
      rw [← PadicInt.valuation_coe, PadicInt.coe_intCast, Padic.valuation_intCast, ha]
      rfl
    exact_mod_cast h
  have hass : Associated (a : PadicInt p) (p : PadicInt p) := by
    rw [PadicInt.unitCoeff_spec ha0, hv, pow_one]
    exact associated_unit_mul_left _ _ (PadicInt.unitCoeff ha0).isUnit
  have hirr := hass.irreducible_iff.mpr PadicInt.irreducible_p
  apply (MulEquiv.irreducible_iff (padicUnitBallEquiv p)).mp
  simpa only [map_intCast] using hirr

/-- Literal integer parameters in Viviani's hypothesis have the same actual
finite upper groups; no new coordinate or filtration hypothesis is required. -/
theorem finiteUpperAffine_integerParameter_interval (hp₂ : p ≠ 2) (a : ℤ)
    (ha : padicValInt p a = 1) (n r : ℕ) (hr : r ≤ n) {u : ℝ}
    (hu0 : (r : ℝ) < u) (hu1 : u ≤ (r : ℝ) + 1) :
    finiteUpperAffineGroup hp₂ (irreducible_integerParameter p a ha) n u =
      finiteAffineSubgroup p (n + 1) (radicalTranslationDepth p (n + 1) u)
        (finiteUnitSubgroup p (n + 1) (r + 1)) :=
  finiteUpperAffine_eq_interval hp₂ (irreducible_integerParameter p a ha) n r hr hu0 hu1

/-- The corrected original Herbrand table for the literal integer parameter
a with v_p(a)=1, including the final break of every positive finite layer. -/
theorem inverseHerbrandFunction_falseTate_integerParameter (hp₂ : p ≠ 2) (a : ℤ)
    (ha : padicValInt p a = 1) (n i : ℕ) (hi : i ≤ n) :
    let D := falseTateLayer p (a : Qp) (n + 1) (n + 1)
    let ψ := inverseHerbrandFunction (R := spectralIntegerRing Qp D) (D ≃ₐ[Qp] D)
    ψ ((i : ℝ) + 1 / ((p : ℝ) - 1)) =
        (2 * (p : ℝ) ^ (2 * i) + (p : ℝ) - 1) / ((p : ℝ) + 1) ∧
      ψ ((i : ℝ) + 1) =
        ((p : ℝ) - 1) * ((p : ℝ) ^ (2 * i + 1) + 1) / ((p : ℝ) + 1) ∧
      ψ ((n : ℝ) + 1 + 1 / ((p : ℝ) - 1)) =
        ((p : ℝ) ^ (2 * (n + 1)) + (p : ℝ) ^ (2 * n) + (p : ℝ) - 1) /
          ((p : ℝ) + 1) := by
  exact ⟨inverseHerbrandFunction_falseTate_fractional hp₂
    (irreducible_integerParameter p a ha) n i hi,
    inverseHerbrandFunction_falseTate_integer hp₂ (irreducible_integerParameter p a ha) n i hi,
    inverseHerbrandFunction_falseTate_final hp₂ (irreducible_integerParameter p a ha) n⟩

end IntegerParameter

end FalseTateExtension
