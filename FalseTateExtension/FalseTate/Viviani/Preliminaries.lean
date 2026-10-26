/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FalseTateExtension.FalseTate.TotalRamification
public import FalseTateExtension.Kummer.APF
public import FontaineWintenberger.APF.Finite.ConstantIndex
public import FontaineWintenberger.Ramification.Herbrand.Interval
public import FontaineWintenberger.Ramification.Upper.Transport
public import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# Preliminaries for Viviani's filtration

Over `ℚ_p` the upper ramification breaks of `ℚ_p(π^{1/p^∞})/ℚ_p` are `u_j = j + 1/(p-1)`,
`j ≥ 1`, and the APF index of `ℚ_p(π^{1/p^n})/ℚ_p` at `u ≥ 0` is `p^d`, where
`d = radicalTranslationDepth p n u` is the number of breaks `u_1, …, u_n` below `u`: `d = min(n, j)`
for `u_j < u ≤ u_{j+1}`, so `d = i - 1` at `u = u_i` and `d = i` at `u = i + 1`.

In the affine group `G = ℤ/p^n ⋊ (ℤ/p^n)ˣ` with `p ≠ 2`, the commutator of `(0, 2)` with `(a, u)`
is `(a, 1)`, so a normal subgroup `N` containing `(a, u)` contains `(a, 1)` and `(0, u)`; hence
`N = (N ∩ T) ⋊ ρ(N)` with `T = ℤ/p^n ⋊ 1` the translations and `ρ : G → (ℤ/p^n)ˣ` the projection,
and `(G : N) = ((ℤ/p^n)ˣ : ρ(N)) (ℤ/p^n : N ∩ T)`. The subgroups of `G` appearing in the
ramification filtration of `ℚ_p(π^{1/p^n}, ζ_{p^n})/ℚ_p` are `p^k ℤ/p^n ⋊ V` for a subgroup `V` of
principal units `1 + p^r ℤ/p^n`.

## Main results

* `radicalTranslationDepth`, `radicalLayer_apfIndex_eq_pow_translationDepth`: the number `d` of
  breaks `u_j < u`, `1 ≤ j ≤ n`, and `apfIndex ℚ_p ℚ_p(π^{1/p^n}) u = p^d` for `u ≥ 0`.
* `radicalTranslationDepth_interval`: `d = min(n, j)` for `u_j < u ≤ u_{j+1}`.
* `finiteTranslationSubgroup`, `finiteUnitSubgroup`, `finiteAffineSubgroup`: the subgroups
  `p^k ℤ/p^n`, `1 + p^r ℤ/p^n` and `p^k ℤ/p^n ⋊ V`.
* `finiteAffine_commutator_two`: `[(0, 2), (a, u)] = (a, 1)` for `p ≠ 2`.
* `mem_finiteAffine_normal_iff`: `(a, u) ∈ N ↔ (a, 1) ∈ N ∧ u ∈ ρ(N)` for `N` normal, `p ≠ 2`.
* `finiteAffine_normal_index`: `(G : N) = ((ℤ/p^n)ˣ : ρ(N)) (ℤ/p^n : N ∩ T)` for `N` normal.

## References

* [Viviani, *Ramification groups and Artin conductors of radical extensions of
  ℚ*](https://doi.org/10.5802/jtnb.470), §6.
* [Wintenberger, *Le corps des normes de certaines extensions infinies de corps locaux;
  applications*](https://doi.org/10.24033/asens.1440), §1.2.
-/

@[expose] public section

noncomputable section

namespace FalseTateExtension

open IsDiscreteValuationRing FontaineWintenberger

variable (p : ℕ) [Fact p.Prime]

/-- `v_p(p) = 1` in `𝒪[ℚ_p] = ℤ_p`. -/
theorem addVal_padicUnitBall_p : addVal 𝒪[ℚ_[p]] (p : 𝒪[ℚ_[p]]) = 1 := by
  apply addVal_uniformizer
  have h := (MulEquiv.irreducible_iff (f := (padicValuationSubringEquiv p).symm)).mpr
    PadicInt.irreducible_p
  simpa only [map_natCast] using h

/-- The upper ramification breaks of `ℚ_p(π^{1/p^∞})/ℚ_p` are `u_r = r + 1/(p-1)`. -/
theorem radicalUpperBreak_padic (r : ℕ) :
    radicalUpperBreak (K := ℚ_[p]) p r = (r : ℝ) + 1 / ((p : ℝ) - 1) := by
  simp [radicalUpperBreak, absoluteRamificationIdx, addVal_padicUnitBall_p]

/-- The number of breaks `u_j = j + 1/(p-1)`, `1 ≤ j ≤ n`, of `ℚ_p(π^{1/p^∞})/ℚ_p` lying below
`u`. -/
def radicalTranslationDepth (n : ℕ) (u : ℝ) : ℕ :=
  ((Finset.range n).filter (fun r : ℕ => (r : ℝ) + 1 + 1 / ((p : ℝ) - 1) < u)).card

omit [Fact p.Prime] in
/-- No break of `ℚ_p(π^{1/p^0})` lies below any `u`. -/
theorem radicalTranslationDepth_zero (u : ℝ) : radicalTranslationDepth p 0 u = 0 := by
  simp [radicalTranslationDepth]

omit [Fact p.Prime] in
/-- At most `n` of the breaks `u_1, …, u_n` lie below `u`. -/
theorem radicalTranslationDepth_le (n : ℕ) (u : ℝ) :
    radicalTranslationDepth p n u ≤ n := by
  exact (Finset.card_filter_le ..).trans_eq (Finset.card_range n)

omit [Fact p.Prime] in
/-- The number of breaks `u_1, …, u_{n+1}` below `u` is the number of breaks `u_1, …, u_n` below
`u`, plus one if `u_{n+1} = n + 1 + 1/(p-1) < u`. -/
theorem radicalTranslationDepth_succ (n : ℕ) (u : ℝ) :
    radicalTranslationDepth p (n + 1) u = radicalTranslationDepth p n u +
      if u ≤ (n + 1 : ℝ) + 1 / ((p : ℝ) - 1) then 0 else 1 := by
  classical
  simp only [radicalTranslationDepth, Finset.range_add_one, Finset.filter_insert]
  by_cases h : u ≤ (n + 1 : ℝ) + 1 / ((p : ℝ) - 1)
  · rw [ite_eq_right (not_lt.mpr h), ite_eq_left h, Nat.add_zero]
  · rw [ite_eq_left (lt_of_not_ge h), ite_eq_right h, Finset.card_insert_of_notMem]
    exact fun hn => Nat.lt_irrefl n (Finset.mem_range.mp (Finset.mem_filter.mp hn).1)

/-- The APF index of `ℚ_p(π^{1/p^n})/ℚ_p` at `u ≥ 0` is `p^d`, where `d` is the number of breaks
`u_1, …, u_n` below `u`. -/
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
/-- For `j + 1/(p-1) < u ≤ j + 1 + 1/(p-1)`, exactly `min(n, j)` of the breaks `u_1, …, u_n` lie
below `u`. -/
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
/-- For `u ≤ 1 + 1/(p-1)` no break lies below `u`. -/
theorem radicalTranslationDepth_initial (n : ℕ) {u : ℝ}
    (hu : u ≤ 1 + 1 / ((p : ℝ) - 1)) : radicalTranslationDepth p n u = 0 := by
  classical
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro r hr
  have h := (Finset.mem_filter.mp hr).2
  linarith [Nat.cast_nonneg (α := ℝ) r]

omit [Fact p.Prime] in
/-- For `u > n + 1/(p-1)` all `n` breaks `u_1, …, u_n` lie below `u`. -/
theorem radicalTranslationDepth_tail (n : ℕ) {u : ℝ}
    (hu : (n : ℝ) + 1 / ((p : ℝ) - 1) < u) :
    radicalTranslationDepth p n u = n := by
  classical
  rw [radicalTranslationDepth, Finset.filter_eq_self.mpr, Finset.card_range]
  intro r hr
  have hr' : (r : ℝ) + 1 ≤ n := by
    exact_mod_cast (Nat.succ_le_of_lt (Finset.mem_range.mp hr))
  linarith

/-- `0 < 1/(p-1) < 1` for `p ≠ 2`. -/
theorem viviani_fraction_pos_lt_one [hp₂ : Fact (p ≠ 2)] :
    0 < 1 / ((p : ℝ) - 1) ∧ 1 / ((p : ℝ) - 1) < 1 := by
  have hp : 2 < p := lt_of_le_of_ne (Fact.out : p.Prime).two_le (Ne.symm hp₂.out)
  have hp' : (2 : ℝ) < p := by exact_mod_cast hp
  constructor
  · exact div_pos zero_lt_one (by linarith)
  · exact (div_lt_one (by linarith)).mpr (by linarith)

omit [Fact p.Prime] in
/-- For `1 ≤ i ≤ n`, exactly `i - 1` of the breaks `u_1, …, u_n` lie below `u_i = i + 1/(p-1)`. -/
theorem radicalTranslationDepth_fractional (n i : ℕ) (hi : 1 ≤ i) (hin : i ≤ n) :
    radicalTranslationDepth p n ((i : ℝ) + 1 / ((p : ℝ) - 1)) = i - 1 := by
  have hi' : (i - 1 : ℕ) + 1 = i := Nat.sub_add_cancel hi
  have hc : ((i - 1 : ℕ) : ℝ) + 1 = i := by exact_mod_cast hi'
  rw [radicalTranslationDepth_interval p n (i - 1) (by linarith) (by linarith),
    Nat.min_eq_right (by omega : i - 1 ≤ n)]

/-- For `p ≠ 2` and `i ≤ n`, exactly `i` of the breaks `u_1, …, u_n` lie below `i + 1`. -/
theorem radicalTranslationDepth_integer [hp₂ : Fact (p ≠ 2)] (n i : ℕ) (hin : i ≤ n) :
    radicalTranslationDepth p n ((i : ℝ) + 1) = i := by
  have hδ := viviani_fraction_pos_lt_one p
  rw [radicalTranslationDepth_interval p n i (by linarith) (by linarith), Nat.min_eq_right hin]

/-- The subgroup `p^k ℤ/p^n` of the additive group `ℤ/p^n`. -/
def finiteTranslationSubgroup (n k : ℕ) : Subgroup (Multiplicative (ZMod (p ^ n))) :=
  (powMonoidHom (p ^ k) : Multiplicative (ZMod (p ^ n)) →* _).range

/-- `(ℤ/p^n : p^k ℤ/p^n) = p^k` for `k ≤ n`. -/
theorem finiteTranslationSubgroup_index (n k : ℕ) (hk : k ≤ n) :
    (finiteTranslationSubgroup p n k).index = p ^ k := by
  have : NeZero (p ^ n) := ⟨pow_ne_zero n (Fact.out : p.Prime).ne_zero⟩
  rw [finiteTranslationSubgroup, IsCyclic.index_powMonoidHom_range]
  simp only [Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card]
  exact Nat.gcd_eq_right (Nat.pow_dvd_pow p hk)

omit [Fact p.Prime] in
/-- `p^0 ℤ/p^n = ℤ/p^n`. -/
theorem finiteTranslationSubgroup_zero (n : ℕ) : finiteTranslationSubgroup p n 0 = ⊤ := by
  ext b
  simp only [Subgroup.mem_top, iff_true]
  exact ⟨b, by simp [powMonoidHom]⟩

omit [Fact p.Prime] in
/-- `p^n ℤ/p^n = 0`. -/
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

/-- The principal units `1 + p^r ℤ/p^n = ker((ℤ/p^n)ˣ → (ℤ/p^r)ˣ)` for `r ≤ n`; for `r ≥ n` the
trivial group. -/
def finiteUnitSubgroup (n r : ℕ) : Subgroup (ZMod (p ^ n))ˣ :=
  (ZMod.unitsMap (pow_dvd_pow p (Nat.min_le_right r n))).ker

omit [Fact p.Prime] in
/-- For `r ≤ n`, `finiteUnitSubgroup p n r = ker((ℤ/p^n)ˣ → (ℤ/p^r)ˣ)`. -/
theorem finiteUnitSubgroup_eq_kernel (n r : ℕ) (hr : r ≤ n) :
    finiteUnitSubgroup p n r = (ZMod.unitsMap (pow_dvd_pow p hr)).ker := by
  let f : {j : ℕ // j ≤ n} → Subgroup (ZMod (p ^ n))ˣ :=
    fun j => (ZMod.unitsMap (pow_dvd_pow p j.property)).ker
  exact congrArg f (show (⟨min r n, Nat.min_le_right r n⟩ : {j : ℕ // j ≤ n}) =
    ⟨r, hr⟩ from Subtype.ext (Nat.min_eq_left hr))

omit [Fact p.Prime] in
/-- For `r ≥ n`, `finiteUnitSubgroup p n r` is trivial. -/
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
/-- `p^k ℤ/p^n` is stable under multiplication by every unit of `ℤ/p^n`. -/
theorem finiteTranslationSubgroup_action (n k : ℕ) (u : (ZMod (p ^ n))ˣ)
    {b : Multiplicative (ZMod (p ^ n))} (hb : b ∈ finiteTranslationSubgroup p n k) :
    finiteAffineAction p n u b ∈ finiteTranslationSubgroup p n k := by
  obtain ⟨a, ha⟩ := hb
  refine ⟨finiteAffineAction p n u a, ?_⟩
  change a ^ (p ^ k) = b at ha
  change (finiteAffineAction p n u a) ^ (p ^ k) = finiteAffineAction p n u b
  rw [← map_pow, ha]

/-- The subgroup `p^k ℤ/p^n ⋊ V` of `ℤ/p^n ⋊ (ℤ/p^n)ˣ`, for a subgroup `V ≤ (ℤ/p^n)ˣ`. -/
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
/-- `ℤ/p^n ⋊ 1` is the group of translations of `ℤ/p^n ⋊ (ℤ/p^n)ˣ`. -/
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
/-- `p^n ℤ/p^n ⋊ 1` is the trivial subgroup of `ℤ/p^n ⋊ (ℤ/p^n)ˣ`. -/
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

/-- `[(0, 2), (a, u)] = (a, 1)` in `ℤ/p^n ⋊ (ℤ/p^n)ˣ`, `p ≠ 2`. -/
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

/-- A normal subgroup of `ℤ/p^n ⋊ (ℤ/p^n)ˣ`, `p ≠ 2`, containing `(a, u)` contains `(a, 1)`. -/
theorem finiteAffine_normal_inl_left [hp₂ : Fact (p ≠ 2)]
    (N : Subgroup (FullFiniteAffineGroup p n)) [N.Normal]
    {g : FullFiniteAffineGroup p n} (hg : g ∈ N) :
    SemidirectProduct.inl g.left ∈ N := by
  rw [← finiteAffine_commutator_two n g, commutatorElement_def]
  exact N.mul_mem ((inferInstance : N.Normal).conj_mem g hg _) (N.inv_mem hg)

/-- A normal subgroup of `ℤ/p^n ⋊ (ℤ/p^n)ˣ`, `p ≠ 2`, containing `(a, u)` contains `(0, u)`. -/
theorem finiteAffine_normal_inr_right [hp₂ : Fact (p ≠ 2)]
    (N : Subgroup (FullFiniteAffineGroup p n)) [N.Normal]
    {g : FullFiniteAffineGroup p n} (hg : g ∈ N) :
    SemidirectProduct.inr g.right ∈ N := by
  have he : (SemidirectProduct.inl g.left : FullFiniteAffineGroup p n)⁻¹ * g =
      SemidirectProduct.inr g.right := by
    apply SemidirectProduct.ext <;> simp
  rw [← he]
  exact N.mul_mem (N.inv_mem (finiteAffine_normal_inl_left n N hg)) hg

/-- For a normal subgroup `N` of `ℤ/p^n ⋊ (ℤ/p^n)ˣ`, `p ≠ 2`: `(a, u) ∈ N` if and only if
`(a, 1) ∈ N` and `u` is the unit coordinate of some element of `N`. -/
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

/-- For a normal subgroup `N` of `ℤ/p^n ⋊ (ℤ/p^n)ˣ`, `p ≠ 2`: `(a, u) ∈ (0 ⋊ (ℤ/p^n)ˣ) N` if and
only if `(a, 1) ∈ N`. -/
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

/-- For a normal subgroup `N` of `G = ℤ/p^n ⋊ (ℤ/p^n)ˣ`, `p ≠ 2`:
`(G : (0 ⋊ (ℤ/p^n)ˣ) N) = (ℤ/p^n : N ∩ (ℤ/p^n ⋊ 1))`. -/
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
/-- For a normal subgroup `N` of `G = ℤ/p^n ⋊ (ℤ/p^n)ˣ` with image `ρ(N)` in `(ℤ/p^n)ˣ`:
`(G : N) = ((ℤ/p^n)ˣ : ρ(N)) (ℤ/p^n : N ∩ (ℤ/p^n ⋊ 1))`. -/
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
