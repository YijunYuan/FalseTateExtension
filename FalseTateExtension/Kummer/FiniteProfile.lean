/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FalseTateExtension.Kummer.Breaks
public import FalseTateExtension.Kummer.Eisenstein
public import FalseTateExtension.Kummer.StepProfile
public import FontaineWintenberger.APF.BaseChange.Basic
public import FontaineWintenberger.APF.Elementary.PrimeDegree
public import FontaineWintenberger.APF.Galois.Union
public import FontaineWintenberger.APF.Strict
public import FontaineWintenberger.APF.Tower.TotallyRamified

/-!
# The APF profile of the finite radical layers

The APF index and inverse Herbrand function of `K(π^{1/p^n})/K` are computed at every real parameter
by induction on `n`, together with the first ramification bound of one step.
-/

@[expose] public section

noncomputable section

namespace FalseTateExtension

open FontaineWintenberger IsDiscreteValuationRing

section FiniteProfiles

variable {K : Type*} [NontriviallyNormedField K] [IsCompleteDiscreteValuedField K]
    [PerfectField (𝓀[K])] [CharZero K]
variable (p : ℕ) [Fact p.Prime]
variable (π : 𝒪[K])

/-- Each finite radical Herbrand function is affine after its
last base threshold, with its degree as slope. -/
theorem radicalLayer_apfPsi_tail [hπ : Fact (Irreducible π)] (n : ℕ) (u : ℝ)
    (hu : radicalUpperBreak (K := K) p n ≤ u) :
    apfPsi K (radicalLayer p (π : K) n) u =
      (p : ℝ) ^ n * (absoluteRamificationIdx p K : ℝ) / ((p : ℝ) - 1) +
        (p : ℝ) ^ n * (u - radicalUpperBreak (K := K) p n) := by
  induction n generalizing u with
  | zero =>
    rw [radicalLayer_zero, apfPsi_algEquiv K _ (IntermediateField.botEquiv K _),
      apfPsi_eq_self_of_bound_eq_top K K (apfRamificationBound_self K)]
    simp only [pow_zero, one_mul, radicalUpperBreak, Nat.cast_zero, zero_add]
    ring
  | succ n ih =>
    have hmono : radicalUpperBreak (K := K) p n ≤
        radicalUpperBreak (K := K) p (n + 1) := by
      rw [radicalUpperBreak_succ]
      exact le_add_of_nonneg_right (Nat.cast_nonneg _)
    have hψb : apfPsi K (radicalLayer p (π : K) n)
        (radicalUpperBreak (K := K) p (n + 1)) = radicalRelativeBreak (K := K) p n := by
      rw [ih _ hmono, radicalRelativeBreak_eq_affine]
    have hψu := ih u (hmono.trans hu)
    by_cases hub : u ≤ radicalUpperBreak (K := K) p (n + 1)
    · have hueq := hub.antisymm hu
      subst u
      rw [radicalLayer_apfPsi_succ p π n]
      change (if apfPsi K (radicalLayer p (π : K) n) (radicalUpperBreak (K := K) p (n + 1)) ≤
          radicalRelativeBreak (K := K) p n then _ else _) = _
      rw [hψb]
      rw [ite_eq_left le_rfl, sub_self, mul_zero, add_zero]
      rfl
    · have hψgt : ¬ apfPsi K (radicalLayer p (π : K) n) u ≤
          radicalRelativeBreak (K := K) p n := by
        rw [← hψb]
        exact not_le.mpr ((IsAPF.strictMono_apfPsi K _)
          (lt_of_not_ge hub))
      rw [radicalLayer_apfPsi_succ p π n]
      change (if apfPsi K (radicalLayer p (π : K) n) u ≤
          radicalRelativeBreak (K := K) p n then _ else _) = _
      rw [ite_eq_right hψgt, hψu]
      rw [radicalUpperBreak_succ]
      rw [pow_succ]
      have hp : (p : ℝ) - 1 ≠ 0 := by
        have : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
        linarith
      field_simp
      ring

/-- The next relative break is attained at the next base threshold. -/
theorem radicalLayer_apfPsi_next_break [hπ : Fact (Irreducible π)] (n : ℕ) :
    apfPsi K (radicalLayer p (π : K) n) (radicalUpperBreak (K := K) p (n + 1)) =
      radicalRelativeBreak (K := K) p n := by
  rw [radicalLayer_apfPsi_tail p π n _ (by
    rw [radicalUpperBreak_succ]
    exact le_add_of_nonneg_right (Nat.cast_nonneg _)), radicalRelativeBreak_eq_affine]

/-- The new index factor changes precisely at the next threshold
in the normalization of the base field. -/
theorem radicalLayer_apfIndex_succ_threshold [hπ : Fact (Irreducible π)] (n : ℕ)
    {u : ℝ} (hu : 0 ≤ u) :
    apfIndex K (radicalLayer p (π : K) (n + 1)) u =
      apfIndex K (radicalLayer p (π : K) n) u *
        if u ≤ radicalUpperBreak (K := K) p (n + 1) then 1 else p := by
  have hiff : apfPsi K (radicalLayer p (π : K) n) u ≤ radicalRelativeBreak (K := K) p n ↔
      u ≤ radicalUpperBreak (K := K) p (n + 1) := by
    rw [← radicalLayer_apfPsi_next_break p π n]
    exact (IsAPF.strictMono_apfPsi K _).le_iff_le
  rw [radicalLayer_apfIndex_succ p π n hu]
  dsimp only [radicalRelativeBreak] at hiff
  by_cases h : u ≤ radicalUpperBreak (K := K) p (n + 1)
  · rw [ite_eq_left (hiff.mpr h), ite_eq_left h]
  · rw [ite_eq_right (fun hψ => h (hiff.mp hψ)), ite_eq_right h]

/-- After its last threshold, the finite radical index is its degree. -/
theorem radicalLayer_apfIndex_tail [hπ : Fact (Irreducible π)] (n : ℕ) {u : ℝ}
    (hu : radicalUpperBreak (K := K) p n < u) :
    apfIndex K (radicalLayer p (π : K) n) u = p ^ n := by
  induction n with
  | zero =>
    rw [radicalLayer_zero, apfIndex_algEquiv K _ (IntermediateField.botEquiv K _),
      apfIndex_eq_one_of_bound_eq_top K K (apfRamificationBound_self K)
        ((radicalUpperBreak_nonneg p 0).trans hu.le), pow_zero]
  | succ n ih =>
    rw [radicalLayer_apfIndex_succ_threshold p π n
      ((radicalUpperBreak_nonneg p (n + 1)).trans hu.le), ite_eq_right (not_le.mpr hu),
      ih ((radicalUpperBreak_mono p (Nat.le_succ n)).trans_lt hu), pow_succ]

/-- A fixed upper parameter stops changing once its next threshold is reached. -/
theorem radicalLayer_apfIndex_stable [hπ : Fact (Irreducible π)] {n m : ℕ} (hnm : n ≤ m)
    {u : ℝ} (hu : 0 ≤ u) (hb : u ≤ radicalUpperBreak (K := K) p (n + 1)) :
    apfIndex K (radicalLayer p (π : K) m) u =
      apfIndex K (radicalLayer p (π : K) n) u := by
  induction m, hnm using Nat.le_induction with
  | base => rfl
  | succ m hnm ih =>
    rw [radicalLayer_apfIndex_succ_threshold p π m hu,
      ite_eq_left (hb.trans (radicalUpperBreak_mono p (Nat.add_le_add_right hnm 1))),
      mul_one, ih]

/-- The full finite radical profile on every interval between consecutive
thresholds, including the right endpoint and finite-level truncation. -/
theorem radicalLayer_apfIndex_interval [hπ : Fact (Irreducible π)] (n j : ℕ) {u : ℝ}
    (hlo : radicalUpperBreak (K := K) p j < u)
    (hhi : u ≤ radicalUpperBreak (K := K) p (j + 1)) :
    apfIndex K (radicalLayer p (π : K) n) u = p ^ min n j := by
  by_cases h : j ≤ n
  · rw [radicalLayer_apfIndex_stable p π h
      ((radicalUpperBreak_nonneg p j).trans hlo.le) hhi,
      radicalLayer_apfIndex_tail p π j hlo, min_eq_right h]
  · rw [radicalLayer_apfIndex_tail p π n
      ((radicalUpperBreak_mono p (le_of_not_ge h)).trans_lt hlo),
      min_eq_left (le_of_not_ge h)]

/-- The finite radical index stays one through the first threshold. -/
theorem radicalLayer_apfIndex_initial [hπ : Fact (Irreducible π)] (n : ℕ) {u : ℝ}
    (hu : 0 ≤ u) (hb : u ≤ radicalUpperBreak (K := K) p 1) :
    apfIndex K (radicalLayer p (π : K) n) u = 1 := by
  rw [radicalLayer_apfIndex_stable p π (Nat.zero_le n) hu hb,
    radicalLayer_zero, apfIndex_algEquiv K _ (IntermediateField.botEquiv K _),
    apfIndex_eq_one_of_bound_eq_top K K (apfRamificationBound_self K) hu]

/-- Shifting the upper parameter by the base valuation of `p`
crosses at most one jump, uniformly in the finite radical layer. -/
theorem radicalLayer_apfIndex_growth [hπ : Fact (Irreducible π)] (n : ℕ) {u : ℝ} (hu : 0 ≤ u) :
    apfIndex K (radicalLayer p (π : K) n) (u + absoluteRamificationIdx p K) ≤
      p * apfIndex K (radicalLayer p (π : K) n) u := by
  have hu' : 0 ≤ u + (absoluteRamificationIdx p K : ℝ) := add_nonneg hu (Nat.cast_nonneg _)
  induction n with
  | zero =>
    rw [radicalLayer_zero,
      apfIndex_algEquiv K _ (IntermediateField.botEquiv K _) (u + absoluteRamificationIdx p K),
      apfIndex_algEquiv K _ (IntermediateField.botEquiv K _) u,
      apfIndex_eq_one_of_bound_eq_top K K (apfRamificationBound_self K) hu',
      apfIndex_eq_one_of_bound_eq_top K K (apfRamificationBound_self K) hu, mul_one]
    exact (Fact.out : p.Prime).one_lt.le
  | succ n ih =>
    rw [radicalLayer_apfIndex_succ_threshold p π n hu',
      radicalLayer_apfIndex_succ_threshold p π n hu]
    by_cases hshift : u + absoluteRamificationIdx p K ≤ radicalUpperBreak (K := K) p (n + 1)
    · have h : u ≤ radicalUpperBreak (K := K) p (n + 1) :=
        (le_add_of_nonneg_right (Nat.cast_nonneg _)).trans hshift
      rw [ite_eq_left hshift, ite_eq_left h, mul_one, mul_one]
      exact ih
    · by_cases h : u ≤ radicalUpperBreak (K := K) p (n + 1)
      · have hlo : radicalUpperBreak (K := K) p n < u := by
          rw [radicalUpperBreak_succ] at hshift
          linarith
        rw [ite_eq_right hshift, ite_eq_left h, mul_one,
          radicalLayer_apfIndex_tail p π n hlo,
          radicalLayer_apfIndex_tail p π n
            (hlo.trans_le (le_add_of_nonneg_right (Nat.cast_nonneg _))), mul_comm]
      · rw [ite_eq_right hshift, ite_eq_right h]
        calc
          _ ≤ (p * apfIndex K (radicalLayer p (π : K) n) u) * p :=
            Nat.mul_le_mul_right p ih
          _ = _ := by ring

end FiniteProfiles

section PrimeStepFirstBound

variable {K : Type*} [NontriviallyNormedField K] [IsCompleteDiscreteValuedField K]
    [PerfectField (𝓀[K])] [CharZero K]
variable (p : ℕ) [Fact p.Prime]
variable (π : 𝒪[K])

attribute [local instance] kummerBaseNormedField kummerBaseNormedAlgebra kummerBaseUltrametric
  kummerBaseComplete kummerBaseDVR kummerBaseCompleteDiscreteValuedField kummerBasePerfect
  kummerStepAlgebra kummerStepScalarTower
  kummerStepFinite kummerStepValuation kummerStepOwnValuation

/-- The extended first bound of the consecutive radical
step equals the break determined by its different, without normality. -/
theorem radicalLayer_step_apfRamificationBound [hπ : Fact (Irreducible π)] (n : ℕ) :
    apfRamificationBound (radicalLayer p (π : K) n) (radicalLayer p (π : K) (n + 1)) =
      (((p : ℝ) ^ (n + 1) * (addVal 𝒪[K] (p : 𝒪[K])).toNat / ((p : ℝ) - 1) : ℝ) : EReal) := by
  let E := radicalLayer p (π : K) n
  let F := radicalLayer p (π : K) (n + 1)
  let t : ℝ := (p : ℝ) ^ (n + 1) * (addVal 𝒪[K] (p : 𝒪[K])).toNat / ((p : ℝ) - 1)
  let j : F →ₐ[E] SeparableClosure E := IsSepClosed.lift
  have ht : 0 ≤ t := div_nonneg
    (mul_nonneg (pow_nonneg (Nat.cast_nonneg p) _) (Nat.cast_nonneg _)) (by
      have : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
      linarith)
  have he : (IsLocalRing.maximalIdeal (spectralIntegerRing E F)).ramificationIdx
      𝒪[E] = Module.finrank E F := by
    rw [radicalLayer_step_own_ramificationIdx p π n, radicalLayer_step_finrank p π n]
  have hiff (u : ℝ) (hu : 0 ≤ u) : apfSubgroup E j.fieldRange u = ⊤ ↔ u ≤ t := by
    rw [← Subgroup.index_eq_one,
      apfSubgroup_fieldRange_index_eq_apfIndex_of_ramificationIdx_eq_finrank E F j he hu,
      radicalLayer_step_apfIndex p π n hu]
    change (if u ≤ t then 1 else p) = 1 ↔ u ≤ t
    split_ifs with h
    · simp [h]
    · simp [h, (Fact.out : p.Prime).ne_one]
  apply le_antisymm
  · rw [apfRamificationBound_eq_embedding E F j]
    apply sSup_le
    rintro x ⟨u, _hu, htop, rfl⟩
    apply EReal.coe_le_coe_iff.mpr
    by_cases hu : 0 ≤ u
    · exact (hiff u hu).mp htop
    · exact (le_of_not_ge hu).trans ht
  · exact le_apfRamificationBound E F j (by linarith : -1 ≤ t) ((hiff t ht).mpr le_rfl)

end PrimeStepFirstBound

end FalseTateExtension
end
