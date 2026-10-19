/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FalseTateExtension.RadicalRamification
public import FontaineWintenberger.APF.Elementary.PrimeDegree
public import FontaineWintenberger.APF.BaseChange.Basic
public import FontaineWintenberger.APF.Strict
public import FontaineWintenberger.APF.Galois.Union
public import FontaineWintenberger.APF.Tower.TotallyRamified

/-!
# Intrinsic APF profiles in the actual radical tower

The actual relative different determines each prime-step profile. Composing
the true finite-base Herbrand functions places its breaks over the original
base field and gives the stabilized profile of the infinite radical tower.
-/

@[expose] public section

noncomputable section

namespace FalseTateExtension

open FontaineWintenberger IsDiscreteValuationRing

section PrimeStep

variable {K : Type*} [NontriviallyNormedField K] [IsCompleteDiscreteValuedField K]
    [PerfectField (𝓀[K])] [CharZero K]
variable (p : ℕ) [Fact p.Prime]
variable (π : 𝒪[K])
    [hπ : Fact (Irreducible π)] (n : ℕ)

local notation "F₀" => radicalLayer (K := K) p (π : K) n
local notation "F₁" => radicalLayer (K := K) p (π : K) (n + 1)
local notation "O₀" => spectralIntegerRing K F₀
local notation "O₁" => spectralIntegerRing K F₁

noncomputable local instance kummerBaseNormedField : NontriviallyNormedField F₀ :=
  spectralNorm.nontriviallyNormedField K F₀
noncomputable local instance kummerBaseNormedAlgebra : NormedAlgebra K F₀ :=
  spectralNorm.normedAlgebra K F₀
local instance kummerBaseUltrametric : IsUltrametricDist F₀ :=
  IsUltrametricDist.isUltrametricDist_iff_isNonarchimedean_norm.mpr
    (isNonarchimedean_spectralNorm (K := K) (L := F₀))
local instance kummerBaseComplete : CompleteSpace F₀ := spectralNorm.completeSpace K F₀
local instance kummerBaseDVR : IsDiscreteValuationRing
    (NormedField.valuation (K := F₀)).valuationSubring :=
  normedAlgebra_unitBall_isDiscreteValuationRing K F₀
local instance kummerBaseCompleteDiscreteValuedField : IsCompleteDiscreteValuedField F₀ where
local instance kummerBasePerfect : PerfectField (IsLocalRing.ResidueField
    (NormedField.valuation (K := F₀)).valuationSubring) :=
  Algebra.IsAlgebraic.perfectField (𝓀[K])
local instance kummerStepAlgebra : Algebra F₀ F₁ :=
  (IntermediateField.inclusion (radicalLayer_le_succ p (π : K) n)).toRingHom.toAlgebra
local instance kummerStepScalarTower : IsScalarTower K F₀ F₁ :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl
local instance kummerStepFinite : FiniteDimensional F₀ F₁ :=
  Module.Finite.right K F₀ F₁
local instance kummerStepValuation :
    (spectralValuation K F₀).HasExtension (spectralValuation K F₁) :=
  spectralValuation_hasExtension_tower K (E := F₀) (L := F₁)
local instance kummerStepOwnValuation :
    (NormedField.valuation (K := F₀)).HasExtension (spectralValuation K F₁) where
  val_isEquiv_comap := by
    intro x y
    change spectralNorm K F₀ x ≤ spectralNorm K F₀ y ↔
      spectralNorm K F₁ (algebraMap F₀ F₁ x) ≤ spectralNorm K F₁ (algebraMap F₀ F₁ y)
    rw [← spectralNorm.eq_of_tower x, ← spectralNorm.eq_of_tower y]

include hπ n

omit [PerfectField (𝓀[K])] in
/-- On its own actual spectral integers, a consecutive radical step has
canonical ramification index `p`. -/
theorem radicalLayer_step_own_ramificationIdx :
    (IsLocalRing.maximalIdeal (spectralIntegerRing F₀ F₁)).ramificationIdx
      (NormedField.valuation (K := F₀)).valuationSubring = p := by
  have h := extensionValuationSubring_ramificationIdx_eq_spectral F₀ F₁
    (spectralValuation K F₁)
  change (IsLocalRing.maximalIdeal O₁).ramificationIdx O₀ = _ at h
  rw [← h]
  exact radicalLayer_step_ramificationIdx p π n

/-- The same actual relative different is computed on the own spectral
integer ring of the relative base field. -/
theorem radicalLayer_step_own_different_order :
    (emultiplicity (IsLocalRing.maximalIdeal (spectralIntegerRing F₀ F₁))
      (differentIdeal (NormedField.valuation (K := F₀)).valuationSubring
        (spectralIntegerRing F₀ F₁))).toNat =
      p ^ (n + 1) * (addVal 𝒪[K] (p : 𝒪[K])).toNat + (p - 1) := by
  have h := extensionValuationSubring_different_order_eq_spectral F₀ F₁
    (spectralValuation K F₁)
  change emultiplicity (IsLocalRing.maximalIdeal O₁) (differentIdeal O₀ O₁) = _ at h
  rw [← h]
  exact radicalLayer_step_different_order p π n

/-- The intrinsic upper index of the actual nonnormal prime step has
break `p^(n+1) v_K(p)/(p-1)`, with its right endpoint included. -/
theorem radicalLayer_step_apfIndex {u : ℝ} (hu : 0 ≤ u) :
    apfIndex F₀ F₁ u =
      if u ≤ (p : ℝ) ^ (n + 1) * (addVal 𝒪[K] (p : 𝒪[K])).toNat / ((p : ℝ) - 1)
        then 1 else p := by
  have hn := radicalLayer_step_finrank p π n
  have he : (IsLocalRing.maximalIdeal (spectralIntegerRing F₀ F₁)).ramificationIdx
      (NormedField.valuation (K := F₀)).valuationSubring = Module.finrank F₀ F₁ := by
    rw [radicalLayer_step_own_ramificationIdx p π n, hn]
  have hp : (Module.finrank F₀ F₁).Prime := by rw [hn]; exact Fact.out
  have h := apfIndex_prime_degree_eq_different F₀ F₁ hp he
  dsimp only at h
  rw [radicalLayer_step_own_different_order p π n, hn] at h
  have hp₁ : 1 ≤ p := (Fact.out : p.Prime).one_lt.le
  have hpℝ : (p : ℝ) - 1 ≠ 0 := by
    have : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
    linarith
  have hb : ((p ^ (n + 1) * (addVal 𝒪[K] (p : 𝒪[K])).toNat + (p - 1) : ℕ) : ℝ) /
      ((p : ℝ) - 1) - 1 =
      (p : ℝ) ^ (n + 1) * (addVal 𝒪[K] (p : 𝒪[K])).toNat / ((p : ℝ) - 1) := by
    push_cast [Nat.cast_sub hp₁]
    field_simp
    ring
  rw [hb] at h
  exact h.2 u hu

/-- The actual inverse Herbrand function of a consecutive radical step,
including its identity continuation for all nonpositive arguments. -/
theorem radicalLayer_step_apfPsi (u : ℝ) :
    let t := (p : ℝ) ^ (n + 1) * (addVal 𝒪[K] (p : 𝒪[K])).toNat / ((p : ℝ) - 1)
    apfPsi F₀ F₁ u = if u ≤ t then u else t + (p : ℝ) * (u - t) := by
  have hpℝ : (0 : ℝ) < (p : ℝ) - 1 := by
    have : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
    linarith
  have ht : 0 ≤ (p : ℝ) ^ (n + 1) * (addVal 𝒪[K] (p : 𝒪[K])).toNat / ((p : ℝ) - 1) :=
    div_nonneg (mul_nonneg (pow_nonneg (Nat.cast_nonneg p) _) (Nat.cast_nonneg _)) hpℝ.le
  have hprofile (v : ℝ) (hv : 0 ≤ v) : apfIndex F₀ F₁ v =
      if v ≤ (p : ℝ) ^ (n + 1) * (addVal 𝒪[K] (p : 𝒪[K])).toNat / ((p : ℝ) - 1)
        then 1 else Module.finrank F₀ F₁ := by
    rw [radicalLayer_step_finrank p π n]
    exact radicalLayer_step_apfIndex p π n hv
  simpa only [radicalLayer_step_finrank p π n] using
    apfPsi_eq_of_index_profile F₀ F₁ ht hprofile u

end PrimeStep

section Successor

variable {K : Type*} [NontriviallyNormedField K] [IsCompleteDiscreteValuedField K]
    [PerfectField (𝓀[K])] [CharZero K]
variable (p : ℕ) [Fact p.Prime]
variable (π : 𝒪[K]) (n : ℕ)

attribute [local instance] kummerBaseNormedField kummerBaseNormedAlgebra kummerBaseUltrametric
  kummerBaseComplete kummerBaseDVR kummerBaseCompleteDiscreteValuedField kummerBasePerfect
  kummerStepAlgebra kummerStepScalarTower
  kummerStepFinite kummerStepValuation kummerStepOwnValuation

local notation "F₀" => radicalLayer (K := K) p (π : K) n
local notation "F₁" => radicalLayer (K := K) p (π : K) (n + 1)

/-- The index of the radical layer `n + 1` over `K` is that of the layer `n` times the index of
the step, evaluated at `ψ_n(u)`; the step has index `1` below its break and `p` above it. -/
theorem radicalLayer_apfIndex_succ [hπ : Fact (Irreducible π)]
    {u : ℝ} (hu : 0 ≤ u) :
    apfIndex K F₁ u = apfIndex K F₀ u *
      if apfPsi K F₀ u ≤ (p : ℝ) ^ (n + 1) * absoluteRamificationIdx p K / ((p : ℝ) - 1)
        then 1 else p := by
  rw [apfIndex_eq_mul_finiteBase_of_normedAlgebra K F₀ F₁ hu,
    radicalLayer_step_apfIndex p π n (hu.trans (IsAPF.le_apfPsi K F₀ u))]

/-- The inverse Herbrand function of the radical layer `n + 1` over `K` is obtained from that
of the layer `n` by the step profile. -/
theorem radicalLayer_apfPsi_succ [hπ : Fact (Irreducible π)] (u : ℝ) :
    let t := (p : ℝ) ^ (n + 1) * absoluteRamificationIdx p K / ((p : ℝ) - 1)
    apfPsi K F₁ u =
      if apfPsi K F₀ u ≤ t then apfPsi K F₀ u
        else t + (p : ℝ) * (apfPsi K F₀ u - t) := by
  rw [← IsAPF.apfPsi_finiteBase_comp_of_normedAlgebra K F₀ F₁ u]
  exact radicalLayer_step_apfPsi p π n _

end Successor


section Breaks

variable {K : Type*} [NontriviallyNormedField K] [IsCompleteDiscreteValuedField K]
variable (p : ℕ) [Fact p.Prime]


/-- The original-base upper thresholds; `j=0` is also useful for the
initial affine identity before any nontrivial radical layer. -/
def radicalUpperBreak (j : ℕ) : ℝ :=
  (absoluteRamificationIdx p K : ℝ) * ((j : ℝ) + 1 / ((p : ℝ) - 1))

/-- The actual relative upper break in `F_(n+1)/F_n`. -/
def radicalRelativeBreak (n : ℕ) : ℝ :=
  (p : ℝ) ^ (n + 1) * (absoluteRamificationIdx p K : ℝ) / ((p : ℝ) - 1)

omit [Fact p.Prime] in
private theorem radicalUpperBreak_succ (n : ℕ) :
    radicalUpperBreak (K := K) p (n + 1) =
      radicalUpperBreak (K := K) p n + absoluteRamificationIdx p K := by
  simp only [radicalUpperBreak, Nat.cast_add, Nat.cast_one]
  ring

private theorem radicalRelativeBreak_eq_affine (n : ℕ) :
    radicalRelativeBreak (K := K) p n =
      (p : ℝ) ^ n * (absoluteRamificationIdx p K : ℝ) / ((p : ℝ) - 1) +
        (p : ℝ) ^ n * (radicalUpperBreak (K := K) p (n + 1) -
          radicalUpperBreak (K := K) p n) := by
  have hp : (p : ℝ) - 1 ≠ 0 := by
    have : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
    linarith
  rw [radicalUpperBreak_succ]
  dsimp only [radicalRelativeBreak]
  rw [pow_succ]
  field_simp
  ring

private theorem radicalUpperBreak_nonneg (n : ℕ) : 0 ≤ radicalUpperBreak (K := K) p n := by
  have hp : 0 < (p : ℝ) - 1 := by
    have : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
    linarith
  exact mul_nonneg (Nat.cast_nonneg _) (add_nonneg (Nat.cast_nonneg _)
    (div_nonneg zero_le_one hp.le))

omit [Fact p.Prime] in
private theorem radicalUpperBreak_mono : Monotone (radicalUpperBreak (K := K) p) := by
  apply monotone_nat_of_le_succ
  intro n
  rw [radicalUpperBreak_succ]
  exact le_add_of_nonneg_right (Nat.cast_nonneg _)

end Breaks

section FiniteProfiles

variable {K : Type*} [NontriviallyNormedField K] [IsCompleteDiscreteValuedField K]
    [PerfectField (𝓀[K])] [CharZero K]
variable (p : ℕ) [Fact p.Prime]
variable (π : 𝒪[K])


/-- Each actual finite radical Herbrand function is affine after its
last original-base threshold, with its true degree as slope. -/
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

/-- The next relative break is attained at the next original-base threshold. -/
theorem radicalLayer_apfPsi_next_break [hπ : Fact (Irreducible π)] (n : ℕ) :
    apfPsi K (radicalLayer p (π : K) n) (radicalUpperBreak (K := K) p (n + 1)) =
      radicalRelativeBreak (K := K) p n := by
  rw [radicalLayer_apfPsi_tail p π n _ (by
    rw [radicalUpperBreak_succ]
    exact le_add_of_nonneg_right (Nat.cast_nonneg _)), radicalRelativeBreak_eq_affine]

/-- The actual new index factor changes precisely at the next threshold
in the normalization of the original base field. -/
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

/-- After its last threshold, the actual finite radical index is its degree. -/
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

/-- The actual finite radical index stays one through the first threshold. -/
theorem radicalLayer_apfIndex_initial [hπ : Fact (Irreducible π)] (n : ℕ) {u : ℝ}
    (hu : 0 ≤ u) (hb : u ≤ radicalUpperBreak (K := K) p 1) :
    apfIndex K (radicalLayer p (π : K) n) u = 1 := by
  rw [radicalLayer_apfIndex_stable p π (Nat.zero_le n) hu hb,
    radicalLayer_zero, apfIndex_algEquiv K _ (IntermediateField.botEquiv K _),
    apfIndex_eq_one_of_bound_eq_top K K (apfRamificationBound_self K) hu]

/-- Shifting the upper parameter by the actual base valuation of `p`
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

section InfiniteProfiles

variable {K : Type*} [NontriviallyNormedField K] [IsCompleteDiscreteValuedField K]
    [PerfectField (𝓀[K])] [CharZero K]

local notation "G" => SeparableClosure K ≃ₐ[K] SeparableClosure K

variable (p : ℕ) [Fact p.Prime]
variable (π : 𝒪[K])

/-- A fixed embedding of the algebraic closure into the separable closure. -/
private def radicalClosureEmbedding : AlgebraicClosure K →ₐ[K] SeparableClosure K :=
  IsSepClosed.lift

/-- The image of the radical layer `n` in the separable closure. -/
private def radicalSeparableLayer (π : K) (n : ℕ) :
    IntermediateField K (SeparableClosure K) :=
  (radicalLayer p π n).map (radicalClosureEmbedding (K := K))

omit [IsCompleteDiscreteValuedField K] [PerfectField (𝓀[K])] in
private theorem radicalSeparableLayer_mono (π : K) :
    Monotone (radicalSeparableLayer p π) := fun _ _ hmn =>
  IntermediateField.map_mono (radicalClosureEmbedding (K := K)) (radicalLayer_mono p π hmn)

omit [PerfectField (𝓀[K])] in
private instance radicalSeparableLayer_finiteDimensional (π : K) (n : ℕ) :
    FiniteDimensional K (radicalSeparableLayer p π n) :=
  Module.Finite.equiv
    ((radicalLayer p π n).equivMap (radicalClosureEmbedding (K := K))).toLinearEquiv

private theorem radicalSeparable_apfSubgroup_index [hπ : Fact (Irreducible π)] (n : ℕ)
    {u : ℝ} (hu : 0 ≤ u) :
    (apfSubgroup K (radicalSeparableLayer p (π : K) n) u).index =
      apfIndex K (radicalLayer p (π : K) n) u := by
  let j := (radicalClosureEmbedding (K := K)).comp (radicalLayer p (π : K) n).val
  have hr : j.fieldRange = radicalSeparableLayer p (π : K) n := by
    rw [IntermediateField.fieldRange_comp_val]
    rfl
  rw [← hr]
  apply apfSubgroup_fieldRange_index_eq_apfIndex_of_ramificationIdx_eq_finrank K _ j _ hu
  rw [radicalLayer_ramificationIdx p π n (spectralValuation K _), finrank_radicalLayer p π n]

private theorem radicalSeparable_apfSubgroup_zero [hπ : Fact (Irreducible π)] (n : ℕ) :
    apfSubgroup K (radicalSeparableLayer p (π : K) n) 0 = ⊤ := by
  rw [← Subgroup.index_eq_one, radicalSeparable_apfSubgroup_index p π n le_rfl, apfIndex_zero]

private theorem radicalSeparable_apfSubgroup_eq_layer [hπ : Fact (Irreducible π)] (N : ℕ)
    {u : ℝ} (hu : 0 ≤ u) (hb : u ≤ radicalUpperBreak (K := K) p (N + 1)) :
    apfSubgroup K (⨆ n, radicalSeparableLayer p (π : K) n) u =
      apfSubgroup K (radicalSeparableLayer p (π : K) N) u := by
  let S := fun n => apfSubgroup K (radicalSeparableLayer p (π : K) n) u
  have hanti : Antitone S := fun m n hmn => sup_le_sup_right
    (IntermediateField.fixingSubgroup_le (radicalSeparableLayer_mono p (π : K) hmn)) _
  have hfin (n : ℕ) : (S n).FiniteIndex :=
    (isOpen_apfSubgroup_iff_finiteIndex K _ u).mp
      ((isAPFSubextension_of_finite K _).isOpen_apfSubgroup u (by linarith : -1 ≤ u))
  have hstable (n : ℕ) (hn : N ≤ n) : S n = S N := by
    let := hfin N
    apply Subgroup.eq_of_index_dvd_index (hanti hn)
    change (apfSubgroup K (radicalSeparableLayer p (π : K) n) u).index ∣
      (apfSubgroup K (radicalSeparableLayer p (π : K) N) u).index
    rw [radicalSeparable_apfSubgroup_index p π n hu,
      radicalSeparable_apfSubgroup_index p π N hu,
      radicalLayer_apfIndex_stable p π hn hu hb]
  rw [apfSubgroup_iSup_eq_iInf K _ (radicalSeparableLayer_mono p (π : K)) u]
  change (⨅ n, S n) = S N
  refine le_antisymm (iInf_le S N) (le_iInf fun n => ?_)
  rcases le_total N n with hn | hn
  · rw [hstable n hn]
  · exact hanti hn

/-- Every actual embedding of the infinite radical extension has full
zero-level APF product. No positivity assumption on the valuation of `p`
is needed for this assertion. -/
theorem apfSubgroup_kummerExtension_zero_eq_top [hπ : Fact (Irreducible π)]
    (j : kummerExtension p (π : K) →ₐ[K] SeparableClosure K) :
    apfSubgroup K j.fieldRange 0 = ⊤ := by
  let j₀ := (radicalClosureEmbedding (K := K)).comp (kummerExtension p (π : K)).val
  apply (apfSubgroup_fieldRange_eq_top_iff K _ j j₀ 0).mpr
  have hr : j₀.fieldRange = ⨆ n, radicalSeparableLayer p (π : K) n := by
    rw [IntermediateField.fieldRange_comp_val]
    change (⨆ n, radicalLayer p (π : K) n).map (radicalClosureEmbedding (K := K)) = _
    rw [IntermediateField.map_iSup]
    rfl
  rw [hr, radicalSeparable_apfSubgroup_eq_layer p π 0 le_rfl
    (radicalUpperBreak_nonneg p 1), radicalSeparable_apfSubgroup_zero p π 0]

omit [PerfectField (𝓀[K])] [CharZero K] in
private theorem exists_radicalUpperBreak_ge
    (he : 0 < (addVal 𝒪[K] (p : 𝒪[K])).toNat) (u : ℝ) :
    ∃ N : ℕ, u ≤ radicalUpperBreak (K := K) p (N + 1) := by
  have heℝ : (0 : ℝ) < (addVal 𝒪[K] (p : 𝒪[K])).toNat := Nat.cast_pos.mpr he
  have hp : (0 : ℝ) < (p : ℝ) - 1 := by
    have : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
    linarith
  obtain ⟨N, hN⟩ := exists_nat_gt (u / ((addVal 𝒪[K] (p : 𝒪[K])).toNat : ℝ))
  refine ⟨N, ?_⟩
  have hlt := (div_lt_iff₀ heℝ).mp hN
  have hmul := mul_nonneg heℝ.le (div_nonneg (show (0 : ℝ) ≤ 1 by norm_num) hp.le)
  simp only [radicalUpperBreak, Nat.cast_add, Nat.cast_one]
  nlinarith

private theorem radicalSeparable_isAPF [hπ : Fact (Irreducible π)]
    (he : 0 < (addVal 𝒪[K] (p : 𝒪[K])).toNat) :
    IsAPFSubextension K (⨆ n, radicalSeparableLayer p (π : K) n) := by
  constructor
  intro u hu
  by_cases h0 : 0 ≤ u
  · obtain ⟨N, hN⟩ := exists_radicalUpperBreak_ge p he u
    rw [radicalSeparable_apfSubgroup_eq_layer p π N h0 hN]
    exact (isAPFSubextension_of_finite K _).isOpen_apfSubgroup u hu
  · have hz : apfSubgroup K (⨆ n, radicalSeparableLayer p (π : K) n) 0 = ⊤ := by
      rw [radicalSeparable_apfSubgroup_eq_layer p π 0 le_rfl (radicalUpperBreak_nonneg p 1),
        radicalSeparable_apfSubgroup_zero p π 0]
    have hle := apfSubgroup_antitoneOn K (⨆ n, radicalSeparableLayer p (π : K) n)
      hu (by norm_num : -1 ≤ (0 : ℝ)) (le_of_not_ge h0)
    rw [hz] at hle
    rw [top_unique hle]
    exact isOpen_univ

/-- The actual infinite radical extension is APF whenever the residue
characteristic is `p`, expressed by the positive actual valuation of `p`. -/
theorem isAPF_kummerExtension_of_addVal_p_pos [hπ : Fact (Irreducible π)]
    (he : 0 < (addVal 𝒪[K] (p : 𝒪[K])).toNat) : IsAPF K (kummerExtension p (π : K)) := by
  let j := (radicalClosureEmbedding (K := K)).comp (kummerExtension p (π : K)).val
  apply (isAPF_iff_embedding K _ j).mpr
  have hr : j.fieldRange = ⨆ n, radicalSeparableLayer p (π : K) n := by
    rw [IntermediateField.fieldRange_comp_val]
    change (⨆ n, radicalLayer p (π : K) n).map (radicalClosureEmbedding (K := K)) = _
    rw [IntermediateField.map_iSup]
    rfl
  rw [hr]
  exact radicalSeparable_isAPF p π he

/-- At every fixed upper parameter before the next threshold, the actual
infinite radical index is exactly its attained finite-layer index. -/
theorem kummerExtension_apfIndex_eq_layer [hπ : Fact (Irreducible π)] (N : ℕ)
    {u : ℝ} (hu : 0 ≤ u) (hb : u ≤ radicalUpperBreak (K := K) p (N + 1)) :
    apfIndex K (kummerExtension p (π : K)) u =
      apfIndex K (radicalLayer p (π : K) N) u := by
  let j := (radicalClosureEmbedding (K := K)).comp (kummerExtension p (π : K)).val
  let jN := (radicalClosureEmbedding (K := K)).comp (radicalLayer p (π : K) N).val
  rw [apfIndex_eq_embedding K _ j, apfIndex_eq_embedding K _ jN]
  have hr : j.fieldRange = ⨆ n, radicalSeparableLayer p (π : K) n := by
    rw [IntermediateField.fieldRange_comp_val]
    change (⨆ n, radicalLayer p (π : K) n).map (radicalClosureEmbedding (K := K)) = _
    rw [IntermediateField.map_iSup]
    rfl
  have hrN : jN.fieldRange = radicalSeparableLayer p (π : K) N := by
    rw [IntermediateField.fieldRange_comp_val]
    rfl
  rw [hr, hrN, apfInertiaIndex, apfInertiaIndex,
    apfInertiaSubgroup_eq_inf K _ u hu, apfInertiaSubgroup_eq_inf K _ u hu,
    radicalSeparable_apfSubgroup_eq_layer p π N hu hb]

/-- The full APF-product index for any actual separable embedding equals
the intrinsic inertia index of the original infinite radical extension. -/
theorem kummerExtension_apfSubgroup_fieldRange_index [hπ : Fact (Irreducible π)]
    (he : 0 < (addVal 𝒪[K] (p : 𝒪[K])).toNat)
    (j : kummerExtension p (π : K) →ₐ[K] SeparableClosure K)
    {u : ℝ} (hu : 0 ≤ u) :
    (apfSubgroup K j.fieldRange u).index = apfIndex K (kummerExtension p (π : K)) u := by
  obtain ⟨N, hN⟩ := exists_radicalUpperBreak_ge p he u
  let j₀ := (radicalClosureEmbedding (K := K)).comp (kummerExtension p (π : K)).val
  have hr : j₀.fieldRange = ⨆ n, radicalSeparableLayer p (π : K) n := by
    rw [IntermediateField.fieldRange_comp_val]
    change (⨆ n, radicalLayer p (π : K) n).map (radicalClosureEmbedding (K := K)) = _
    rw [IntermediateField.map_iSup]
    rfl
  rw [apfSubgroup_fieldRange_index_eq K _ j j₀ u, hr,
    radicalSeparable_apfSubgroup_eq_layer p π N hu hN,
    radicalSeparable_apfSubgroup_index p π N hu,
    kummerExtension_apfIndex_eq_layer p π N hu hN]

/-- The actual infinite radical index is one through the first threshold. -/
theorem kummerExtension_apfIndex_initial [hπ : Fact (Irreducible π)] {u : ℝ}
    (hu : 0 ≤ u) (hb : u ≤ radicalUpperBreak (K := K) p 1) :
    apfIndex K (kummerExtension p (π : K)) u = 1 := by
  rw [kummerExtension_apfIndex_eq_layer p π 0 hu hb,
    radicalLayer_apfIndex_initial p π 0 hu hb]

/-- The actual infinite radical index on each interval between consecutive
thresholds includes the right endpoint. -/
theorem kummerExtension_apfIndex_interval [hπ : Fact (Irreducible π)] (j : ℕ) {u : ℝ}
    (hlo : radicalUpperBreak (K := K) p j < u)
    (hhi : u ≤ radicalUpperBreak (K := K) p (j + 1)) :
    apfIndex K (kummerExtension p (π : K)) u = p ^ j := by
  rw [kummerExtension_apfIndex_eq_layer p π j
    ((radicalUpperBreak_nonneg p j).trans hlo.le) hhi,
    radicalLayer_apfIndex_tail p π j hlo]

/-- Shifting by the actual positive base valuation of `p` crosses at most
one jump in the infinite radical extension. -/
theorem kummerExtension_apfIndex_growth [hπ : Fact (Irreducible π)]
    (he : 0 < (addVal 𝒪[K] (p : 𝒪[K])).toNat) {u : ℝ} (hu : 0 ≤ u) :
    apfIndex K (kummerExtension p (π : K)) (u + (addVal 𝒪[K] (p : 𝒪[K])).toNat) ≤
      p * apfIndex K (kummerExtension p (π : K)) u := by
  obtain ⟨N, hN⟩ := exists_radicalUpperBreak_ge p he
    (u + ((addVal 𝒪[K] (p : 𝒪[K])).toNat : ℝ))
  rw [kummerExtension_apfIndex_eq_layer p π N
      (add_nonneg hu (Nat.cast_nonneg _)) hN,
    kummerExtension_apfIndex_eq_layer p π N hu
      ((le_add_of_nonneg_right (Nat.cast_nonneg _)).trans hN)]
  exact radicalLayer_apfIndex_growth p π N hu

/-- The actual inverse Herbrand integral of the infinite radical extension
has the explicit geometric values at its affine upper thresholds. -/
theorem kummerExtension_apfPsi_break [hπ : Fact (Irreducible π)] (j : ℕ) :
    apfPsi K (kummerExtension p (π : K)) (radicalUpperBreak (K := K) p j) =
      (p : ℝ) ^ j * ((addVal 𝒪[K] (p : 𝒪[K])).toNat : ℝ) / ((p : ℝ) - 1) := by
  have heq : apfPsi K (kummerExtension p (π : K)) (radicalUpperBreak (K := K) p j) =
      apfPsi K (radicalLayer p (π : K) j) (radicalUpperBreak (K := K) p j) := by
    rw [apfPsi_eq_integral_index K _ (radicalUpperBreak_nonneg p j),
      apfPsi_eq_integral_index K _ (radicalUpperBreak_nonneg p j)]
    apply intervalIntegral.integral_congr
    rw [Set.uIcc_of_le (radicalUpperBreak_nonneg p j)]
    intro v hv
    exact congrArg (fun n : ℕ => (n : ℝ))
      (kummerExtension_apfIndex_eq_layer p π j hv.1
        (hv.2.trans (radicalUpperBreak_mono p (Nat.le_succ j))))
  rw [heq, radicalLayer_apfPsi_tail p π j _ le_rfl, sub_self, mul_zero, add_zero]

/-- The explicit radical profile gives the source strictness-ratio lower
bound after the first upper threshold. -/
theorem kummerExtension_apfPsi_div_index_ge [hπ : Fact (Irreducible π)]
    (he : 0 < (addVal 𝒪[K] (p : 𝒪[K])).toNat) {u : ℝ}
    (hu : radicalUpperBreak (K := K) p 1 ≤ u) :
    ((addVal 𝒪[K] (p : 𝒪[K])).toNat : ℝ) / ((p : ℝ) - 1) ≤
      apfPsi K (kummerExtension p (π : K)) u /
        (apfIndex K (kummerExtension p (π : K)) u : ℝ) := by
  have hAPF := isAPF_kummerExtension_of_addVal_p_pos p π he
  have hu0 := (radicalUpperBreak_nonneg p 1).trans hu
  have hp : (0 : ℝ) < p := Nat.cast_pos.mpr (Fact.out : p.Prime).pos
  have hratio (N : ℕ) (hN : u ≤ radicalUpperBreak (K := K) p (N + 1)) :
      ((addVal 𝒪[K] (p : 𝒪[K])).toNat : ℝ) / ((p : ℝ) - 1) ≤
        apfPsi K (kummerExtension p (π : K)) u /
          (apfIndex K (kummerExtension p (π : K)) u : ℝ) := by
    induction N with
    | zero =>
      rw [kummerExtension_apfIndex_initial p π hu0 hN, Nat.cast_one, div_one]
      calc
        _ ≤ radicalUpperBreak (K := K) p 1 := by
          simp only [radicalUpperBreak, Nat.cast_one, mul_add, mul_one,
            div_eq_mul_inv, one_mul]
          exact le_add_of_nonneg_left (Nat.cast_nonneg _)
        _ ≤ u := hu
        _ ≤ apfPsi K (kummerExtension p (π : K)) u :=
          IsAPF.le_apfPsi K (kummerExtension p (π : K)) u
    | succ N ih =>
      by_cases h : u ≤ radicalUpperBreak (K := K) p (N + 1)
      · exact ih h
      · have hlo : radicalUpperBreak (K := K) p (N + 1) < u := lt_of_not_ge h
        have hPsi := (IsAPF.strictMono_apfPsi K (kummerExtension p (π : K))).monotone hlo.le
        rw [kummerExtension_apfPsi_break p π (N + 1)] at hPsi
        rw [kummerExtension_apfIndex_interval p π (N + 1) hlo hN, Nat.cast_pow]
        apply (le_div_iff₀ (pow_pos hp (N + 1))).mpr
        calc
          _ = (p : ℝ) ^ (N + 1) * ((addVal 𝒪[K] (p : 𝒪[K])).toNat : ℝ) /
              ((p : ℝ) - 1) := by ring
          _ ≤ _ := hPsi
  obtain ⟨N, hN⟩ := exists_radicalUpperBreak_ge p he u
  exact hratio N hN

/-- The actual infinite radical extension is strictly APF at every prime
when the actual base valuation of `p` is positive. -/
theorem isStrictlyAPF_kummerExtension_of_addVal_p_pos [hπ : Fact (Irreducible π)]
    (he : 0 < (addVal 𝒪[K] (p : 𝒪[K])).toNat) :
    IsStrictlyAPF K (kummerExtension p (π : K)) := by
  have hp : (0 : ℝ) < (p : ℝ) - 1 := by
    have : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
    linarith
  have hlower : ENNReal.ofReal (((addVal 𝒪[K] (p : 𝒪[K])).toNat : ℝ) / ((p : ℝ) - 1)) ≤
      Filter.liminf (apfStrictnessRatio K (kummerExtension p (π : K))) Filter.atTop := by
    apply Filter.le_liminf_of_le (h := ?_)
    exact Filter.eventually_atTop.mpr ⟨radicalUpperBreak (K := K) p 1,
      fun u hu => ENNReal.ofReal_le_ofReal (kummerExtension_apfPsi_div_index_ge p π he hu)⟩
  exact {
    toIsAPF := isAPF_kummerExtension_of_addVal_p_pos p π he
    liminf_pos := (ENNReal.ofReal_pos.mpr (div_pos (Nat.cast_pos.mpr he) hp)).trans_le hlower }

section PadicBase

variable [Algebra (ℚ_[p]) K]
    [(NormedField.valuation (K := ℚ_[p])).HasExtension (NormedField.valuation (K := K))]

omit [PerfectField (𝓀[K])] [CharZero K] in
private theorem addVal_p_toNat_pos_of_padicBase : 0 < (addVal 𝒪[K] (p : 𝒪[K])).toNat := by
  rw [addVal_p_toNat_eq_padic_ramificationIdx p]
  exact local_ramificationIdx_pos
    𝒪[ℚ_[p]] 𝒪[K]

/-- The actual infinite radical extension over a norm-compatible `p`-adic
base is APF; positivity comes from its canonical ramification index. -/
instance isAPF_kummerExtension [hπ : Fact (Irreducible π)] :
    IsAPF K (kummerExtension p (π : K)) :=
  isAPF_kummerExtension_of_addVal_p_pos p π (addVal_p_toNat_pos_of_padicBase p)

/-- The actual infinite radical extension over a norm-compatible `p`-adic
base is strictly APF, including the prime two. -/
instance isStrictlyAPF_kummerExtension [hπ : Fact (Irreducible π)] :
    IsStrictlyAPF K (kummerExtension p (π : K)) :=
  isStrictlyAPF_kummerExtension_of_addVal_p_pos p π (addVal_p_toNat_pos_of_padicBase p)

end PadicBase

end InfiniteProfiles

section PrimeStepFirstBound

variable {K : Type*} [NontriviallyNormedField K] [IsCompleteDiscreteValuedField K]
    [PerfectField (𝓀[K])] [CharZero K]
variable (p : ℕ) [Fact p.Prime]
variable (π : 𝒪[K])

attribute [local instance] kummerBaseNormedField kummerBaseNormedAlgebra kummerBaseUltrametric
  kummerBaseComplete kummerBaseDVR kummerBaseCompleteDiscreteValuedField kummerBasePerfect
  kummerStepAlgebra kummerStepScalarTower
  kummerStepFinite kummerStepValuation kummerStepOwnValuation

/-- The intrinsic extended first bound of the actual consecutive radical
step equals the break determined by its original different, without normality. -/
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
