/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FalseTateExtension.Kummer.Breaks
public import FalseTateExtension.Kummer.Eisenstein
public import FalseTateExtension.Kummer.FiniteProfile
public import FalseTateExtension.Kummer.StepProfile
public import FontaineWintenberger.APF.BaseChange.Basic
public import FontaineWintenberger.APF.Elementary.PrimeDegree
public import FontaineWintenberger.APF.Galois.Union
public import FontaineWintenberger.APF.Strict
public import FontaineWintenberger.APF.Tower.TotallyRamified

/-!
# The Kummer extension is strictly APF

`K(π^{1/p^∞})/K` is strictly arithmetically profinite: its APF subgroups stabilize along the layers,
and the indices grow by a factor `p` at every break.

## References

* Wintenberger, *Le corps des normes de certaines extensions infinies de corps locaux;
  applications*, 1.2.3.
-/

@[expose] public section

noncomputable section

namespace FalseTateExtension

open FontaineWintenberger IsDiscreteValuationRing

section InfiniteProfiles

variable {K : Type*} [NontriviallyNormedField K] [IsCompleteDiscreteValuedField K]
    [PerfectField (𝓀[K])] [CharZero K]

local notation "G" => SeparableClosure K ≃ₐ[K] SeparableClosure K

variable (p : ℕ) [Fact p.Prime]
variable (π : 𝒪[K])

/-- A fixed embedding of the algebraic closure into the separable closure. -/
def radicalClosureEmbedding : AlgebraicClosure K →ₐ[K] SeparableClosure K :=
  IsSepClosed.lift

/-- The image of the radical layer `n` in the separable closure. -/
def radicalSeparableLayer (π : K) (n : ℕ) :
    IntermediateField K (SeparableClosure K) :=
  (radicalLayer p π n).map (radicalClosureEmbedding (K := K))

omit [IsCompleteDiscreteValuedField K] [PerfectField (𝓀[K])] in
theorem radicalSeparableLayer_mono (π : K) :
    Monotone (radicalSeparableLayer p π) := fun _ _ hmn =>
  IntermediateField.map_mono (radicalClosureEmbedding (K := K)) (radicalLayer_mono p π hmn)

omit [PerfectField (𝓀[K])] in
instance radicalSeparableLayer_finiteDimensional (π : K) (n : ℕ) :
    FiniteDimensional K (radicalSeparableLayer p π n) :=
  Module.Finite.equiv
    ((radicalLayer p π n).equivMap (radicalClosureEmbedding (K := K))).toLinearEquiv

theorem radicalSeparable_apfSubgroup_index [hπ : Fact (Irreducible π)] (n : ℕ)
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

theorem radicalSeparable_apfSubgroup_zero [hπ : Fact (Irreducible π)] (n : ℕ) :
    apfSubgroup K (radicalSeparableLayer p (π : K) n) 0 = ⊤ := by
  rw [← Subgroup.index_eq_one, radicalSeparable_apfSubgroup_index p π n le_rfl, apfIndex_zero]

theorem radicalSeparable_apfSubgroup_eq_layer [hπ : Fact (Irreducible π)] (N : ℕ)
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
theorem exists_radicalUpperBreak_ge
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

theorem radicalSeparable_isAPF [hπ : Fact (Irreducible π)]
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
theorem addVal_p_toNat_pos_of_padicBase : 0 < (addVal 𝒪[K] (p : 𝒪[K])).toNat := by
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

end FalseTateExtension
end
