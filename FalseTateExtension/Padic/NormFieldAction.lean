/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FalseTateExtension.Padic.NormFieldCoordinates
public import FalseTateExtension.Padic.TameGenerator
public import FontaineWintenberger.FieldOfNorms.Galois.Action
public import Mathlib.RingTheory.PowerSeries.Substitution
public import Mathlib.Dynamics.PeriodicPts.Defs

/-!
# Actual false Tate power series and their first coefficients

The coordinate attached to every original norm-field uniformizer has the
Kummer ramification profile. Continuity of the original action extends its
first nonlinear coefficient to all p-adic translation powers, and the actual
tame conjugation relation determines the tame linear coefficient.

References: Yuan, Proposition 5.1 and Lemma 5.3.
-/

@[expose] public section

noncomputable section

namespace FalseTateExtension

open FontaineWintenberger

section FiniteJets

variable {R : Type*} [CommRing R]

private theorem coeff_pow_of_lt (g : PowerSeries R) (hg : g.constantCoeff = 0)
    (d e : ℕ) (h : e < d) : (g ^ d).coeff e = 0 := by
  obtain ⟨a, ha⟩ := PowerSeries.X_dvd_iff.mpr hg
  apply PowerSeries.X_pow_dvd_iff.mp
    (show (PowerSeries.X : PowerSeries R) ^ d ∣ g ^ d from
      ⟨a ^ d, by rw [ha, mul_pow]⟩) e h

private theorem coeff_pow_diagonal (g : PowerSeries R) (hg : g.constantCoeff = 0)
    (d : ℕ) : (g ^ d).coeff d = g.coeff 1 ^ d := by
  obtain ⟨a, rfl⟩ := PowerSeries.X_dvd_iff.mpr hg
  have hlin : (PowerSeries.X * a).coeff 1 = a.constantCoeff := by
    simpa only [pow_one, zero_add, PowerSeries.coeff_zero_eq_constantCoeff] using
      PowerSeries.coeff_X_pow_mul a 1 0
  rw [hlin, mul_pow]
  simpa only [zero_add, PowerSeries.coeff_zero_eq_constantCoeff, map_pow] using
    PowerSeries.coeff_X_pow_mul (a ^ d) d 0

private theorem coeff_subst_eq_sum (g f : PowerSeries R)
    (hg : g.constantCoeff = 0) (e : ℕ) :
    PowerSeries.coeff e (PowerSeries.subst g f) =
      ∑ d ∈ Finset.range (e + 1), f.coeff d * (g ^ d).coeff e := by
  classical
  rw [PowerSeries.coeff_subst' (PowerSeries.HasSubst.of_constantCoeff_zero' hg)]
  simp only [smul_eq_mul]
  apply finsum_eq_finsetSum_of_support_subset
  intro d hd
  apply Finset.mem_range.mpr
  by_contra h
  have he : e < d := by omega
  exact hd (by simp [coeff_pow_of_lt g hg d e he])

private theorem X_pow_dvd_pow_sub (g : PowerSeries R) (hg : g.constantCoeff = 0)
    (N : ℕ) (hN : (PowerSeries.X : PowerSeries R) ^ N ∣ g - PowerSeries.X)
    (n : ℕ) :
    (PowerSeries.X : PowerSeries R) ^ (N + n) ∣
      g ^ (n + 1) - PowerSeries.X ^ (n + 1) := by
  induction n with
  | zero => simpa using hN
  | succ n ih =>
      have h₁ : (PowerSeries.X : PowerSeries R) ^ (N + n + 1) ∣
          (g ^ (n + 1) - PowerSeries.X ^ (n + 1)) * g := by
        rw [pow_succ]
        exact mul_dvd_mul ih (PowerSeries.X_dvd_iff.mpr hg)
      have h₂ : (PowerSeries.X : PowerSeries R) ^ (N + n + 1) ∣
          PowerSeries.X ^ (n + 1) * (g - PowerSeries.X) := by
        rw [show N + n + 1 = (n + 1) + N by omega, pow_add]
        exact mul_dvd_mul dvd_rfl hN
      convert dvd_add h₁ h₂ using 1
      ring

private theorem coeff_pow_sub_X_pow (g : PowerSeries R) (hg : g.constantCoeff = 0)
    (N : ℕ) (hN : (PowerSeries.X : PowerSeries R) ^ N ∣ g - PowerSeries.X)
    (d e : ℕ) (hd : 2 ≤ d) (he : e ≤ N) :
    (g ^ d - PowerSeries.X ^ d).coeff e = 0 := by
  have h := X_pow_dvd_pow_sub g hg N hN (d - 1)
  rw [Nat.sub_add_cancel (by omega : 1 ≤ d)] at h
  exact PowerSeries.X_pow_dvd_iff.mp h e (by omega)

private theorem coeff_subst_near_inner (g f : PowerSeries R)
    (hg : g.constantCoeff = 0) (N : ℕ)
    (hN : (PowerSeries.X : PowerSeries R) ^ N ∣ g - PowerSeries.X)
    (e : ℕ) (he₁ : 1 ≤ e) (he : e ≤ N) :
    PowerSeries.coeff e (PowerSeries.subst g f) - f.coeff e =
      f.coeff 1 * (g - PowerSeries.X).coeff e := by
  classical
  have hX : (PowerSeries.X : PowerSeries R).constantCoeff = 0 := by simp
  have hs : ∑ d ∈ Finset.range (e + 1),
      f.coeff d * ((g ^ d).coeff e - (PowerSeries.X ^ d).coeff e) =
      f.coeff 1 * (g - PowerSeries.X).coeff e := by
    rw [Finset.sum_eq_single 1]
    · simp only [pow_one, map_sub]
    · intro d hd hd₁
      by_cases hd₀ : d = 0
      · simp [hd₀]
      · rw [← map_sub, coeff_pow_sub_X_pow g hg N hN d e (by omega) he, mul_zero]
    · simp only [Finset.mem_range]
      omega
  have hsub :
      PowerSeries.coeff e (PowerSeries.subst g f) -
        PowerSeries.coeff e (PowerSeries.subst PowerSeries.X f) =
      f.coeff 1 * (g - PowerSeries.X).coeff e := by
    rw [coeff_subst_eq_sum g f hg, coeff_subst_eq_sum PowerSeries.X f hX,
      ← Finset.sum_sub_distrib]
    convert hs using 1
    apply Finset.sum_congr rfl
    intro d hd
    ring
  simpa using hsub

private theorem coeff_subst_near_outer (g f : PowerSeries R)
    (hg : g.constantCoeff = 0) (N : ℕ)
    (hN : (PowerSeries.X : PowerSeries R) ^ N ∣ f - PowerSeries.X)
    (e : ℕ) (he : e ≤ N) :
    PowerSeries.coeff e (PowerSeries.subst g f) - g.coeff e =
      (f - PowerSeries.X).coeff e * g.coeff 1 ^ e := by
  classical
  have hs : PowerSeries.coeff e (PowerSeries.subst g (f - PowerSeries.X)) =
      (f - PowerSeries.X).coeff e * g.coeff 1 ^ e := by
    rw [coeff_subst_eq_sum g (f - PowerSeries.X) hg, Finset.sum_eq_single e]
    · rw [coeff_pow_diagonal g hg]
    · intro d hd hde
      have hd' : d < N := by have := Finset.mem_range.mp hd; omega
      rw [PowerSeries.X_pow_dvd_iff.mp hN d hd', zero_mul]
    · simp
  simpa only [PowerSeries.subst_sub (PowerSeries.HasSubst.of_constantCoeff_zero' hg),
    PowerSeries.subst_X (PowerSeries.HasSubst.of_constantCoeff_zero' hg), map_sub] using hs

private theorem coeff_subst_iterate (f : PowerSeries R) (hf : f.constantCoeff = 0)
    (N : ℕ) (hN₂ : 2 ≤ N)
    (hN : (PowerSeries.X : PowerSeries R) ^ N ∣ f - PowerSeries.X)
    (n e : ℕ) (he : e ≤ N) :
    PowerSeries.coeff e
      (((PowerSeries.subst f : PowerSeries R → PowerSeries R)^[n] PowerSeries.X) -
        PowerSeries.X) = (n : R) * (f - PowerSeries.X).coeff e := by
  induction n generalizing e with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      let g := (PowerSeries.subst f : PowerSeries R → PowerSeries R)^[n] PowerSeries.X
      have hi (i : ℕ) (hi : i ≤ N) :
          (g - PowerSeries.X).coeff i = (n : R) * (f - PowerSeries.X).coeff i :=
        ih i hi
      by_cases he₀ : e = 0
      · subst e
        have h₀ := hi 0 (by omega)
        simp only [map_sub] at h₀ ⊢
        rw [coeff_subst_eq_sum f g hf]
        simpa [hf] using h₀
      · have hlin : g.coeff 1 = 1 := by
          have h := hi 1 (by omega)
          have hz := PowerSeries.X_pow_dvd_iff.mp hN 1 (by omega)
          have hz' := h.trans (by rw [hz, mul_zero])
          simpa [sub_eq_zero] using hz' 
        have hcomp := coeff_subst_near_inner f g hf N hN e (by omega) he
        have hprev := hi e he
        simp only [map_sub, hlin, one_mul] at hcomp hprev ⊢
        push_cast
        linear_combination hcomp + hprev

end FiniteJets

section ActualAction

open WithZero
open scoped Topology PowerSeries.WithPiTopology LaurentSeries

variable (p : ℕ) [Fact p.Prime]

variable {π : (NormedField.valuation (K := Padic p)).valuationSubring}
variable (hp₂ : p ≠ 2) (hπ : Irreducible π)

local notation "FT" => falseTateExtension p (π : Padic p)
local notation "NX" => FieldOfNorms (Padic p) FT
local instance normFieldActionInfinite : Fact (¬ Module.Finite (Padic p) FT) :=
  ⟨not_finiteDimensional_falseTateExtension_padic p (π : Padic p)⟩

/-- Every original coordinate has the literal Kummer displacement valuation. -/
theorem falseTatePowerSeriesCoordinate_tau_pow_valuation (u : NX)
    (hu : letI := isAPF_falseTateExtension p hπ
      FieldOfNorms.valuation (Padic p) FT u = exp (-1 : ℤ)) (k : ℕ) :
    letI := isAPF_falseTateExtension p hπ
    (Valued.v
      ((falseTatePowerSeriesCoordinate p hp₂ hπ u hu
        ((tau p hp₂ hπ).val ^ (p ^ k)) : LaurentSeries (ZMod p)) -
          HahnSeries.single (1 : ℤ) 1) : WithZero (Multiplicative ℤ)) =
      exp (-(kummerRamificationBreak p k + 1 : ℕ) : ℤ) := by
  have := isAPF_falseTateExtension p hπ
  exact (valuation_falseTatePowerSeriesCoordinate_displacement p hp₂ hπ u hu _).trans
    (normLimitValuation_tau_pow_displacement p hp₂ hπ u hu k)

/-- The ordinary power-series order in every original coordinate is the
unshifted finite Kummer ramification number. -/
theorem falseTatePowerSeriesCoordinate_tau_pow_order (u : NX)
    (hu : letI := isAPF_falseTateExtension p hπ
      FieldOfNorms.valuation (Padic p) FT u = exp (-1 : ℤ)) (k : ℕ) :
    letI := isAPF_falseTateExtension p hπ
    (falseTatePowerSeriesCoordinate p hp₂ hπ u hu
      ((tau p hp₂ hπ).val ^ (p ^ k)) - PowerSeries.X).order =
        (↑(kummerRamificationBreak p k + 1) : ℕ∞) := by
  have := isAPF_falseTateExtension p hπ
  let f := falseTatePowerSeriesCoordinate p hp₂ hπ u hu
    ((tau p hp₂ hπ).val ^ (p ^ k)) - PowerSeries.X
  have hv : (Valued.v (algebraMap (PowerSeries (ZMod p)) (LaurentSeries (ZMod p)) f) :
      WithZero (Multiplicative ℤ)) =
      exp (-(kummerRamificationBreak p k + 1 : ℕ) : ℤ) := by
    simpa only [f, map_sub, LaurentSeries.coe_algebraMap, HahnSeries.ofPowerSeries_X] using
      falseTatePowerSeriesCoordinate_tau_pow_valuation p hp₂ hπ u hu k
  have hf : f ≠ 0 := by
    intro hf
    rw [hf, map_zero, map_zero] at hv
    exact exp_ne_zero hv.symm
  have horder := laurent_valuation_powerSeries_order f hf
  have hn : f.order.toNat = kummerRamificationBreak p k + 1 := by
    have he := exp_injective (horder.symm.trans hv)
    omega
  exact (PowerSeries.coe_toNat_order hf).symm.trans (congrArg (fun n : ℕ => (n : ℕ∞)) hn)

/-- The original Kummer coordinate has no positive compositional period. -/
theorem falseTatePowerSeriesCoordinate_tau_infiniteOrder (u : NX)
    (hu : letI := isAPF_falseTateExtension p hπ
      FieldOfNorms.valuation (Padic p) FT u = exp (-1 : ℤ)) :
    letI := isAPF_falseTateExtension p hπ
    ∀ n : ℕ, 0 < n →
      (PowerSeries.subst (falseTatePowerSeriesCoordinate p hp₂ hπ u hu
        (tau p hp₂ hπ).val) : PowerSeries (ZMod p) → PowerSeries (ZMod p))^[n]
          PowerSeries.X ≠ PowerSeries.X := by
  have := isAPF_falseTateExtension p hπ
  intro m hm hperiod
  let f := falseTatePowerSeriesCoordinate p hp₂ hπ u hu (tau p hp₂ hπ).val
  let S := (PowerSeries.subst f : PowerSeries (ZMod p) → PowerSeries (ZMod p))
  have hper : Function.IsPeriodicPt S m PowerSeries.X := hperiod
  have hinj : Function.Injective (fun k : ℕ =>
      falseTatePowerSeriesCoordinate p hp₂ hπ u hu
        ((tau p hp₂ hπ).val ^ (p ^ k))) := by
    intro i j hij
    have he := congrArg (fun f : PowerSeries (ZMod p) => (f - PowerSeries.X).order) hij
    rw [falseTatePowerSeriesCoordinate_tau_pow_order,
      falseTatePowerSeriesCoordinate_tau_pow_order] at he
    have hd : kummerRamificationBreak p i = kummerRamificationBreak p j := by
      exact Nat.add_right_cancel (ENat.natCast_inj.mp he)
    exact (kummerRamificationBreak_strictMono p (Fact.out : p.Prime).two_le).injective hd
  apply (Set.finite_range (fun n : Fin m => S^[n.val] PowerSeries.X)).not_infinite
  apply Set.infinite_of_injective_forall_mem hinj
  intro k
  refine ⟨⟨p ^ k % m, Nat.mod_lt _ hm⟩, ?_⟩
  exact (hper.iterate_mod_apply (p ^ k)).trans
    (falseTatePowerSeriesCoordinate_pow p hp₂ hπ u hu (tau p hp₂ hπ).val (p ^ k)).symm

/-- Each coefficient of the actual continuous Kummer powers is continuous
in the original p-adic parameter. -/
theorem continuous_falseTatePowerSeriesCoordinate_tauPadicPower_coeff (u : NX)
    (hu : letI := isAPF_falseTateExtension p hπ
      FieldOfNorms.valuation (Padic p) FT u = exp (-1 : ℤ)) (j : ℕ) :
    letI := isAPF_falseTateExtension p hπ
    letI : UniformSpace (ZMod p) := ⊥
    Continuous (fun a : PadicInt p =>
      (falseTatePowerSeriesCoordinate p hp₂ hπ u hu
        (tauPadicPower p hp₂ hπ a).val).coeff j) := by
  have := isAPF_falseTateExtension p hπ
  let : UniformSpace (ZMod p) := ⊥
  have hτ : Continuous (fun a : PadicInt p => (tauPadicPower p hp₂ hπ a).val) :=
    continuous_subtype_val.comp (continuous_tauPadicPower p hp₂ hπ)
  have haction := FieldOfNorms.continuous_aut_apply (Padic p) FT u
  have he := (uniformContinuous_falseTateNormFieldLaurentEquiv_symm
    p hp₂ hπ u hu).continuous
  have hcoeff := (LaurentSeries.uniformContinuous_coeff (K := ZMod p) (j : ℤ)).continuous
  have hcont := hcoeff.comp (he.comp (haction.comp hτ))
  convert hcont using 1
  funext a
  have hback : (falseTateNormFieldLaurentEquiv p hp₂ hπ u hu).symm
      (FieldOfNorms.aut (Padic p) FT (tauPadicPower p hp₂ hπ a).val u) =
      (falseTatePowerSeriesCoordinate p hp₂ hπ u hu
        (tauPadicPower p hp₂ hπ a).val : LaurentSeries (ZMod p)) := by
    apply (falseTateNormFieldLaurentEquiv p hp₂ hπ u hu).injective
    rw [RingEquiv.apply_symm_apply,
      falseTateNormFieldLaurentEquiv_powerSeriesCoordinate]
  dsimp only [Function.comp_apply]
  rw [hback]
  simp

private theorem tau_first_order (u : NX)
    (hu : letI := isAPF_falseTateExtension p hπ
      FieldOfNorms.valuation (Padic p) FT u = exp (-1 : ℤ)) :
    letI := isAPF_falseTateExtension p hπ
    (falseTatePowerSeriesCoordinate p hp₂ hπ u hu (tau p hp₂ hπ).val -
      PowerSeries.X).order = (↑(2 * p) : ℕ∞) := by
  have := isAPF_falseTateExtension p hπ
  have h := falseTatePowerSeriesCoordinate_tau_pow_order p hp₂ hπ u hu 0
  rw [pow_zero, pow_one, kummerRamificationBreak_zero p
    (by have := (Fact.out : p.Prime).two_le; omega)] at h
  have hnum : 2 * p - 1 + 1 = 2 * p := by
    have := (Fact.out : p.Prime).two_le
    omega
  simpa only [hnum] using h

private theorem continuous_padicResidue :
    letI : UniformSpace (ZMod p) := ⊥
    Continuous (PadicInt.toZMod : PadicInt p → ZMod p) := by
  let : UniformSpace (ZMod p) := ⊥
  apply continuous_iff_continuousAt.mpr
  intro a
  have heq : ∀ᶠ b in nhds a, PadicInt.toZMod b = PadicInt.toZMod a := by
    filter_upwards [Metric.ball_mem_nhds a zero_lt_one] with b hb
    apply sub_eq_zero.mp
    rw [← map_sub, PadicInt.toZMod_eq_zero_iff_norm_lt_one]
    simpa only [Metric.mem_ball, dist_eq_norm] using hb
  apply Filter.Tendsto.congr' _ tendsto_const_nhds
  filter_upwards [heq] with b hb
  exact hb.symm

/-- The first finite jet of actual p-adic Kummer powers is scalar
multiplication by the original residue character of the exponent. -/
theorem falseTatePowerSeriesCoordinate_tauPadicPower_coeff_displacement (u : NX)
    (hu : letI := isAPF_falseTateExtension p hπ
      FieldOfNorms.valuation (Padic p) FT u = exp (-1 : ℤ))
    (a : PadicInt p) (j : ℕ) (hj : j ≤ 2 * p) :
    letI := isAPF_falseTateExtension p hπ
    (falseTatePowerSeriesCoordinate p hp₂ hπ u hu
      (tauPadicPower p hp₂ hπ a).val - PowerSeries.X).coeff j =
        PadicInt.toZMod a *
          (falseTatePowerSeriesCoordinate p hp₂ hπ u hu (tau p hp₂ hπ).val -
            PowerSeries.X).coeff j := by
  have := isAPF_falseTateExtension p hπ
  let : UniformSpace (ZMod p) := ⊥
  have : DiscreteUniformity (ZMod p) := inferInstance
  let f := falseTatePowerSeriesCoordinate p hp₂ hπ u hu (tau p hp₂ hπ).val
  have horder : (f - PowerSeries.X).order = (↑(2 * p) : ℕ∞) :=
    tau_first_order p hp₂ hπ u hu
  have hdiv : (PowerSeries.X : PowerSeries (ZMod p)) ^ (2 * p) ∣
      f - PowerSeries.X :=
    PowerSeries.X_pow_dvd_iff.mpr (PowerSeries.order_eq_nat.mp horder).2
  have hL : Continuous (fun b : PadicInt p =>
      (falseTatePowerSeriesCoordinate p hp₂ hπ u hu
        (tauPadicPower p hp₂ hπ b).val - PowerSeries.X).coeff j) := by
    simp only [map_sub]
    exact (continuous_falseTatePowerSeriesCoordinate_tauPadicPower_coeff
      p hp₂ hπ u hu j).sub continuous_const
  have hR : Continuous (fun b : PadicInt p =>
      PadicInt.toZMod b * (f - PowerSeries.X).coeff j) :=
    (continuous_padicResidue p).mul continuous_const
  apply congrFun ((PadicInt.denseRange_natCast (p := p)).equalizer hL hR ?_) a
  funext n
  dsimp only [Function.comp_apply]
  have hpow : (tauPadicPower p hp₂ hπ (n : PadicInt p)).val =
      (tau p hp₂ hπ).val ^ n := by
    have h := congrArg Subtype.val (tauPadicPower_intCast p hp₂ hπ (n : ℤ))
    simpa only [Int.cast_natCast, zpow_natCast, Subgroup.coe_pow] using h
  rw [hpow, falseTatePowerSeriesCoordinate_pow, map_natCast]
  exact coeff_subst_iterate f
    (falseTatePowerSeriesCoordinate_constantCoeff p hp₂ hπ u hu _)
    (2 * p) (by have := (Fact.out : p.Prime).two_le; omega) hdiv n j hj

/-- The actual wild coordinate is tangent to the identity. -/
theorem falseTatePowerSeriesCoordinate_tau_coeff_one (u : NX)
    (hu : letI := isAPF_falseTateExtension p hπ
      FieldOfNorms.valuation (Padic p) FT u = exp (-1 : ℤ)) :
    letI := isAPF_falseTateExtension p hπ
    (falseTatePowerSeriesCoordinate p hp₂ hπ u hu (tau p hp₂ hπ).val).coeff 1 = 1 := by
  have := isAPF_falseTateExtension p hπ
  have h := (PowerSeries.order_eq_nat.mp (tau_first_order p hp₂ hπ u hu)).2 1
    (by have := (Fact.out : p.Prime).two_le; omega)
  simpa [sub_eq_zero] using h

/-- The first nonlinear coefficient of the actual wild coordinate is nonzero. -/
theorem falseTatePowerSeriesCoordinate_tau_coeff_first_ne_zero (u : NX)
    (hu : letI := isAPF_falseTateExtension p hπ
      FieldOfNorms.valuation (Padic p) FT u = exp (-1 : ℤ)) :
    letI := isAPF_falseTateExtension p hπ
    (falseTatePowerSeriesCoordinate p hp₂ hπ u hu (tau p hp₂ hπ).val).coeff
      (2 * p) ≠ 0 := by
  have := isAPF_falseTateExtension p hπ
  have h := (PowerSeries.order_eq_nat.mp (tau_first_order p hp₂ hπ u hu)).1
  have hN : 2 * p ≠ 1 := by have := (Fact.out : p.Prime).two_le; omega
  simpa [PowerSeries.coeff_X, hN] using h

/-- The exact profile holds for literal substitution iterates of the original
wild coordinate, for every original uniformizer. -/
theorem falseTatePowerSeriesCoordinate_tau_iterate_order (u : NX)
    (hu : letI := isAPF_falseTateExtension p hπ
      FieldOfNorms.valuation (Padic p) FT u = exp (-1 : ℤ)) (k : ℕ) :
    letI := isAPF_falseTateExtension p hπ
    (((PowerSeries.subst
      (falseTatePowerSeriesCoordinate p hp₂ hπ u hu (tau p hp₂ hπ).val) :
        PowerSeries (ZMod p) → PowerSeries (ZMod p))^[p ^ k] PowerSeries.X) -
          PowerSeries.X).order = (↑(kummerRamificationBreak p k + 1) : ℕ∞) := by
  have := isAPF_falseTateExtension p hπ
  rw [← falseTatePowerSeriesCoordinate_pow]
  exact falseTatePowerSeriesCoordinate_tau_pow_order p hp₂ hπ u hu k

/-- The actual tame conjugation relation determines the same original
linear coefficient in every original norm-field coordinate. -/
theorem falseTatePowerSeriesCoordinate_tameGenerator_coeff_one (u : NX)
    (hu : letI := isAPF_falseTateExtension p hπ
      FieldOfNorms.valuation (Padic p) FT u = exp (-1 : ℤ)) :
    letI := isAPF_falseTateExtension p hπ
    (falseTatePowerSeriesCoordinate p hp₂ hπ u hu
      (tameGenerator p hp₂ hπ).val).coeff 1 =
      PadicInt.toZMod
        (padicCyclotomicCharacter p (π : Padic p) (tameGenerator p hp₂ hπ).val :
          PadicInt p) := by
  have := isAPF_falseTateExtension p hπ
  let δ := (tameGenerator p hp₂ hπ).val
  let t := (tau p hp₂ hπ).val
  let a : PadicInt p := padicCyclotomicCharacter p (π : Padic p) δ
  let f := falseTatePowerSeriesCoordinate p hp₂ hπ u hu t
  let w := falseTatePowerSeriesCoordinate p hp₂ hπ u hu δ
  let h := falseTatePowerSeriesCoordinate p hp₂ hπ u hu
    (tauPadicPower p hp₂ hπ a).val
  let α := (f - PowerSeries.X).coeff (2 * p)
  let ell := w.coeff 1
  have hp : 2 ≤ p := (Fact.out : p.Prime).two_le
  have hN : 2 ≤ 2 * p := by omega
  have horder : (f - PowerSeries.X).order = (↑(2 * p) : ℕ∞) :=
    tau_first_order p hp₂ hπ u hu
  have hα : α ≠ 0 := (PowerSeries.order_eq_nat.mp horder).1
  have hell : ell ≠ 0 :=
    (falseTatePowerSeriesCoordinate_linear_isUnit p hp₂ hπ u hu δ).ne_zero
  have hf : (PowerSeries.X : PowerSeries (ZMod p)) ^ (2 * p) ∣ f - PowerSeries.X :=
    PowerSeries.X_pow_dvd_iff.mpr (PowerSeries.order_eq_nat.mp horder).2
  have hjet (j : ℕ) (hj : j ≤ 2 * p) :
      (h - PowerSeries.X).coeff j = PadicInt.toZMod a * (f - PowerSeries.X).coeff j :=
    falseTatePowerSeriesCoordinate_tauPadicPower_coeff_displacement p hp₂ hπ u hu a j hj
  have hh : (PowerSeries.X : PowerSeries (ZMod p)) ^ (2 * p) ∣ h - PowerSeries.X := by
    apply PowerSeries.X_pow_dvd_iff.mpr
    intro j hj
    rw [hjet j (by omega), (PowerSeries.order_eq_nat.mp horder).2 j hj, mul_zero]
  have hrel : δ * t = (tauPadicPower p hp₂ hπ a).val * δ := by
    have hc := tameGenerator_conj_tau p hp₂ hπ
    change δ * t * δ⁻¹ = (tauPadicPower p hp₂ hπ a).val at hc
    have hc' := congrArg (fun g : FT ≃ₐ[Padic p] FT => g * δ) hc
    simpa only [mul_assoc, inv_mul_cancel, mul_one] using hc'
  have hcomp : PowerSeries.subst h w = PowerSeries.subst w f := by
    have hc := congrArg (falseTatePowerSeriesCoordinate p hp₂ hπ u hu) hrel
    rw [falseTatePowerSeriesCoordinate_mul, falseTatePowerSeriesCoordinate_mul] at hc
    exact hc.symm
  have hleft := coeff_subst_near_inner h w
    (falseTatePowerSeriesCoordinate_constantCoeff p hp₂ hπ u hu _) (2 * p) hh
    (2 * p) (by omega) le_rfl
  have hright := coeff_subst_near_outer w f
    (falseTatePowerSeriesCoordinate_constantCoeff p hp₂ hπ u hu _) (2 * p) hf
    (2 * p) le_rfl
  have hlead : ell * (PadicInt.toZMod a * α) = α * ell ^ (2 * p) := by
    exact (congrArg (fun x : ZMod p => ell * x) (hjet (2 * p) le_rfl)).symm.trans
      (hleft.symm.trans ((congrArg (fun q : PowerSeries (ZMod p) =>
        q.coeff (2 * p) - w.coeff (2 * p)) hcomp).trans hright))
  have hcancel : ell * PadicInt.toZMod a = ell ^ (2 * p) := by
    apply mul_left_cancel₀ hα
    calc
      α * (ell * PadicInt.toZMod a) = ell * (PadicInt.toZMod a * α) := by ring
      _ = α * ell ^ (2 * p) := hlead
  have hfermat : ell ^ (p - 1) = 1 := by
    exact ZMod.pow_card_sub_one_eq_one hell
  have hpower : ell ^ (2 * p) = ell * ell := by
    rw [show 2 * p = (p - 1) + (p - 1) + 2 by omega, pow_add, pow_add,
      hfermat, one_mul, one_mul, pow_two]
  have heq : PadicInt.toZMod a = ell := by
    apply mul_left_cancel₀ hell
    exact hcancel.trans hpower
  exact heq.symm

/-- The actual tame linear coefficient has exact multiplicative order
p - 1 in the original prime field. -/
theorem orderOf_falseTatePowerSeriesCoordinate_tameGenerator_linear (u : NX)
    (hu : letI := isAPF_falseTateExtension p hπ
      FieldOfNorms.valuation (Padic p) FT u = exp (-1 : ℤ)) :
    letI := isAPF_falseTateExtension p hπ
    orderOf ((falseTatePowerSeriesCoordinate p hp₂ hπ u hu
      (tameGenerator p hp₂ hπ).val).coeff 1) = p - 1 := by
  have := isAPF_falseTateExtension p hπ
  rw [falseTatePowerSeriesCoordinate_tameGenerator_coeff_one]
  change orderOf ((Units.map PadicInt.toZMod.toMonoidHom
    (padicCyclotomicCharacter p (π : Padic p) (tameGenerator p hp₂ hπ).val) :
      (ZMod p)ˣ) : ZMod p) = p - 1
  rw [orderOf_units]
  exact orderOf_tameGenerator_residueCharacter p hp₂ hπ

/-- The same exact order holds for the original linear coefficient regarded
as a unit, with its canonical inverse. -/
theorem orderOf_falseTatePowerSeriesCoordinate_tameGenerator_linear_unit (u : NX)
    (hu : letI := isAPF_falseTateExtension p hπ
      FieldOfNorms.valuation (Padic p) FT u = exp (-1 : ℤ)) :
    letI := isAPF_falseTateExtension p hπ
    orderOf (Units.mk0
      ((falseTatePowerSeriesCoordinate p hp₂ hπ u hu
        (tameGenerator p hp₂ hπ).val).coeff 1)
      (falseTatePowerSeriesCoordinate_linear_isUnit p hp₂ hπ u hu _).ne_zero) =
        p - 1 := by
  have := isAPF_falseTateExtension p hπ
  rw [← orderOf_units]
  exact orderOf_falseTatePowerSeriesCoordinate_tameGenerator_linear p hp₂ hπ u hu

end ActualAction

end FalseTateExtension
