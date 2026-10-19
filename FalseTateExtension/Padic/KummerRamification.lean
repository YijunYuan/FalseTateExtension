/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FalseTateExtension.Padic.Viviani
public import FontaineWintenberger.Ramification.Lower.Generator
public import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Stable finite ramification of the prescribed Kummer generator

The actual restriction of tau^(p^k) to diagonal level N has stable shifted
lower break d_k when N≥k+2. Its unshifted integral order is d_k+1.
The original spectral integer rings and every actual uniformizer are retained.
-/

@[expose] public section

noncomputable section

namespace FalseTateExtension

/-- The stable shifted lower break of the prescribed `p^k`-th Kummer power. -/
def kummerRamificationBreak (p k : ℕ) : ℕ :=
  1 + 2 * (p - 1) * ∑ j ∈ Finset.range (k + 1), p ^ (2 * j)

lemma kummerRamificationBreak_zero (p : ℕ) (hp : 1 ≤ p) :
    kummerRamificationBreak p 0 = 2 * p - 1 := by
  simp [kummerRamificationBreak]
  omega

lemma kummerRamificationBreak_succ (p k : ℕ) :
    kummerRamificationBreak p (k + 1) =
      kummerRamificationBreak p k + 2 * (p - 1) * p ^ (2 * (k + 1)) := by
  simp only [kummerRamificationBreak, Finset.sum_range_succ]
  ring

/-- The closed formula is stated without truncated subtraction or division. -/
lemma kummerRamificationBreak_mul (p k : ℕ) (hp : 1 ≤ p) :
    (p + 1) * kummerRamificationBreak p k = 2 * p ^ (2 * k + 2) + (p - 1) := by
  have hp' : p - 1 + 1 = p := Nat.sub_add_cancel hp
  induction k with
  | zero =>
      simp only [kummerRamificationBreak, Finset.sum_range_one, mul_zero, pow_zero,
        mul_one, zero_add]
      nlinarith
  | succ k ih =>
      rw [kummerRamificationBreak_succ]
      have hexp : 2 * (k + 1) = 2 * k + 2 := by omega
      rw [hexp]
      rw [show p ^ (2 * k + 2 + 2) = p ^ (2 * k + 2) * p ^ 2 from pow_add ..]
      have hfactor : (p + 1) * (p - 1) + 1 = p ^ 2 := by
        nlinarith [congrArg (fun n => (p + 1) * n) hp']
      have hmul := congrArg (fun n => 2 * p ^ (2 * k + 2) * n) hfactor
      nlinarith [hmul]

lemma kummerRamificationBreak_pos (p k : ℕ) : 0 < kummerRamificationBreak p k := by
  unfold kummerRamificationBreak
  omega

lemma kummerRamificationBreak_real (p k : ℕ) (hp : 1 ≤ p) :
    (kummerRamificationBreak p k : ℝ) =
      (2 * (p : ℝ) ^ (2 * k + 2) + p - 1) / (p + 1) := by
  have h := congrArg (fun n : ℕ => (n : ℝ)) (kummerRamificationBreak_mul p k hp)
  push_cast [Nat.cast_sub hp] at h
  apply (eq_div_iff (by positivity : (p : ℝ) + 1 ≠ 0)).2
  nlinarith [h]

lemma kummerRamificationBreak_recurrence (p k : ℕ) (hp : 1 ≤ p) :
    kummerRamificationBreak p (k + 1) + (p - 1) ^ 2 =
      p ^ 2 * kummerRamificationBreak p k := by
  have h := kummerRamificationBreak_mul p k hp
  have hp' : p - 1 + 1 = p := Nat.sub_add_cancel hp
  rw [kummerRamificationBreak_succ]
  have hexp : 2 * (k + 1) = 2 * k + 2 := by omega
  rw [hexp]
  have hmul := congrArg (fun n => (p - 1) * n) h
  have hsub := congrArg (fun n => (p + 1) * kummerRamificationBreak p k * n) hp'
  nlinarith [hmul, hsub]

lemma kummerRamificationBreak_mono (p : ℕ) : Monotone (kummerRamificationBreak p) := by
  apply monotone_nat_of_le_succ
  intro k
  rw [kummerRamificationBreak_succ]
  omega

lemma kummerRamificationBreak_lower (p k : ℕ) (hp : 1 ≤ p) :
    p - 1 ≤ kummerRamificationBreak p k := by
  have h := kummerRamificationBreak_mono p (Nat.zero_le k)
  rw [kummerRamificationBreak_zero p hp] at h
  omega

lemma kummerRamificationBreak_growth (p k : ℕ) (hp : 2 ≤ p) :
    (p + 1) * kummerRamificationBreak p k ≤ kummerRamificationBreak p (k + 1) := by
  have hd := kummerRamificationBreak_lower p k (by omega)
  have he := kummerRamificationBreak_recurrence p k (by omega)
  have hc : (p + 1) + (p - 1) ≤ p ^ 2 := by
    have hs : p - 1 + 1 = p := Nat.sub_add_cancel (by omega)
    nlinarith [Nat.mul_le_mul_left p hp]
  have hc' := Nat.mul_le_mul_right (kummerRamificationBreak p k) hc
  have hd' := Nat.mul_le_mul_left (p - 1) hd
  nlinarith [hc', hd']

lemma kummerRamificationBreak_strictMono (p : ℕ) (hp : 2 ≤ p) :
    StrictMono (kummerRamificationBreak p) := by
  apply strictMono_nat_of_lt_succ
  intro k
  have h := kummerRamificationBreak_growth p k hp
  have hd := kummerRamificationBreak_pos p k
  nlinarith

lemma kummerRamificationBreak_succ_dvd (p k : ℕ) [Fact p.Prime] :
    p ∣ kummerRamificationBreak p k + 1 := by
  have hp := (Fact.out : p.Prime).one_le
  have h := congrArg (fun n : ℕ => (n : ZMod p)) (kummerRamificationBreak_mul p k hp)
  have he : 2 * k + 2 ≠ 0 := by omega
  push_cast [Nat.cast_sub hp] at h
  simp only [ZMod.natCast_self, zero_add, one_mul, zero_pow he, mul_zero] at h
  apply (ZMod.natCast_eq_zero_iff _ _).mp
  push_cast
  linear_combination h

lemma kummerRamificationBreak_tendsto_real (p : ℕ) (hp : 2 ≤ p) :
    Filter.Tendsto (fun k => (kummerRamificationBreak p k : ℝ)) Filter.atTop Filter.atTop := by
  apply tendsto_atTop_of_geom_le
    (by exact_mod_cast kummerRamificationBreak_pos p 0)
    (show (1 : ℝ) < (p : ℝ) + 1 by exact_mod_cast (show 1 < p + 1 by omega))
  intro k
  exact_mod_cast kummerRamificationBreak_growth p k hp

/-- The next integer table entry lies at least one lower unit beyond the break. -/
lemma kummerRamificationBreak_add_one_le_integer (p k : ℕ) (hp : 3 ≤ p) :
    (kummerRamificationBreak p k : ℝ) + 1 ≤
      ((p : ℝ) - 1) * ((p : ℝ) ^ (2 * (k + 1) + 1) + 1) / ((p : ℝ) + 1) := by
  have hpR : (3 : ℝ) ≤ p := by exact_mod_cast hp
  have hgap :
      ((p : ℝ) - 1) * ((p : ℝ) ^ (2 * (k + 1) + 1) + 1) / ((p : ℝ) + 1) =
        kummerRamificationBreak p k + ((p : ℝ) - 2) * (p : ℝ) ^ (2 * (k + 1)) := by
    rw [kummerRamificationBreak_real p k (by omega),
      show 2 * (k + 1) = 2 * k + 2 by omega, pow_succ]
    field_simp
    ring
  rw [hgap]
  have hpow : (1 : ℝ) ≤ (p : ℝ) ^ (2 * (k + 1)) := one_le_pow₀ (by linarith)
  nlinarith

section ActualGenerator

open IsDiscreteValuationRing FontaineWintenberger

variable (p : ℕ) [Fact p.Prime]
variable (π : 𝒪[ℚ_[p]])
variable [hp₂ : Fact (p ≠ 2)] [hπ : Fact (Irreducible π)]

/-- The ordinary finite restriction of the prescribed original generator power. -/
def kummerTauFinite (N k : ℕ) :
    (falseTateLayer p (π : ℚ_[p]) N N) ≃ₐ[ℚ_[p]]
      (falseTateLayer p (π : ℚ_[p]) N N) :=
  infiniteLayerRestriction p (π : ℚ_[p]) N
    ((tau p π).val ^ (p ^ k))

/-- Powers in the actual character kernel have their prescribed additive coordinate. -/
lemma padicKummerExponent_tau_pow (m : ℕ) :
    padicKummerExponent p (π : ℚ_[p])
      ((tau p π).val ^ m) = m := by
  change (fullKummerKernelMulEquiv p π ((tau p π) ^ m)).toAdd = _
  rw [map_pow]
  change m • padicKummerExponent p (π : ℚ_[p]) (tau p π).val = _
  rw [padicKummerExponent_tau]
  simp

/-- Under the checked finite affine isomorphism the actual restriction is
the translation by `p^k`; the unit coordinate is exactly one. -/
lemma finiteDiagonalGaloisEquiv_kummerTauFinite (N k : ℕ) :
    finiteDiagonalGaloisEquiv_padic p π N (kummerTauFinite p π N k) =
      SemidirectProduct.inl (Multiplicative.ofAdd (p ^ k : ZMod (p ^ N))) := by
  apply SemidirectProduct.ext
  · apply congrArg Multiplicative.ofAdd
    change finiteKummerExponent p (π : ℚ_[p]) N
      (infiniteLayerRestriction p (π : ℚ_[p]) N ((tau p π).val ^ (p ^ k))) = _
    rw [← padicKummerExponent_toZModPow, padicKummerExponent_tau_pow]
    simp
  · rw [finiteDiagonalGaloisEquiv_padic_right]
    change finiteCyclotomicCharacter p (π : ℚ_[p]) N
      (infiniteLayerRestriction p (π : ℚ_[p]) N ((tau p π).val ^ (p ^ k))) = 1
    rw [← padicCyclotomicCharacter_toZModPow, map_pow]
    have hχ : padicCyclotomicCharacter p (π : ℚ_[p]) (tau p π).val = 1 :=
      (tau p π).property
    simp [hχ]

omit [Fact p.Prime] hp₂ in
lemma primePower_mem_finiteTranslationSubgroup (N k : ℕ) :
    Multiplicative.ofAdd (p ^ k : ZMod (p ^ N)) ∈ finiteTranslationSubgroup p N k := by
  refine ⟨Multiplicative.ofAdd (1 : ZMod (p ^ N)), ?_⟩
  change Multiplicative.ofAdd ((p ^ k) • (1 : ZMod (p ^ N))) = _
  simp [nsmul_eq_mul]

omit hp₂ in
lemma primePower_notMem_finiteTranslationSubgroup (N k : ℕ) (hk : k < N) :
    Multiplicative.ofAdd (p ^ k : ZMod (p ^ N)) ∉ finiteTranslationSubgroup p N (k + 1) := by
  rintro ⟨a, ha⟩
  let ρ := ZMod.castHom (Nat.pow_dvd_pow p (show k + 1 ≤ N by omega))
    (ZMod (p ^ (k + 1)))
  have h := congrArg (fun a : Multiplicative (ZMod (p ^ N)) => ρ a.toAdd) ha
  change ρ ((p ^ (k + 1)) • a.toAdd) = ρ (p ^ k : ZMod (p ^ N)) at h
  rw [map_nsmul, nsmul_eq_mul] at h
  have hz : ((p ^ (k + 1) : ℕ) : ZMod (p ^ (k + 1))) = 0 := ZMod.natCast_self _
  have h0 : (p ^ k : ZMod (p ^ (k + 1))) = 0 := by
    simpa only [map_pow, map_natCast, hz, zero_mul] using h.symm
  have hd := (ZMod.natCast_eq_zero_iff (p ^ k) (p ^ (k + 1))).mp (by
    simpa only [Nat.cast_pow] using h0)
  have := (Nat.pow_dvd_pow_iff_le_right (Fact.out : p.Prime).one_lt).mp hd
  omega

/-- The original generator power belongs to the actual lower group at its break. -/
lemma kummerTauFinite_mem_lower_break (n k : ℕ) (hk : k + 1 ≤ n) :
    kummerTauFinite p π (n + 1) k ∈
      lowerRamificationGroupReal
        ((falseTateLayer p (π : ℚ_[p]) (n + 1) (n + 1)) ≃ₐ[ℚ_[p]] _)
        (IsLocalRing.maximalIdeal
          (spectralIntegerRing (ℚ_[p]) (falseTateLayer p (π : ℚ_[p]) (n + 1) (n + 1))))
        (kummerRamificationBreak p k) := by
  let e := finiteDiagonalGaloisEquiv_padic p π (n + 1)
  have htable := lowerRamificationGroupReal_falseTate_fractional π n (k + 1)
    (by omega) hk
  have hd : (kummerRamificationBreak p k : ℝ) =
      (2 * (p : ℝ) ^ (2 * (k + 1)) + (p : ℝ) - 1) / ((p : ℝ) + 1) := by
    simpa only [show 2 * (k + 1) = 2 * k + 2 by omega] using
      kummerRamificationBreak_real p k (Fact.out : p.Prime).one_le
  rw [← hd] at htable
  simp only [Nat.add_sub_cancel] at htable
  have hm : e (kummerTauFinite p π (n + 1) k) ∈
      (lowerRamificationGroupReal
        ((falseTateLayer p (π : ℚ_[p]) (n + 1) (n + 1)) ≃ₐ[ℚ_[p]] _)
        (IsLocalRing.maximalIdeal
          (spectralIntegerRing (ℚ_[p]) (falseTateLayer p (π : ℚ_[p]) (n + 1) (n + 1))))
        (kummerRamificationBreak p k)).map e.toMonoidHom := by
    rw [htable]
    dsimp only [e]
    rw [finiteDiagonalGaloisEquiv_kummerTauFinite]
    exact (show _ ∈ finiteAffineSubgroup p (n + 1) k
      (finiteUnitSubgroup p (n + 1) (k + 1 + 1)) from
      ⟨primePower_mem_finiteTranslationSubgroup p (n + 1) k, Subgroup.one_mem _⟩)
  obtain ⟨g, hg, he⟩ := hm
  have hge : g = kummerTauFinite p π (n + 1) k := e.injective he
  simpa only [lowerRamificationGroupReal, Int.ceil_natCast, hge, SetLike.mem_coe] using hg

/-- Immediately beyond that break the actual restriction leaves the lower group. -/
lemma kummerTauFinite_notMem_lower_break_add_one (n k : ℕ) (hk : k + 1 ≤ n) :
    kummerTauFinite p π (n + 1) k ∉
      lowerRamificationGroupReal
        ((falseTateLayer p (π : ℚ_[p]) (n + 1) (n + 1)) ≃ₐ[ℚ_[p]] _)
        (IsLocalRing.maximalIdeal
          (spectralIntegerRing (ℚ_[p]) (falseTateLayer p (π : ℚ_[p]) (n + 1) (n + 1))))
        ((kummerRamificationBreak p k : ℝ) + 1) := by
  intro hg
  have hp3 : 3 ≤ p := by have := (Fact.out : p.Prime).two_le; have := hp₂.out; omega
  have htable := lowerRamificationGroupReal_falseTate_fractional_integer π n (k + 1) hk
    (t := (kummerRamificationBreak p k : ℝ) + 1)
    (by rw [kummerRamificationBreak_real p k (by omega)];
        simp only [show 2 * (k + 1) = 2 * k + 2 by omega]; linarith)
    (kummerRamificationBreak_add_one_le_integer p k hp3)
  have hm := Subgroup.mem_map_of_mem
    (finiteDiagonalGaloisEquiv_padic p π (n + 1)).toMonoidHom hg
  rw [htable] at hm
  change finiteDiagonalGaloisEquiv_padic p π (n + 1)
    (kummerTauFinite p π (n + 1) k) ∈ _ at hm
  rw [finiteDiagonalGaloisEquiv_kummerTauFinite] at hm
  exact primePower_notMem_finiteTranslationSubgroup p (n + 1) k (by omega) hm.1

/-- The unshifted order on the original spectral integer ring is `d_k + 1`. -/
theorem ramificationOrder_kummerTauFinite_succ (n k : ℕ) (hk : k + 1 ≤ n) :
    ramificationOrder
      (R := spectralIntegerRing (ℚ_[p]) (falseTateLayer p (π : ℚ_[p]) (n + 1) (n + 1)))
      ((falseTateLayer p (π : ℚ_[p]) (n + 1) (n + 1)) ≃ₐ[ℚ_[p]] _)
      (kummerTauFinite p π (n + 1) k) = (kummerRamificationBreak p k + 1 : ℕ) := by
  let D := falseTateLayer p (π : ℚ_[p]) (n + 1) (n + 1)
  let G := D ≃ₐ[ℚ_[p]] D
  let O := spectralIntegerRing (ℚ_[p]) D
  have hm := kummerTauFinite_mem_lower_break p π n k hk
  have hn := kummerTauFinite_notMem_lower_break_add_one p π n k hk
  have hlo : (kummerRamificationBreak p k + 1 : ℕ∞) ≤
      ramificationOrder (R := O) G (kummerTauFinite p π (n + 1) k) := by
    simpa [lowerRamificationGroupReal, mem_lowerRamificationGroup_iff_le_order] using hm
  have hhi : ¬ (kummerRamificationBreak p k + 1 : ℕ∞) + 1 ≤
      ramificationOrder (R := O) G (kummerTauFinite p π (n + 1) k) := by
    have hto : ((kummerRamificationBreak p k : ℤ) + 2).toNat =
        kummerRamificationBreak p k + 2 := by omega
    simpa [lowerRamificationGroupReal, mem_lowerRamificationGroup_iff_le_order,
      hto, Nat.cast_add, add_assoc, show (1 : ℕ∞) + 1 = 2 by norm_num] using hn
  apply le_antisymm
  · exact (ENat.lt_add_one_iff (by simp)).mp (lt_of_not_ge hhi)
  · exact hlo

/-- The stable order at every diagonal level `N ≥ k + 2`, with the true cutoff. -/
theorem ramificationOrder_kummerTauFinite (N k : ℕ) (hk : k + 2 ≤ N) :
    ramificationOrder
      (R := spectralIntegerRing (ℚ_[p]) (falseTateLayer p (π : ℚ_[p]) N N))
      ((falseTateLayer p (π : ℚ_[p]) N N) ≃ₐ[ℚ_[p]] _)
      (kummerTauFinite p π N k) = (kummerRamificationBreak p k + 1 : ℕ) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show N ≠ 0 by omega)
  exact ramificationOrder_kummerTauFinite_succ p π n k (by omega)

/-- Every actual uniformizer attains that same integral displacement order. -/
theorem addVal_kummerTauFinite_uniformizer (N k : ℕ) (hk : k + 2 ≤ N)
    {ϖ : spectralIntegerRing (ℚ_[p]) (falseTateLayer p (π : ℚ_[p]) N N)}
    (hϖ : Irreducible ϖ) :
    addVal (spectralIntegerRing (ℚ_[p]) (falseTateLayer p (π : ℚ_[p]) N N))
      (kummerTauFinite p π N k • ϖ - ϖ) = (kummerRamificationBreak p k + 1 : ℕ) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show N ≠ 0 by omega)
  let D := falseTateLayer p (π : ℚ_[p]) (n + 1) (n + 1)
  have hgen := extensionValuationSubring_adjoin_uniformizer_eq_top (ℚ_[p]) D
    (spectralValuation (ℚ_[p]) D)
    (falseTateLayer_spectral_ramificationIdx p π n) hϖ
  rw [← ramificationOrder_eq_generator (D ≃ₐ[ℚ_[p]] D) hgen]
  exact ramificationOrder_kummerTauFinite_succ p π n k (by omega)

/-- Exact normalized displacement on the original finite field, for every uniformizer. -/
theorem normalizedValuation_kummerTauFinite_displacement (N k : ℕ) (hk : k + 2 ≤ N)
    {ϖ : spectralIntegerRing (ℚ_[p]) (falseTateLayer p (π : ℚ_[p]) N N)}
    (hϖ : Irreducible ϖ) :
    (maximalIdeal (spectralIntegerRing (ℚ_[p]) (falseTateLayer p (π : ℚ_[p]) N N))).valuation
      (falseTateLayer p (π : ℚ_[p]) N N)
      (kummerTauFinite p π N k (ϖ : falseTateLayer p (π : ℚ_[p]) N N) - ϖ) =
      WithZero.exp (-(kummerRamificationBreak p k + 1 : ℕ) : ℤ) := by
  let D := falseTateLayer p (π : ℚ_[p]) N N
  let O := spectralIntegerRing (ℚ_[p]) D
  have hv : (maximalIdeal O).valuation D
      ((kummerTauFinite p π N k • ϖ - ϖ : O) : D) =
      WithZero.exp (-(kummerRamificationBreak p k + 1 : ℕ) : ℤ) := by
    change (maximalIdeal O).valuation D
      (algebraMap O D (kummerTauFinite p π N k • ϖ - ϖ)) = _
    rw [IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap,
      intValuation_maximalIdeal, addVal_kummerTauFinite_uniformizer p π N k hk hϖ]
    rw [ENat.recTopCoe_natCast]
    simp [← WithZero.exp_eq_coe_ofAdd]
  have hc : ((kummerTauFinite p π N k • ϖ - ϖ : O) : D) =
      kummerTauFinite p π N k (ϖ : D) - ϖ := by
    change ((kummerTauFinite p π N k • ϖ : O) : D) - (ϖ : D) = _
    rw [coe_spectralIntegerRing_galois_smul]
  rw [hc] at hv
  exact hv

/-- The normalized relative displacement has the source's shifted order `d_k`. -/
theorem normalizedValuation_kummerTauFinite_div_sub_one (N k : ℕ) (hk : k + 2 ≤ N)
    {ϖ : spectralIntegerRing (ℚ_[p]) (falseTateLayer p (π : ℚ_[p]) N N)}
    (hϖ : Irreducible ϖ) :
    (maximalIdeal (spectralIntegerRing (ℚ_[p]) (falseTateLayer p (π : ℚ_[p]) N N))).valuation
      (falseTateLayer p (π : ℚ_[p]) N N)
      (kummerTauFinite p π N k (ϖ : falseTateLayer p (π : ℚ_[p]) N N) / ϖ - 1) =
      WithZero.exp (-(kummerRamificationBreak p k : ℤ)) := by
  let D := falseTateLayer p (π : ℚ_[p]) N N
  let O := spectralIntegerRing (ℚ_[p]) D
  have hne : (ϖ : D) ≠ 0 := fun h => hϖ.ne_zero (Subtype.ext h)
  have hu : (maximalIdeal O).valuation D (ϖ : D) = WithZero.exp (-1 : ℤ) := by
    change (maximalIdeal O).valuation D (algebraMap O D ϖ) = _
    rw [IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap]
    exact (maximalIdeal O).intValuation_singleton hϖ.ne_zero hϖ.maximalIdeal_eq
  have he : kummerTauFinite p π N k (ϖ : D) / ϖ - 1 =
      (kummerTauFinite p π N k (ϖ : D) - ϖ) / ϖ := by
    field_simp
  rw [he, map_div₀, normalizedValuation_kummerTauFinite_displacement p π N k hk hϖ, hu]
  rw [← WithZero.exp_sub]
  congr 1
  push_cast
  ring

end ActualGenerator

end FalseTateExtension
