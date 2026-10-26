/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FalseTateExtension.Kummer.Eisenstein
public import FontaineWintenberger.APF.BaseChange.Basic
public import FontaineWintenberger.APF.Elementary.PrimeDegree
public import FontaineWintenberger.APF.Galois.Union
public import FontaineWintenberger.APF.Strict
public import FontaineWintenberger.APF.Tower.TotallyRamified

/-!
# The ramification profile of one step of the Kummer tower

Let `K` be a complete discretely valued field of characteristic zero with perfect residue
field, `π` a uniformizer and `e_K = v_K(p)`. The step `F_n = K(π^{1/p^n}) ⊆ F_{n+1}` is totally
ramified of degree `p` with different exponent `p^{n+1} e_K + p - 1`, so it has a single
ramification break at `t_n = p^{n+1} e_K / (p - 1)`: its APF index is `1` for `u ≤ t_n` and `p`
for `u > t_n`, and its inverse Herbrand function is `u` for `u ≤ t_n` and `t_n + p (u - t_n)`
above. By the transitivity of the Herbrand functions, the index and inverse Herbrand function
of `F_{n+1}/K` are those of `F_n/K` composed with this step profile.

## Main results

* `radicalLayer_step_own_ramificationIdx`, `radicalLayer_step_own_different_order`: the step
  has ramification index `p` and different exponent `p^{n+1} e_K + p - 1`.
* `radicalLayer_step_apfIndex`: the APF index of the step is `1` up to `t_n` and `p` beyond.
* `radicalLayer_step_apfPsi`: the inverse Herbrand function of the step.
* `radicalLayer_apfIndex_succ`, `radicalLayer_apfPsi_succ`: the index and inverse Herbrand
  function of `F_{n+1}/K` in terms of those of `F_n/K`.

## Notation

The local notations `F₀` and `F₁` denote the consecutive layers `K(π^{1/p^n})` and
`K(π^{1/p^{n+1}})`, and `O₀` and `O₁` their spectral integer rings over `K`.

## References

* [J.-P. Serre, *Local Fields*](https://doi.org/10.1007/978-1-4757-5673-9), Chapter IV §1, §3.
* [J.-P. Wintenberger, *Le corps des normes de certaines extensions infinies de corps locaux;
  applications*](https://doi.org/10.24033/asens.1440), §1.2.3.
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
local notation "F₁" => radicalLayer (K := K) p (π : K) (n + (1 : ℕ))
local notation "O₀" => spectralIntegerRing K F₀
local notation "O₁" => spectralIntegerRing K F₁

/-- The spectral norm on `F_n = K(π^{1/p^n})`. -/
noncomputable local instance kummerBaseNormedField : NontriviallyNormedField F₀ :=
  spectralNorm.nontriviallyNormedField K F₀

/-- `F_n` is a normed `K`-algebra for the spectral norm. -/
noncomputable local instance kummerBaseNormedAlgebra : NormedAlgebra K F₀ :=
  spectralNorm.normedAlgebra K F₀

/-- The spectral norm on `F_n` is nonarchimedean. -/
local instance kummerBaseUltrametric : IsUltrametricDist F₀ :=
  IsUltrametricDist.isUltrametricDist_iff_isNonarchimedean_norm.mpr
    (isNonarchimedean_spectralNorm (K := K) (L := F₀))

/-- `F_n` is complete for the spectral norm. -/
local instance kummerBaseComplete : CompleteSpace F₀ := spectralNorm.completeSpace K F₀

/-- The valuation ring of `F_n` is a discrete valuation ring. -/
local instance kummerBaseDVR : IsDiscreteValuationRing
    (NormedField.valuation (K := F₀)).valuationSubring :=
  normedAlgebra_unitBall_isDiscreteValuationRing K F₀

/-- `F_n` is a complete discretely valued field. -/
local instance kummerBaseCompleteDiscreteValuedField : IsCompleteDiscreteValuedField F₀ where

/-- The residue field of `F_n` is perfect. -/
local instance kummerBasePerfect : PerfectField (IsLocalRing.ResidueField
    (NormedField.valuation (K := F₀)).valuationSubring) :=
  Algebra.IsAlgebraic.perfectField (𝓀[K])

/-- The algebra structure of `F_{n+1}` over `F_n`. -/
local instance kummerStepAlgebra : Algebra F₀ F₁ :=
  (IntermediateField.inclusion (radicalLayer_le_succ p (π : K) n)).toRingHom.toAlgebra

/-- `K ⊆ F_n ⊆ F_{n+1}` is a tower. -/
local instance kummerStepScalarTower : IsScalarTower K F₀ F₁ :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

/-- `F_{n+1}/F_n` is finite. -/
local instance kummerStepFinite : FiniteDimensional F₀ F₁ :=
  Module.Finite.right K F₀ F₁

/-- The spectral valuation of `F_{n+1}` over `K` extends that of `F_n` over `K`. -/
local instance kummerStepValuation :
    (spectralValuation K F₀).HasExtension (spectralValuation K F₁) :=
  spectralValuation_hasExtension_tower K (E := F₀) (L := F₁)

/-- The spectral valuation of `F_{n+1}` over `K` extends the valuation of `F_n`. -/
local instance kummerStepOwnValuation :
    (NormedField.valuation (K := F₀)).HasExtension (spectralValuation K F₁) where
  val_isEquiv_comap := by
    intro x y
    change spectralNorm K F₀ x ≤ spectralNorm K F₀ y ↔
      spectralNorm K F₁ (algebraMap F₀ F₁ x) ≤ spectralNorm K F₁ (algebraMap F₀ F₁ y)
    rw [← spectralNorm.eq_of_tower x, ← spectralNorm.eq_of_tower y]

include hπ n

omit [PerfectField (𝓀[K])] in
/-- `F_{n+1}/F_n` has ramification index `p`. -/
theorem radicalLayer_step_own_ramificationIdx :
    (IsLocalRing.maximalIdeal (spectralIntegerRing F₀ F₁)).ramificationIdx
      (NormedField.valuation (K := F₀)).valuationSubring = p := by
  have h := extensionValuationSubring_ramificationIdx_eq_spectral F₀ F₁
    (spectralValuation K F₁)
  change (IsLocalRing.maximalIdeal O₁).ramificationIdx O₀ = _ at h
  rw [← h]
  exact radicalLayer_step_ramificationIdx p π n

/-- The different exponent of `F_{n+1}/F_n` is `p^{n+1} e_K + p - 1`. -/
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

/-- The APF index of `F_{n+1}/F_n` at `u ≥ 0` is `1` for `u ≤ p^{n+1} e_K / (p - 1)` and `p`
beyond. -/
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

/-- The inverse Herbrand function of `F_{n+1}/F_n` is `u` for `u ≤ t = p^{n+1} e_K / (p - 1)`
and `t + p (u - t)` beyond. -/
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
local notation "F₁" => radicalLayer (K := K) p (π : K) (n + (1 : ℕ))

/-- The APF index of `F_{n+1}/K` at `u ≥ 0` is that of `F_n/K` times the index of
`F_{n+1}/F_n` at `ψ_{F_n/K}(u)`, which is `1` below `p^{n+1} e_K / (p - 1)` and `p` above. -/
theorem radicalLayer_apfIndex_succ [hπ : Fact (Irreducible π)]
    {u : ℝ} (hu : 0 ≤ u) :
    apfIndex K F₁ u = apfIndex K F₀ u *
      if apfPsi K F₀ u ≤ (p : ℝ) ^ (n + 1) * absoluteRamificationIdx p K / ((p : ℝ) - 1)
        then 1 else p := by
  rw [apfIndex_eq_mul_finiteBase_of_normedAlgebra K F₀ F₁ hu,
    radicalLayer_step_apfIndex p π n (hu.trans (IsAPF.le_apfPsi K F₀ u))]

/-- `ψ_{F_{n+1}/K} = ψ_{F_{n+1}/F_n} ∘ ψ_{F_n/K}`, with the step profile of
`radicalLayer_step_apfPsi`. -/
theorem radicalLayer_apfPsi_succ [hπ : Fact (Irreducible π)] (u : ℝ) :
    let t := (p : ℝ) ^ (n + 1) * absoluteRamificationIdx p K / ((p : ℝ) - 1)
    apfPsi K F₁ u =
      if apfPsi K F₀ u ≤ t then apfPsi K F₀ u
        else t + (p : ℝ) * (apfPsi K F₀ u - t) := by
  rw [← IsAPF.apfPsi_finiteBase_comp_of_normedAlgebra K F₀ F₁ u]
  exact radicalLayer_step_apfPsi p π n _

end Successor

end FalseTateExtension
end
