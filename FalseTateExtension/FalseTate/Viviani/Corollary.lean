/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FalseTateExtension.FalseTate.FiniteGaloisGroup
public import FalseTateExtension.FalseTate.Viviani.Filtration
public import FalseTateExtension.FalseTate.Viviani.Preliminaries
public import FalseTateExtension.Kummer.APF
public import FontaineWintenberger.APF.Finite.ConstantIndex
public import FontaineWintenberger.Ramification.Herbrand.Interval
public import FontaineWintenberger.Ramification.Upper.Transport
public import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# Viviani's Corollary 6.10 for an integer parameter

Let `p ≠ 2` and let `a` be an integer with `v_p(a) = 1`, so that `a` is a uniformizer of `ℚ_p`.
For `D = ℚ_p(a^{1/p^{n+1}}, ζ_{p^{n+1}})` and `G = Gal(D/ℚ_p) ≅ ℤ/p^{n+1} ⋊ (ℤ/p^{n+1})ˣ`:

* the upper ramification groups are `G^u = ⊤` for `-1 ≤ u ≤ 0`, on `(r, r + 1]` (`r ≤ n`)
  `G^u = p^{d(u)} ℤ/p^{n+1} ⋊ (1 + p^{r+1})` where `d(u)` counts the thresholds
  `j + 1 + 1/(p-1) < u`, and `G^u = ⊥` for `u > n + 1 + 1/(p-1)`;
* the inverse Herbrand function takes the values `ψ(i + 1/(p-1)) = (2p^{2i} + p - 1)/(p+1)`,
  `ψ(i + 1) = (p-1)(p^{2i+1} + 1)/(p+1)` and
  `ψ(n + 1 + 1/(p-1)) = (p^{2n+2} + p^{2n} + p - 1)/(p+1)`;
* at these lower breaks `G_t` is `p^{i-1} ℤ/p^{n+1} ⋊ (1 + p^{i+1})`, respectively
  `p^i ℤ/p^{n+1} ⋊ (1 + p^{i+1})`, and `G_t = ⊥` beyond the last break.

The value at the integer breaks corrects the statement of Viviani's Corollary 6.10 (the
exponent is `2i + 1`, not `2i`), see FalseTateLift, Remark 5.2. The general uniformizer
versions are in `Viviani/Filtration`.

## Main results

* `finiteUpperAffine_integerParameter_interval`, `upperRamificationGroup_integerParameter_eq_bot`
* `inverseHerbrandFunction_integerParameter_fractional`,
  `inverseHerbrandFunction_integerParameter_integer`,
  `inverseHerbrandFunction_integerParameter_final`
* `lowerRamificationGroupReal_integerParameter_fractional`,
  `lowerRamificationGroupReal_integerParameter_integer`,
  `lowerRamificationGroupReal_integerParameter_eq_bot`

## Notation

The local notations `D`, `G` and `O` denote the diagonal layer, its Galois group over `ℚ_[p]`
and its valuation ring, respectively.

## References

* [Viviani, *Ramification groups and Artin conductors of radical extensions of
  ℚ*](https://doi.org/10.5802/jtnb.470), Corollary 6.10; FalseTateLift, Remark 5.2.
-/

@[expose] public section

noncomputable section

namespace FalseTateExtension

open IsDiscreteValuationRing FontaineWintenberger

variable (p : ℕ) [Fact p.Prime]

section IntegerParameter

/-- An integer `a` with `v_p(a) = 1` is irreducible in the valuation ring of `ℚ_[p]`. -/
theorem irreducible_integerParameter (a : ℤ) (ha : padicValInt p a = 1) :
    Irreducible (a : 𝒪[ℚ_[p]]) := by
  have haZ : a ≠ 0 := by
    rintro rfl
    simp only [padicValInt.zero] at ha
    omega
  have ha0 : (a : ℤ_[p]) ≠ 0 := Int.cast_ne_zero.mpr haZ
  have hv : (a : ℤ_[p]).valuation = 1 := by
    have h : ((a : ℤ_[p]).valuation : ℤ) = 1 := by
      rw [← PadicInt.valuation_coe, PadicInt.coe_intCast, Padic.valuation_intCast, ha]
      rfl
    exact_mod_cast h
  have hass : Associated (a : ℤ_[p]) (p : ℤ_[p]) := by
    rw [PadicInt.unitCoeff_spec ha0, hv, pow_one]
    exact associated_unit_mul_left _ _ (PadicInt.unitCoeff ha0).isUnit
  have hirr := hass.irreducible_iff.mpr PadicInt.irreducible_p
  apply (MulEquiv.irreducible_iff (padicValuationSubringEquiv p)).mp
  simpa only [map_intCast] using hirr

/-- An integer `a` with `v_p(a) = 1` is a uniformizer of `ℚ_[p]`. -/
instance fact_irreducible_integerParameter (a : ℤ) [ha : Fact (padicValInt p a = 1)] :
    Fact (Irreducible (a : 𝒪[ℚ_[p]])) :=
  ⟨irreducible_integerParameter p a ha.out⟩

variable [Fact (p ≠ 2)] (a : ℤ) [Fact (padicValInt p a = 1)] (n : ℕ)

local notation "D" => falseTateLayer p (a : ℚ_[p]) (n + (1 : ℕ)) (n + (1 : ℕ))
local notation "G" => D ≃ₐ[ℚ_[p]] D
local notation "O" => spectralIntegerRing ℚ_[p] D

/-- On `(r, r + 1]`, `r ≤ n`, the upper ramification group of `ℚ_p(a^{1/p^{n+1}}, ζ_{p^{n+1}})`,
read in `ℤ/p^{n+1} ⋊ (ℤ/p^{n+1})ˣ`, is `p^d ℤ/p^{n+1} ⋊ (1 + p^{r+1})` with
`d = radicalTranslationDepth p (n+1) u`. -/
theorem finiteUpperAffine_integerParameter_interval (r : ℕ) (hr : r ≤ n) {u : ℝ}
    (hu0 : (r : ℝ) < u) (hu1 : u ≤ (r : ℝ) + 1) :
    finiteUpperAffineGroup (a : 𝒪[ℚ_[p]]) n u =
      finiteAffineSubgroup p (n + 1) (radicalTranslationDepth p (n + 1) u)
        (finiteUnitSubgroup p (n + 1) (r + 1)) :=
  finiteUpperAffine_eq_interval (a : 𝒪[ℚ_[p]]) n r hr hu0 hu1

/-- For `-1 ≤ u ≤ 0` the upper ramification group is the whole Galois group. -/
theorem upperRamificationGroup_integerParameter_eq_top {u : ℝ} (hu : -1 ≤ u) (hu0 : u ≤ 0) :
    upperRamificationGroup (R := O) G u = ⊤ :=
  upperRamificationGroup_falseTate_nonpos (a : 𝒪[ℚ_[p]]) n hu hu0

/-- For `u > n + 1 + 1/(p-1)` the upper ramification group is trivial. -/
theorem upperRamificationGroup_integerParameter_eq_bot {u : ℝ}
    (hu : (n : ℝ) + 1 + 1 / ((p : ℝ) - 1) < u) :
    upperRamificationGroup (R := O) G u = ⊥ :=
  upperRamificationGroup_falseTate_eq_bot (a : 𝒪[ℚ_[p]]) n hu

/-- `ψ(i + 1/(p-1)) = (2 p^{2i} + p - 1)/(p + 1)` for `i ≤ n`. -/
theorem inverseHerbrandFunction_integerParameter_fractional (i : ℕ) (hi : i ≤ n) :
    inverseHerbrandFunction (R := O) G ((i : ℝ) + 1 / ((p : ℝ) - 1)) =
      (2 * (p : ℝ) ^ (2 * i) + (p : ℝ) - 1) / ((p : ℝ) + 1) :=
  inverseHerbrandFunction_falseTate_fractional (a : 𝒪[ℚ_[p]]) n i hi

/-- `ψ(i + 1) = (p - 1)(p^{2i+1} + 1)/(p + 1)` for `i ≤ n`. -/
theorem inverseHerbrandFunction_integerParameter_integer (i : ℕ) (hi : i ≤ n) :
    inverseHerbrandFunction (R := O) G ((i : ℝ) + 1) =
      ((p : ℝ) - 1) * ((p : ℝ) ^ (2 * i + 1) + 1) / ((p : ℝ) + 1) :=
  inverseHerbrandFunction_falseTate_integer (a : 𝒪[ℚ_[p]]) n i hi

/-- `ψ(n + 1 + 1/(p-1)) = (p^{2n+2} + p^{2n} + p - 1)/(p + 1)`, the last break. -/
theorem inverseHerbrandFunction_integerParameter_final :
    inverseHerbrandFunction (R := O) G ((n : ℝ) + 1 + 1 / ((p : ℝ) - 1)) =
      ((p : ℝ) ^ (2 * (n + 1)) + (p : ℝ) ^ (2 * n) + (p : ℝ) - 1) / ((p : ℝ) + 1) :=
  inverseHerbrandFunction_falseTate_final (a : 𝒪[ℚ_[p]]) n

/-- At the lower break `ψ(i + 1/(p-1))`, `1 ≤ i ≤ n`, the lower ramification group is
`p^{i-1} ℤ/p^{n+1} ⋊ (1 + p^{i+1})`. -/
theorem lowerRamificationGroupReal_integerParameter_fractional (i : ℕ) (hi : 1 ≤ i)
    (hin : i ≤ n) :
    (lowerRamificationGroupReal G (IsLocalRing.maximalIdeal O)
      ((2 * (p : ℝ) ^ (2 * i) + (p : ℝ) - 1) / ((p : ℝ) + 1))).map
        (finiteDiagonalGaloisEquivPadic p (a : 𝒪[ℚ_[p]]) (n + 1)).toMonoidHom =
      finiteAffineSubgroup p (n + 1) (i - 1) (finiteUnitSubgroup p (n + 1) (i + 1)) :=
  lowerRamificationGroupReal_falseTate_fractional (a : 𝒪[ℚ_[p]]) n i hi hin

/-- At the lower break `ψ(i + 1)`, `i ≤ n`, the lower ramification group is
`p^i ℤ/p^{n+1} ⋊ (1 + p^{i+1})`. -/
theorem lowerRamificationGroupReal_integerParameter_integer (i : ℕ) (hi : i ≤ n) :
    (lowerRamificationGroupReal G (IsLocalRing.maximalIdeal O)
      (((p : ℝ) - 1) * ((p : ℝ) ^ (2 * i + 1) + 1) / ((p : ℝ) + 1))).map
        (finiteDiagonalGaloisEquivPadic p (a : 𝒪[ℚ_[p]]) (n + 1)).toMonoidHom =
      finiteAffineSubgroup p (n + 1) i (finiteUnitSubgroup p (n + 1) (i + 1)) :=
  lowerRamificationGroupReal_falseTate_integer (a : 𝒪[ℚ_[p]]) n i hi

/-- Beyond the last lower break the lower ramification group is trivial. -/
theorem lowerRamificationGroupReal_integerParameter_eq_bot {t : ℝ}
    (ht : ((p : ℝ) ^ (2 * (n + 1)) + (p : ℝ) ^ (2 * n) + (p : ℝ) - 1) / ((p : ℝ) + 1) < t) :
    lowerRamificationGroupReal G (IsLocalRing.maximalIdeal O) t = ⊥ :=
  lowerRamificationGroupReal_falseTate_eq_bot (a : 𝒪[ℚ_[p]]) n ht

end IntegerParameter

end FalseTateExtension
end
