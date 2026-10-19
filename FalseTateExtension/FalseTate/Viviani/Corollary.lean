/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FalseTateExtension.FalseTate.Viviani.Filtration
public import FalseTateExtension.FalseTate.Viviani.Preliminaries
public import FalseTateExtension.Kummer.APF
public import FalseTateExtension.FalseTate.FiniteGaloisGroup
public import FontaineWintenberger.APF.Finite.ConstantIndex
public import FontaineWintenberger.Ramification.Herbrand.Interval
public import FontaineWintenberger.Ramification.Upper.Transport
public import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# Viviani's Corollary 6.10 for an integer parameter

For an integer `a` with `v_p(a) = 1`, the filtration of `ℚ_p(a^{1/p^{n+1}}, ζ_{p^{n+1}})/ℚ_p`.

## References

* Viviani, *Ramification groups and Artin conductors of radical extensions of ℚ*, Corollary 6.10;
  FalseTateLift, Remark 5.2.
-/

@[expose] public section

noncomputable section

namespace FalseTateExtension

open IsDiscreteValuationRing FontaineWintenberger

variable (p : ℕ) [Fact p.Prime]

section IntegerParameter

/-- The integer hypothesis v_p(a)=1 supplies the rational
valuation-ring uniformizer used by every preceding coordinate bridge. -/
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
  apply (MulEquiv.irreducible_iff (padicUnitBallEquiv p)).mp
  simpa only [map_intCast] using hirr

/-- An integer `a` with `v_p(a) = 1` is a uniformizer of `ℚ_[p]`. -/
instance fact_irreducible_integerParameter (a : ℤ) [ha : Fact (padicValInt p a = 1)] :
    Fact (Irreducible (a : 𝒪[ℚ_[p]])) :=
  ⟨irreducible_integerParameter p a ha.out⟩

/-- Viviani's hypothesis `v_p(a) = 1` on an integer parameter `a`: the upper ramification
groups of `ℚ_p(a^{1/p^{n+1}}, ζ_{p^{n+1}})` on `(r, r + 1]`. -/
theorem finiteUpperAffine_integerParameter_interval [Fact (p ≠ 2)] (a : ℤ)
    [Fact (padicValInt p a = 1)] (n r : ℕ) (hr : r ≤ n) {u : ℝ}
    (hu0 : (r : ℝ) < u) (hu1 : u ≤ (r : ℝ) + 1) :
    finiteUpperAffineGroup (a : 𝒪[ℚ_[p]]) n u =
      finiteAffineSubgroup p (n + 1) (radicalTranslationDepth p (n + 1) u)
        (finiteUnitSubgroup p (n + 1) (r + 1)) :=
  finiteUpperAffine_eq_interval (a : 𝒪[ℚ_[p]]) n r hr hu0 hu1

/-- The Herbrand table (Viviani, Corollary 6.10, with the correction of
FalseTateLift, Remark 5.2) for an integer parameter `a` with `v_p(a) = 1`. -/
theorem inverseHerbrandFunction_falseTate_integerParameter [Fact (p ≠ 2)] (a : ℤ)
    [Fact (padicValInt p a = 1)] (n i : ℕ) (hi : i ≤ n) :
    let D := falseTateLayer p (a : ℚ_[p]) (n + 1) (n + 1)
    let ψ := inverseHerbrandFunction (R := spectralIntegerRing ℚ_[p] D) (D ≃ₐ[ℚ_[p]] D)
    ψ ((i : ℝ) + 1 / ((p : ℝ) - 1)) =
        (2 * (p : ℝ) ^ (2 * i) + (p : ℝ) - 1) / ((p : ℝ) + 1) ∧
      ψ ((i : ℝ) + 1) =
        ((p : ℝ) - 1) * ((p : ℝ) ^ (2 * i + 1) + 1) / ((p : ℝ) + 1) ∧
      ψ ((n : ℝ) + 1 + 1 / ((p : ℝ) - 1)) =
        ((p : ℝ) ^ (2 * (n + 1)) + (p : ℝ) ^ (2 * n) + (p : ℝ) - 1) /
          ((p : ℝ) + 1) :=
  ⟨inverseHerbrandFunction_falseTate_fractional (a : 𝒪[ℚ_[p]]) n i hi,
    inverseHerbrandFunction_falseTate_integer (a : 𝒪[ℚ_[p]]) n i hi,
    inverseHerbrandFunction_falseTate_final (a : 𝒪[ℚ_[p]]) n⟩

end IntegerParameter

end FalseTateExtension
end
