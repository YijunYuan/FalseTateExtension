/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import Mathlib.FieldTheory.Minpoly.Field
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Polynomial.Eisenstein.Basic
public import Mathlib.RingTheory.Polynomial.GaussLemma
public import Mathlib.RingTheory.Polynomial.RationalRoot

/-!
# The Eisenstein polynomial `X ^ m - π` of a uniformizer

Over a discrete valuation ring `R` with uniformizer `π`, the polynomial `X ^ m - π` (`m > 0`) is
Eisenstein at the maximal ideal, hence irreducible over the fraction field `K`; it is therefore the
minimal polynomial over `K` of any `m`-th root of `π`.

Upstream candidate: `Mathlib.RingTheory.Polynomial.Eisenstein`.

## Main results

* `Polynomial.isEisensteinAt_X_pow_sub_C_of_irreducible`
* `Polynomial.irreducible_X_pow_sub_C_of_irreducible`
* `Polynomial.minpoly_eq_X_pow_sub_C_of_pow_eq_of_irreducible`
-/

@[expose] public section

namespace Polynomial

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

/-- `X ^ m - π` is Eisenstein at the maximal ideal for a uniformizer `π` and `m > 0`. -/
theorem isEisensteinAt_X_pow_sub_C_of_irreducible {π : R} (hπ : Irreducible π)
    {m : ℕ} (hm : 0 < m) :
    (X ^ m - C π : R[X]).IsEisensteinAt (IsLocalRing.maximalIdeal R) := by
  apply (monic_X_pow_sub_C π hm.ne').isEisensteinAt_of_mem_of_notMem
    (IsLocalRing.maximalIdeal.isMaximal R).ne_top
  · intro i hi
    rw [natDegree_X_pow_sub_C] at hi
    by_cases hi0 : i = 0
    · subst i
      simpa [coeff_sub, coeff_X_pow, hm.ne] using
        (IsLocalRing.maximalIdeal R).neg_mem hπ.not_isUnit
    · simp [coeff_sub, coeff_X_pow, coeff_C, hi.ne, hi0]
  · have hc : (X ^ m - C π : R[X]).coeff 0 = -π := by
      simp [coeff_sub, coeff_X_pow, coeff_C, hm.ne]
    rw [hc, hπ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton, dvd_neg]
    intro h
    apply hπ.not_isUnit
    apply isUnit_of_dvd_one
    exact (mul_dvd_mul_iff_left hπ.ne_zero).mp (by rwa [mul_one, ← pow_two])

/-- `X ^ m - π` is irreducible over the fraction field of `R` (Gauss's lemma). -/
theorem irreducible_X_pow_sub_C_of_irreducible {π : R} (hπ : Irreducible π)
    {m : ℕ} (hm : 0 < m) (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K] :
    Irreducible (X ^ m - C (algebraMap R K π) : K[X]) := by
  have hE := isEisensteinAt_X_pow_sub_C_of_irreducible hπ hm
  have hI := hE.irreducible (inferInstance : (IsLocalRing.maximalIdeal R).IsPrime)
    (monic_X_pow_sub_C π hm.ne').isPrimitive (by simpa using hm)
  have h := (monic_X_pow_sub_C π hm.ne').irreducible_iff_irreducible_map_fraction_map (K := K)
  simpa only [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C]
    using h.mp hI

@[deprecated (since := "2026-10-26")]
alias X_pow_sub_C_irreducible_of_irreducible := irreducible_X_pow_sub_C_of_irreducible

/-- The minimal polynomial over the fraction field of an `m`-th root of a uniformizer. -/
theorem minpoly_eq_X_pow_sub_C_of_pow_eq_of_irreducible {π : R} (hπ : Irreducible π)
    {m : ℕ} (hm : 0 < m) (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]
    {L : Type*} [Field L] [Algebra K L] (α : L)
    (hα : α ^ m = algebraMap K L (algebraMap R K π)) :
    minpoly K α = X ^ m - C (algebraMap R K π) := by
  symm
  apply minpoly.eq_of_irreducible_of_monic
    (irreducible_X_pow_sub_C_of_irreducible hπ hm K)
    (by simpa only [map_sub, map_pow, aeval_X, aeval_C] using sub_eq_zero.mpr hα)
    (monic_X_pow_sub_C _ hm.ne')

end Polynomial
