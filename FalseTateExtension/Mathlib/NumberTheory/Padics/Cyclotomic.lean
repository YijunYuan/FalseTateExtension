/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import Mathlib.Algebra.Polynomial.Taylor
public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Eval
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
public import Mathlib.RingTheory.Polynomial.Eisenstein.IsIntegral
public import Mathlib.RingTheory.Polynomial.GaussLemma

/-!
# Prime-power cyclotomic polynomials over `ℚ_[p]`

`Φ_{p^(n+1)}(X + 1)` is Eisenstein at `(p)` over `ℤ_[p]`, so `Φ_{p^m}` is irreducible over `ℚ_[p]`
for every `m`. Hence `ℚ_[p](ζ_{p^m})/ℚ_[p]` has degree `φ(p^m)`: for a primitive `p^m`-th root
`ζ` in any `ℚ_[p]`-algebra, `IsPrimitiveRoot.minpoly_eq_cyclotomic_of_irreducible` and
`IsCyclotomicExtension.finrank` apply with `Padic.irreducible_cyclotomic_prime_pow`.

Upstream candidate: `Mathlib.NumberTheory.Padics`.

## Main results

* `PadicInt.cyclotomic_prime_pow_comp_X_add_one_isEisensteinAt`
* `Padic.irreducible_cyclotomic_prime_pow`

## References

* [J.-P. Serre, *Local Fields*](https://doi.org/10.1007/978-1-4757-5673-9), Chapter IV, §4, proof of
  Proposition 17.
-/

@[expose] public section

noncomputable section

open Polynomial

namespace PadicInt

variable (p : ℕ) [Fact p.Prime]

/-- The constant coefficient of `Φ_{p^(n+1)}(X + 1)` is `p`. -/
theorem coeff_zero_cyclotomic_prime_pow_comp_X_add_one (n : ℕ) :
    ((cyclotomic (p ^ (n + 1)) (ℤ_[p])).comp (X + 1)).coeff 0 = p := by
  simp only [coeff_zero_eq_eval_zero, eval_comp, eval_add, eval_X, eval_one,
    zero_add, eval_one_cyclotomic_prime_pow]

/-- The translated cyclotomic polynomial `Φ_{p^(n+1)}(X + 1)` is monic. -/
theorem monic_cyclotomic_prime_pow_comp_X_add_one (n : ℕ) :
    ((cyclotomic (p ^ (n + 1)) (ℤ_[p])).comp (X + 1)).Monic := by
  simpa only [C_1] using (cyclotomic.monic (p ^ (n + 1)) (ℤ_[p])).comp
    (monic_X_add_C (1 : ℤ_[p])) (by simp)

/-- The degree of `Φ_{p^(n+1)}(X + 1)` is `(p - 1) * p ^ n`. -/
theorem natDegree_cyclotomic_prime_pow_comp_X_add_one (n : ℕ) :
    ((cyclotomic (p ^ (n + 1)) (ℤ_[p])).comp (X + 1)).natDegree =
      (p - 1) * p ^ n := by
  change (taylor 1 (cyclotomic (p ^ (n + 1)) (ℤ_[p]))).natDegree = _
  rw [natDegree_taylor, natDegree_cyclotomic,
    Nat.totient_prime_pow_succ (Fact.out : p.Prime)]
  exact mul_comm _ _

/-- The prime `p` does not belong to the square of the maximal ideal of `ℤ_[p]`. -/
theorem p_notMem_span_p_sq :
    (p : ℤ_[p]) ∉ (Ideal.span {(p : ℤ_[p])} : Ideal (ℤ_[p])) ^ 2 := by
  intro h
  rw [Ideal.span_singleton_pow] at h
  have hp0 : (p : ℤ_[p]) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hv := (mem_span_pow_iff_le_valuation (p : ℤ_[p]) hp0 2).mp h
  norm_num only [valuation_p] at hv

@[deprecated (since := "2026-10-26")]
alias p_not_mem_span_p_sq := p_notMem_span_p_sq

/-- `Φ_{p^(n+1)}(X + 1)` is Eisenstein at `(p)` over `ℤ_[p]`. -/
theorem cyclotomic_prime_pow_comp_X_add_one_isEisensteinAt (n : ℕ) :
    ((cyclotomic (p ^ (n + 1)) (ℤ_[p])).comp (X + 1)).IsEisensteinAt
      (Ideal.span {(p : ℤ_[p])}) := by
  have hweak :=
    (_root_.cyclotomic_prime_pow_comp_X_add_one_isEisensteinAt p n).isWeaklyEisensteinAt.map
      (Int.castRingHom (ℤ_[p]))
  have hprime : (Ideal.span {(p : ℤ_[p])} : Ideal (ℤ_[p])).IsPrime :=
    (Ideal.span_singleton_prime (by exact_mod_cast (Fact.out : p.Prime).ne_zero)).mpr prime_p
  apply (monic_cyclotomic_prime_pow_comp_X_add_one p n).isEisensteinAt_of_mem_of_notMem
    hprime.ne_top
  · intro k
    simpa [Polynomial.map_comp, map_cyclotomic_int, Ideal.map_span] using (hweak.mem (n := k))
  · rw [coeff_zero_cyclotomic_prime_pow_comp_X_add_one]
    exact p_notMem_span_p_sq p

/-- The translated cyclotomic polynomial `Φ_{p^(n+1)}(X + 1)` is irreducible. -/
theorem irreducible_cyclotomic_prime_pow_comp_X_add_one (n : ℕ) :
    Irreducible ((cyclotomic (p ^ (n + 1)) (ℤ_[p])).comp (X + 1)) := by
  apply (cyclotomic_prime_pow_comp_X_add_one_isEisensteinAt p n).irreducible
    ((Ideal.span_singleton_prime (by exact_mod_cast (Fact.out : p.Prime).ne_zero)).mpr prime_p)
    (monic_cyclotomic_prime_pow_comp_X_add_one p n).isPrimitive
  rw [natDegree_cyclotomic_prime_pow_comp_X_add_one]
  exact Nat.mul_pos (Nat.sub_pos_of_lt (Fact.out : p.Prime).one_lt)
    (pow_pos (Fact.out : p.Prime).pos n)

/-- For positive `m`, the polynomial `Φ_{p^m}(X + 1)` is Eisenstein at `(p)` over `ℤ_[p]`. -/
theorem cyclotomic_prime_pow_comp_X_add_one_isEisensteinAt_of_pos (m : ℕ) (hm : 0 < m) :
    ((cyclotomic (p ^ m) (ℤ_[p])).comp (X + 1)).IsEisensteinAt
      (Ideal.span {(p : ℤ_[p])}) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm.ne'
  exact cyclotomic_prime_pow_comp_X_add_one_isEisensteinAt p n

end PadicInt

namespace Padic

variable (p : ℕ) [Fact p.Prime]

/-- The translated cyclotomic polynomial `Φ_{p^(n+1)}(X + 1)` is irreducible. -/
theorem irreducible_cyclotomic_prime_pow_comp_X_add_one (n : ℕ) :
    Irreducible ((cyclotomic (p ^ (n + 1)) (ℚ_[p])).comp (X + 1)) := by
  have hm := PadicInt.monic_cyclotomic_prime_pow_comp_X_add_one p n
  have h := hm.irreducible_iff_irreducible_map_fraction_map (K := ℚ_[p])
  have hi := h.mp (PadicInt.irreducible_cyclotomic_prime_pow_comp_X_add_one p n)
  simpa [Polynomial.map_comp, Polynomial.map_cyclotomic] using hi

/-- `Φ_{p^m}` is irreducible over `ℚ_[p]` for every `m`, including `m = 0` and `p = 2`. -/
theorem irreducible_cyclotomic_prime_pow (m : ℕ) :
    Irreducible (cyclotomic (p ^ m) (ℚ_[p])) := by
  cases m with
  | zero => simpa using irreducible_X_sub_C (1 : ℚ_[p])
  | succ n =>
      have h := irreducible_cyclotomic_prime_pow_comp_X_add_one p n
      change Irreducible ((taylorEquiv (1 : ℚ_[p])) (cyclotomic (p ^ (n + 1)) (ℚ_[p]))) at h
      exact (MulEquiv.irreducible_iff (f := (taylorEquiv (1 : ℚ_[p])).toMulEquiv)).mp h

end Padic

end
