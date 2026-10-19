/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FalseTateExtension.Layers
public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Mathlib.RingTheory.Polynomial.Eisenstein.IsIntegral
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Eval
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
public import Mathlib.RingTheory.Polynomial.GaussLemma
public import Mathlib.Algebra.Polynomial.Taylor

/-!
# The p-adic prime-power cyclotomic polynomials

The actual cyclotomic polynomial shifted by one is Eisenstein at `(p)` over
the p-adic integers. It is therefore irreducible over the p-adic numbers,
and primitive roots generate the actual cyclotomic layers with degree given
by Euler's totient, including the degree-one zeroth layer.
This proves blueprint `ft:padic-cyclotomic-polynomial`; see Serre,
*Local Fields*, Chapter IV, Section 4, proof of Proposition 17.
-/

@[expose] public section

noncomputable section

open Polynomial

namespace PadicInt

variable (p : ℕ) [Fact p.Prime]

/-- The shifted positive-level cyclotomic polynomial has constant coefficient `p`. -/
theorem coeff_zero_cyclotomic_prime_pow_comp_X_add_one (n : ℕ) :
    ((cyclotomic (p ^ (n + 1)) (PadicInt p)).comp (X + 1)).coeff 0 = p := by
  simp only [coeff_zero_eq_eval_zero, eval_comp, eval_add, eval_X, eval_one,
    zero_add, eval_one_cyclotomic_prime_pow]

/-- The shifted cyclotomic polynomial remains monic. -/
theorem monic_cyclotomic_prime_pow_comp_X_add_one (n : ℕ) :
    ((cyclotomic (p ^ (n + 1)) (PadicInt p)).comp (X + 1)).Monic := by
  simpa only [C_1] using (cyclotomic.monic (p ^ (n + 1)) (PadicInt p)).comp
    (monic_X_add_C (1 : PadicInt p)) (by simp)

/-- The degree of the shifted positive-level polynomial is the prime-power totient. -/
theorem natDegree_cyclotomic_prime_pow_comp_X_add_one (n : ℕ) :
    ((cyclotomic (p ^ (n + 1)) (PadicInt p)).comp (X + 1)).natDegree =
      (p - 1) * p ^ n := by
  change (taylor 1 (cyclotomic (p ^ (n + 1)) (PadicInt p))).natDegree = _
  rw [natDegree_taylor, natDegree_cyclotomic,
    Nat.totient_prime_pow_succ (Fact.out : p.Prime)]
  exact mul_comm _ _

/-- The uniformizer `p` is not in the square of its principal ideal. -/
theorem p_not_mem_span_p_sq :
    (p : PadicInt p) ∉ (Ideal.span {(p : PadicInt p)} : Ideal (PadicInt p)) ^ 2 := by
  intro h
  rw [Ideal.span_singleton_pow] at h
  have hp0 : (p : PadicInt p) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hv := (mem_span_pow_iff_le_valuation (p : PadicInt p) hp0 2).mp h
  norm_num only [valuation_p] at hv

/-- The actual shifted cyclotomic polynomial is Eisenstein at `(p)` over the
p-adic integers, for every positive level and every prime. -/
theorem cyclotomic_prime_pow_comp_X_add_one_isEisensteinAt (n : ℕ) :
    ((cyclotomic (p ^ (n + 1)) (PadicInt p)).comp (X + 1)).IsEisensteinAt
      (Ideal.span {(p : PadicInt p)}) := by
  have hweak :=
    (_root_.cyclotomic_prime_pow_comp_X_add_one_isEisensteinAt p n).isWeaklyEisensteinAt.map
      (Int.castRingHom (PadicInt p))
  have hprime : (Ideal.span {(p : PadicInt p)} : Ideal (PadicInt p)).IsPrime :=
    (Ideal.span_singleton_prime (by exact_mod_cast (Fact.out : p.Prime).ne_zero)).mpr prime_p
  apply (monic_cyclotomic_prime_pow_comp_X_add_one p n).isEisensteinAt_of_mem_of_notMem
    hprime.ne_top
  · intro k
    simpa [Polynomial.map_comp, map_cyclotomic_int, Ideal.map_span] using (hweak.mem (n := k))
  · rw [coeff_zero_cyclotomic_prime_pow_comp_X_add_one]
    exact p_not_mem_span_p_sq p

/-- The shifted polynomial is irreducible already over the p-adic integers. -/
theorem irreducible_cyclotomic_prime_pow_comp_X_add_one (n : ℕ) :
    Irreducible ((cyclotomic (p ^ (n + 1)) (PadicInt p)).comp (X + 1)) := by
  apply (cyclotomic_prime_pow_comp_X_add_one_isEisensteinAt p n).irreducible
    ((Ideal.span_singleton_prime (by exact_mod_cast (Fact.out : p.Prime).ne_zero)).mpr prime_p)
    (monic_cyclotomic_prime_pow_comp_X_add_one p n).isPrimitive
  rw [natDegree_cyclotomic_prime_pow_comp_X_add_one]
  exact Nat.mul_pos (Nat.sub_pos_of_lt (Fact.out : p.Prime).one_lt)
    (pow_pos (Fact.out : p.Prime).pos n)

/-- Reindexing the positive-level Eisenstein theorem to all `m ≥ 1`. -/
theorem cyclotomic_prime_pow_comp_X_add_one_isEisensteinAt_of_pos (m : ℕ) (hm : 0 < m) :
    ((cyclotomic (p ^ m) (PadicInt p)).comp (X + 1)).IsEisensteinAt
      (Ideal.span {(p : PadicInt p)}) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm.ne'
  exact cyclotomic_prime_pow_comp_X_add_one_isEisensteinAt p n

end PadicInt

namespace Padic

variable (p : ℕ) [Fact p.Prime]

/-- Gauss's lemma transports the actual shifted polynomial's irreducibility
from the p-adic integers to their fraction field. -/
theorem irreducible_cyclotomic_prime_pow_comp_X_add_one (n : ℕ) :
    Irreducible ((cyclotomic (p ^ (n + 1)) (Padic p)).comp (X + 1)) := by
  have hm := PadicInt.monic_cyclotomic_prime_pow_comp_X_add_one p n
  have h := hm.irreducible_iff_irreducible_map_fraction_map (K := Padic p)
  have hi := h.mp (PadicInt.irreducible_cyclotomic_prime_pow_comp_X_add_one p n)
  simpa [Polynomial.map_comp, Polynomial.map_cyclotomic] using hi

/-- Every prime-power cyclotomic polynomial is irreducible over the actual
p-adic field, including the zeroth level and the prime two. -/
theorem irreducible_cyclotomic_prime_pow (m : ℕ) :
    Irreducible (cyclotomic (p ^ m) (Padic p)) := by
  cases m with
  | zero => simpa using irreducible_X_sub_C (1 : Padic p)
  | succ n =>
      have h := irreducible_cyclotomic_prime_pow_comp_X_add_one p n
      change Irreducible ((taylorEquiv (1 : Padic p)) (cyclotomic (p ^ (n + 1)) (Padic p))) at h
      exact (MulEquiv.irreducible_iff (f := (taylorEquiv (1 : Padic p)).toMulEquiv)).mp h

/-- Every actual primitive root has the prime-power cyclotomic polynomial
as its minimal polynomial over the p-adic field. -/
theorem minpoly_primitive_root {L : Type*} [Field L] [Algebra (Padic p) L]
    (m : ℕ) {ζ : L} (hζ : IsPrimitiveRoot ζ (p ^ m)) :
    minpoly (Padic p) ζ = cyclotomic (p ^ m) (Padic p) := by
  have : NeZero ((p ^ m : ℕ) : Padic p) :=
    ⟨by exact_mod_cast pow_ne_zero m (Fact.out : p.Prime).ne_zero⟩
  exact (hζ.minpoly_eq_cyclotomic_of_irreducible (irreducible_cyclotomic_prime_pow p m)).symm

/-- Adjoining any actual primitive root gives degree `φ(p^m)`, without an
assumption that the ambient field extension is algebraic. -/
theorem finrank_adjoin_primitive_root {L : Type*} [Field L] [Algebra (Padic p) L]
    (m : ℕ) {ζ : L} (hζ : IsPrimitiveRoot ζ (p ^ m)) :
    Module.finrank (Padic p) (IntermediateField.adjoin (Padic p) {ζ}) = (p ^ m).totient := by
  rw [IntermediateField.adjoin.finrank
    ((hζ.isIntegral (pow_pos (Fact.out : p.Prime).pos m)).tower_top),
    minpoly_primitive_root p m hζ, natDegree_cyclotomic]

end Padic

namespace FalseTateExtension

variable (p : ℕ) [Fact p.Prime]

/-- The existing actual cyclotomic layer over `ℚp` has precisely its expected
degree, for every level including zero. -/
theorem finrank_cyclotomicLayer_padic (m : ℕ) :
    Module.finrank (Padic p) (cyclotomicLayer (K := Padic p) p m) = (p ^ m).totient :=
  Padic.finrank_adjoin_primitive_root p m (isPrimitiveRoot_rootOfUnity (K := Padic p) p m)

/-- The actual zeroth cyclotomic layer has degree one. -/
theorem finrank_cyclotomicLayer_padic_zero :
    Module.finrank (Padic p) (cyclotomicLayer (K := Padic p) p 0) = 1 := by
  rw [finrank_cyclotomicLayer_padic]
  simp only [pow_zero, Nat.totient_one]

end FalseTateExtension

end
