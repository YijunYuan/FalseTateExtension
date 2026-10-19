/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FalseTateExtension.Layers.Galois
public import FalseTateExtension.Mathlib.FieldTheory.Galois.InfiniteCorrespondence
public import Mathlib.NumberTheory.Cyclotomic.Gal
public import Mathlib.FieldTheory.Galois.Abelian
public import Mathlib.FieldTheory.LinearDisjoint
public import Mathlib.RingTheory.ZMod.UnitsCyclic

/-!
# Cyclotomic layers at an odd prime

Let `K` be a field of characteristic zero and `p ≠ 2`. The group `Gal(K(ζ_{p^n})/K)` embeds in
`(ℤ/p^n)ˣ`, which is cyclic, so it is cyclic. If `ζ_p ∈ K` and `r` is the least index with
`K(ζ_{p^{r+1}}) ≠ K`, then `ζ_{p^r} = a ∈ K` and the minimal polynomial of `ζ_{p^{r+1}}` over `K`
is `X^p - a`, so `[K(ζ_{p^{r+1}}) : K] = p`; a subfield of degree `p` of some `K(ζ_{p^m})` is
therefore `K(ζ_{p^{r+1}})`.

## Main results

* `cyclotomicLayer_isAbelianGalois`: `K(ζ_{p^n})/K` is abelian.
* `cyclotomicLayer_isCyclic`: `Gal(K(ζ_{p^n})/K)` is cyclic for `p ≠ 2`.
* `cyclotomicLayer_step_minpoly_of_eq_bot`: if `ζ_p ∈ K`, `K(ζ_{p^n}) = K` and
  `K(ζ_{p^{n+1}}) ≠ K`, the minimal polynomial of `ζ_{p^{n+1}}` over `K` is `X^p - ζ_{p^n}`.
* `cyclotomicLayer_step_finrank_of_eq_bot`: under the same hypotheses `[K(ζ_{p^{n+1}}) : K] = p`.
* `exists_eq_first_cyclotomicLayer_of_finrank_prime`: for `p ≠ 2` and `ζ_p ∈ K`, a subfield of
  degree `p` of `K(ζ_{p^m})` is the first layer `K(ζ_{p^{r+1}}) ≠ K`.

## References

* Liu, *On lattices in semi-stable representations: a proof of a conjecture of Breuil*,
  Lemma 5.1.2.
-/

@[expose] public section

noncomputable section

namespace FalseTateExtension

open Polynomial
open FontaineWintenberger

section FiniteCyclotomic

variable {K : Type*} [Field K] [CharZero K] (p : ℕ) [Fact p.Prime]

/-- `K(ζ_{p^n})/K` is an abelian Galois extension. -/
theorem cyclotomicLayer_isAbelianGalois (n : ℕ) :
    IsAbelianGalois K (cyclotomicLayer (K := K) p n) := by
  have : NeZero (p ^ n) := ⟨pow_ne_zero n (Fact.out : p.Prime).ne_zero⟩
  have : IsCyclotomicExtension {p ^ n} K (cyclotomicLayer (K := K) p n) :=
    (isPrimitiveRoot_zeta (K := K) p n).intermediateField_adjoin_isCyclotomicExtension K
  exact IsCyclotomicExtension.isAbelianGalois {p ^ n} K _

/-- For `p ≠ 2`, `Gal(K(ζ_{p^n})/K)` is cyclic. -/
theorem cyclotomicLayer_isCyclic [hp₂ : Fact (p ≠ 2)] (n : ℕ) :
    IsCyclic (cyclotomicLayer (K := K) p n ≃ₐ[K] cyclotomicLayer (K := K) p n) := by
  have : NeZero (p ^ n) := ⟨pow_ne_zero n (Fact.out : p.Prime).ne_zero⟩
  have : IsCyclotomicExtension {p ^ n} K (cyclotomicLayer (K := K) p n) :=
    (isPrimitiveRoot_zeta (K := K) p n).intermediateField_adjoin_isCyclotomicExtension K
  let ζ : cyclotomicLayer (K := K) p n :=
    ⟨zeta p n, zeta_mem_cyclotomicLayer p n⟩
  have hζ : IsPrimitiveRoot ζ (p ^ n) :=
    (isPrimitiveRoot_zeta (K := K) p n).of_map_of_injective
      (f := (cyclotomicLayer (K := K) p n).val) (cyclotomicLayer p n).val.injective
  let := ZMod.isCyclic_units_of_prime_pow p (Fact.out : p.Prime) hp₂.out n
  exact isCyclic_of_injective (hζ.autToPow K) (hζ.autToPow_injective K)

/-- If `ζ_p ∈ K`, `K(ζ_{p^n}) = K` and `K(ζ_{p^{n+1}}) ≠ K`, then `ζ_{p^n} = a` for some
`a ∈ K` and the minimal polynomial of `ζ_{p^{n+1}}` over `K` is `X^p - a`. -/
theorem cyclotomicLayer_step_minpoly_of_eq_bot (n : ℕ)
    (h₁ : cyclotomicLayer (K := K) p 1 = ⊥)
    (hprev : cyclotomicLayer (K := K) p n = ⊥)
    (hnext : cyclotomicLayer (K := K) p (n + 1) ≠ ⊥) :
    ∃ a : K, algebraMap K (AlgebraicClosure K) a = zeta p n ∧
      minpoly K (zeta (K := K) p (n + 1)) = Polynomial.X ^ p - Polynomial.C a := by
  have hprevMem : zeta (K := K) p n ∈ (⊥ : IntermediateField K (AlgebraicClosure K)) := by
    rw [← hprev]
    exact zeta_mem_cyclotomicLayer p n
  obtain ⟨a, ha⟩ := hprevMem
  change algebraMap K (AlgebraicClosure K) a = zeta p n at ha
  have ha₀ : a ≠ 0 := by
    intro h
    have hz := zeta_pow_eq_one (K := K) p n
    rw [← ha, h, map_zero, zero_pow (pow_ne_zero n (Fact.out : p.Prime).ne_zero)] at hz
    exact zero_ne_one hz
  have hnot (b : K) : b ^ p ≠ a := by
    intro hb
    have hb₀ : b ≠ 0 := by
      intro h
      apply ha₀
      rw [← hb, h, zero_pow (Fact.out : p.Prime).ne_zero]
    have hquot : (zeta (K := K) p (n + 1) /
        algebraMap K (AlgebraicClosure K) b) ^ p = 1 := by
      rw [div_pow, zeta_succ_pow, ← ha, ← map_pow, hb,
        div_self ((map_ne_zero (algebraMap K (AlgebraicClosure K))).mpr ha₀)]
    have hprimitive : IsPrimitiveRoot (zeta (K := K) p 1) p := by
      simpa only [pow_one] using isPrimitiveRoot_zeta (K := K) p 1
    obtain ⟨i, _, hi⟩ := hprimitive.eq_pow_of_pow_eq_one hquot
    have hζ₁ : zeta (K := K) p 1 ∈ (⊥ : IntermediateField K (AlgebraicClosure K)) := by
      rw [← h₁]
      exact zeta_mem_cyclotomicLayer p 1
    apply hnext
    apply le_antisymm _ bot_le
    apply IntermediateField.adjoin_simple_le_iff.mpr
    have hroot : zeta (K := K) p (n + 1) =
        zeta p 1 ^ i * algebraMap K (AlgebraicClosure K) b := by
      rw [hi, div_mul_cancel₀ _ ((map_ne_zero (algebraMap K (AlgebraicClosure K))).mpr hb₀)]
    rw [hroot]
    exact (⊥ : IntermediateField K (AlgebraicClosure K)).mul_mem
      ((⊥ : IntermediateField K (AlgebraicClosure K)).toSubalgebra.pow_mem hζ₁ i)
      ((⊥ : IntermediateField K (AlgebraicClosure K)).algebraMap_mem b)
  have hirr : Irreducible (Polynomial.X ^ p - Polynomial.C a : K[X]) :=
    X_pow_sub_C_irreducible_of_prime (Fact.out : p.Prime) hnot
  refine ⟨a, ha, ?_⟩
  symm
  apply minpoly.eq_of_irreducible_of_monic hirr
  · simp only [map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C,
      zeta_succ_pow, ha, sub_self]
  · exact Polynomial.monic_X_pow_sub_C a (Fact.out : p.Prime).ne_zero

/-- If `ζ_p ∈ K`, `K(ζ_{p^n}) = K` and `K(ζ_{p^{n+1}}) ≠ K`, then `[K(ζ_{p^{n+1}}) : K] = p`. -/
theorem cyclotomicLayer_step_finrank_of_eq_bot (n : ℕ)
    (h₁ : cyclotomicLayer (K := K) p 1 = ⊥)
    (hprev : cyclotomicLayer (K := K) p n = ⊥)
    (hnext : cyclotomicLayer (K := K) p (n + 1) ≠ ⊥) :
    Module.finrank K (cyclotomicLayer (K := K) p (n + 1)) = p := by
  obtain ⟨a, _, hmin⟩ := cyclotomicLayer_step_minpoly_of_eq_bot p n h₁ hprev hnext
  calc
    _ = (minpoly K (zeta (K := K) p (n + 1))).natDegree :=
      IntermediateField.adjoin.finrank (Algebra.IsIntegral.isIntegral _)
    _ = p := by rw [hmin, natDegree_X_pow_sub_C]

/-- If `K(ζ_{p^n}) ≠ K`, there is `r < n` with `K(ζ_{p^r}) = K` and `K(ζ_{p^{r+1}}) ≠ K`. -/
theorem exists_first_nontrivial_cyclotomicLayer {n : ℕ}
    (hn : cyclotomicLayer (K := K) p n ≠ ⊥) :
    ∃ r : ℕ, r + 1 ≤ n ∧ cyclotomicLayer (K := K) p r = ⊥ ∧
      cyclotomicLayer (K := K) p (r + 1) ≠ ⊥ := by
  classical
  let h : ∃ j : ℕ, cyclotomicLayer (K := K) p j ≠ ⊥ := ⟨n, hn⟩
  have hz : Nat.find h ≠ 0 := by
    intro hz
    have hne := Nat.find_spec h
    rw [hz, cyclotomicLayer_zero] at hne
    exact hne rfl
  obtain ⟨r, hr⟩ := Nat.exists_eq_succ_of_ne_zero hz
  refine ⟨r, ?_, ?_, ?_⟩
  · have hle := Nat.find_min' h hn
    omega
  · exact not_not.mp (Nat.find_min h (by omega : r < Nat.find h))
  · simpa only [hr] using Nat.find_spec h

/-- For `p ≠ 2` and `ζ_p ∈ K`, a subfield `F ⊆ K(ζ_{p^m})` with `[F : K] = p` equals
`K(ζ_{p^{r+1}})`, where `r < m`, `K(ζ_{p^r}) = K` and `K(ζ_{p^{r+1}}) ≠ K`. -/
theorem exists_eq_first_cyclotomicLayer_of_finrank_prime [hp₂ : Fact (p ≠ 2)]
    (F : IntermediateField K (AlgebraicClosure K)) [FiniteDimensional K F]
    {m : ℕ} (hFm : F ≤ cyclotomicLayer (K := K) p m)
    (hd : Module.finrank K F = p) (h₁ : cyclotomicLayer (K := K) p 1 = ⊥) :
    ∃ r : ℕ, r + 1 ≤ m ∧ cyclotomicLayer (K := K) p r = ⊥ ∧
      cyclotomicLayer (K := K) p (r + 1) ≠ ⊥ ∧ F = cyclotomicLayer p (r + 1) := by
  have hm : cyclotomicLayer (K := K) p m ≠ ⊥ := by
    intro hm
    have hF : F = ⊥ := bot_unique (hm ▸ hFm)
    rw [hF, IntermediateField.finrank_bot] at hd
    exact (Fact.out : p.Prime).ne_one hd.symm
  obtain ⟨r, hrm, hprev, hnext⟩ := exists_first_nontrivial_cyclotomicLayer p hm
  refine ⟨r, hrm, hprev, hnext, ?_⟩
  let C := cyclotomicLayer (K := K) p m
  let i := IntermediateField.inclusion hFm
  let j := IntermediateField.inclusion (cyclotomicLayer_mono (K := K) p hrm)
  let := cyclotomicLayer_isCyclic (K := K) p m
  have heq : i.fieldRange = j.fieldRange := by
    apply IntermediateField.eq_of_finrank_eq_of_isCyclic
    calc
      _ = Module.finrank K F := i.equivFieldRange.toLinearEquiv.finrank_eq.symm
      _ = p := hd
      _ = Module.finrank K (cyclotomicLayer (K := K) p (r + 1)) :=
        (cyclotomicLayer_step_finrank_of_eq_bot p r h₁ hprev hnext).symm
      _ = _ := j.equivFieldRange.toLinearEquiv.finrank_eq
  have hmap := congrArg (fun E : IntermediateField K C => E.map C.val) heq
  have hi : C.val.comp i = F.val := rfl
  have hj : C.val.comp j = (cyclotomicLayer (K := K) p (r + 1)).val := rfl
  simpa only [AlgHom.map_fieldRange, hi, hj, IntermediateField.fieldRange_val] using hmap

end FiniteCyclotomic

end FalseTateExtension
end
