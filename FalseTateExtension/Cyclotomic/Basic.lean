/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FalseTateExtension.Layers.Basic
public import FalseTateExtension.Padic.Basic
public import FalseTateExtension.Mathlib.NumberTheory.Padics.Cyclotomic
public import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots

/-!
# Degrees of the cyclotomic layers over `ℚ_[p]`

`[ℚ_[p](ζ_{p^m}) : ℚ_[p]] = φ(p^m)` for every `m`, since `Φ_{p^m}` is irreducible over `ℚ_[p]`
(`Padic.irreducible_cyclotomic_prime_pow`).

## References

* Serre, *Local Fields*, Chapter IV, §4, Proposition 17.
-/

@[expose] public section

noncomputable section

open Polynomial

namespace FalseTateExtension

variable (p : ℕ) [Fact p.Prime]

instance cyclotomicLayer_padic_isCyclotomicExtension (m : ℕ) :
    IsCyclotomicExtension {p ^ m} (ℚ_[p]) (cyclotomicLayer (K := ℚ_[p]) p m) := by
  have : NeZero (p ^ m) := ⟨pow_ne_zero m (Fact.out : p.Prime).ne_zero⟩
  exact (isPrimitiveRoot_rootOfUnity (K := ℚ_[p]) p
    m).intermediateField_adjoin_isCyclotomicExtension (ℚ_[p])

/-- The cyclotomic layer `ℚ_[p](ζ_{p^m})` has degree `φ(p^m)`, for every `m`. -/
theorem finrank_cyclotomicLayer_padic (m : ℕ) :
    Module.finrank (ℚ_[p]) (cyclotomicLayer (K := ℚ_[p]) p m) = (p ^ m).totient := by
  have : NeZero (p ^ m) := ⟨pow_ne_zero m (Fact.out : p.Prime).ne_zero⟩
  exact IsCyclotomicExtension.finrank _ (Padic.irreducible_cyclotomic_prime_pow p m)


theorem finrank_cyclotomicLayer_padic_zero :
    Module.finrank (ℚ_[p]) (cyclotomicLayer (K := ℚ_[p]) p 0) = 1 := by
  rw [finrank_cyclotomicLayer_padic]
  simp only [pow_zero, Nat.totient_one]

end FalseTateExtension

end
