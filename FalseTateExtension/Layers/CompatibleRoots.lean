/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

/-!
# Compatible systems of radicals and roots of unity

Let `Ω` be an algebraically closed field. Every `π ∈ Ω` is the first term of a sequence
`(π_n)` with `π_{n+1}^p = π_n`, so that `π_n` is a `p^n`-th root of `π`. If moreover `Ω` has
characteristic zero, there is a sequence `(ζ_n)` of primitive `p^n`-th roots of unity with
`ζ_{n+1}^p = ζ_n` and `ζ_0 = 1`. These sequences are the roots adjoined to `K` in the
false Tate extension `K(π^{1/p^∞}, ζ_{p^∞})`.

## Main results

* `exists_pow_right_inverse`: `x ↦ x^p` has a right inverse on `Ω`.
* `exists_compatible_radicals`: existence of a compatible system of `p`-power roots of `π`.
* `exists_compatible_primitive_roots`: existence of a compatible system of primitive
  `p`-power roots of unity.

## References

* Liu, *On lattices in semi-stable representations: a proof of a conjecture of Breuil*, §5.1.
-/

@[expose] public section

namespace FalseTateExtension

noncomputable section

variable {Ω : Type*} [Field Ω] [IsAlgClosed Ω]

/-- In an algebraically closed field the map `x ↦ x^p`, `p > 0`, has a right inverse. -/
theorem exists_pow_right_inverse (p : ℕ) (hp : 0 < p) :
    ∃ r : Ω → Ω, ∀ x, r x ^ p = x := by
  have hs : Function.Surjective (fun x : Ω ↦ x ^ p) :=
    fun x ↦ IsAlgClosed.exists_pow_nat_eq x hp
  exact ⟨Function.surjInv hs, Function.surjInv_eq hs⟩

/-- Every `π` in an algebraically closed field is the first term of a sequence `(π_n)` with
`π_{n+1}^p = π_n`; then `π_n^{p^n} = π` for all `n`. -/
theorem exists_compatible_radicals (p : ℕ) [Fact p.Prime] (π : Ω) :
    ∃ πSeq : ℕ → Ω, πSeq 0 = π ∧
      (∀ n, πSeq (n + 1) ^ p = πSeq n) ∧
      ∀ n, πSeq n ^ (p ^ n) = π := by
  obtain ⟨r, hr⟩ := exists_pow_right_inverse (Ω := Ω) p (Fact.out : p.Prime).pos
  refine ⟨fun n ↦ r^[n] π, rfl, ?_, ?_⟩
  · intro n
    change r^[n + 1] π ^ p = r^[n] π
    rw [Function.iterate_succ_apply', hr]
  · intro n
    change r^[n] π ^ (p ^ n) = π
    induction n with
    | zero => simp
    | succ n ih =>
        rw [pow_succ', pow_mul, Function.iterate_succ_apply', hr, ih]

variable [CharZero Ω]

/-- In an algebraically closed field of characteristic zero there is a sequence `(ζ_n)` with
`ζ_0 = 1`, `ζ_{n+1}^p = ζ_n`, and `ζ_n` a primitive `p^n`-th root of unity for every `n`. -/
theorem exists_compatible_primitive_roots (p : ℕ) [Fact p.Prime] :
    ∃ ζ : ℕ → Ω, ζ 0 = 1 ∧
      (∀ n, ζ (n + 1) ^ p = ζ n) ∧
      ∀ n, IsPrimitiveRoot (ζ n) (p ^ n) := by
  obtain ⟨r, hr⟩ := exists_pow_right_inverse (Ω := Ω) p (Fact.out : p.Prime).pos
  have : NeZero (p : Ω) := ⟨by exact_mod_cast (Fact.out : p.Prime).ne_zero⟩
  obtain ⟨η, hη⟩ := HasEnoughRootsOfUnity.exists_isPrimitiveRoot Ω p
  have hprim : ∀ n, IsPrimitiveRoot (r^[n] η) (p ^ (n + 1)) := by
    intro n
    induction n with
    | zero => simpa using hη
    | succ n ih =>
        apply IsPrimitiveRoot.iff_orderOf.mpr
        apply orderOf_eq_prime_pow (p := p) (n := n + 1)
        · rw [pow_succ', pow_mul, Function.iterate_succ_apply', hr]
          exact ih.pow_ne_one_of_pos_of_lt (pow_ne_zero n (Fact.out : p.Prime).ne_zero)
            (pow_lt_pow_right₀ (Fact.out : p.Prime).one_lt (Nat.lt_succ_self n))
        · rw [pow_succ', pow_mul, Function.iterate_succ_apply', hr, ih.pow_eq_one]
  let ζ : ℕ → Ω
    | 0 => 1
    | n + 1 => r^[n] η
  refine ⟨ζ, rfl, ?_, ?_⟩
  · intro n
    cases n with
    | zero => simpa [ζ] using hη.pow_eq_one
    | succ n => simp only [ζ, Function.iterate_succ_apply', hr]
  · intro n
    cases n with
    | zero => simp [ζ]
    | succ n => exact hprim n

end

end FalseTateExtension
