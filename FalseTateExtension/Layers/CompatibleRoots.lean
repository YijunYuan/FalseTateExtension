/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

/-!
# Compatible radicals and primitive roots of unity

In an algebraically closed field of characteristic zero, every element admits
a compatible sequence of p-power radicals, and primitive p-power roots of unity
can be chosen compatibly. The construction includes `p = 2` and a zero initial
radicand.

This supplies the choices in blueprint `ft:compatible-roots`, following the
setup of Liu, Section 5.1 (printed page 82).
-/

@[expose] public section

namespace FalseTateExtension

noncomputable section

variable {Ω : Type*} [Field Ω] [IsAlgClosed Ω]

theorem exists_pow_right_inverse (p : ℕ) (hp : 0 < p) :
    ∃ r : Ω → Ω, ∀ x, r x ^ p = x := by
  have hs : Function.Surjective (fun x : Ω ↦ x ^ p) :=
    fun x ↦ IsAlgClosed.exists_pow_nat_eq x hp
  exact ⟨Function.surjInv hs, Function.surjInv_eq hs⟩

/-- Every element of an algebraically closed field of characteristic zero has
a compatible system of p-power radicals. The initial element may be zero. -/
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

/-- Primitive p-power roots of unity can be chosen compatibly, with the
zeroth root equal to one. The initial primitive pth root is chosen separately
before taking successive pth roots, ensuring primitivity at every level. -/
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
