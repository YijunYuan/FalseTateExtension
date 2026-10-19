/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import Mathlib.Data.ZMod.Units
public import Mathlib.Data.Nat.Totient
public import Mathlib.GroupTheory.Index

/-!
# The kernel of `ZMod.unitsMap` between prime-power levels

For `r ≤ n + 1`, the reduction `(ZMod (p ^ (n + 1)))ˣ →* (ZMod (p ^ r))ˣ` has kernel of index
`φ(p ^ r)` and, for `r > 0`, of order `p ^ (n + 1 - r)`; a unit lies in it iff `p ^ r` divides
`a.val - 1`.

Upstream candidate: `Mathlib.Data.ZMod.Units`.

## Main results

* `ZMod.index_ker_unitsMap_prime_pow`
* `ZMod.card_ker_unitsMap_prime_pow`
* `ZMod.mem_ker_unitsMap_prime_pow_iff`
-/

@[expose] public section

namespace ZMod

variable (p : ℕ) [Fact p.Prime]

theorem index_ker_unitsMap_prime_pow (n r : ℕ) (hr : r ≤ n + 1) :
    (unitsMap (pow_dvd_pow p hr)).ker.index = (p ^ r).totient := by
  have : NeZero (p ^ (n + 1)) := ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
  have : NeZero (p ^ r) := ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
  rw [Subgroup.index_ker,
    MonoidHom.range_eq_top.mpr (unitsMap_surjective (pow_dvd_pow p hr)),
    Subgroup.card_top, Nat.card_eq_fintype_card, card_units_eq_totient]

theorem card_ker_unitsMap_prime_pow (n r : ℕ) (hr0 : 0 < r) (hr : r ≤ n + 1) :
    Nat.card (unitsMap (pow_dvd_pow p hr)).ker = p ^ (n + 1 - r) := by
  have : NeZero (p ^ (n + 1)) := ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
  have : NeZero (p ^ r) := ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
  have hmul := Subgroup.card_ker_mul_card_of_surjective
    (unitsMap_surjective (pow_dvd_pow p hr))
  simp only [Nat.card_eq_fintype_card, card_units_eq_totient] at hmul
  have hφ : (p ^ r).totient ≠ 0 := by
    rw [Nat.totient_prime_pow (Fact.out : p.Prime) hr0]
    exact mul_ne_zero (pow_ne_zero _ (Fact.out : p.Prime).ne_zero)
      (Nat.sub_ne_zero_of_lt (Fact.out : p.Prime).one_lt)
  apply mul_right_cancel₀ hφ
  rw [Nat.card_eq_fintype_card, hmul,
    Nat.totient_prime_pow (Fact.out : p.Prime) (by omega : 0 < n + 1),
    Nat.totient_prime_pow (Fact.out : p.Prime) hr0, ← mul_assoc, ← pow_add]
  congr 2
  omega

theorem mem_ker_unitsMap_prime_pow_iff (n r : ℕ) (hr : r ≤ n + 1) (a : (ZMod (p ^ (n + 1)))ˣ) :
    a ∈ (unitsMap (pow_dvd_pow p hr)).ker ↔ p ^ r ∣ (a : ZMod (p ^ (n + 1))).val - 1 := by
  have : NeZero (p ^ (n + 1)) := ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
  have : Fact (1 < p ^ (n + 1)) :=
    ⟨one_lt_pow₀ (Fact.out : p.Prime).one_lt (by omega)⟩
  have ht : 1 ≤ (a : ZMod (p ^ (n + 1))).val := val_pos.mpr (Units.ne_zero a)
  have hcast : castHom (pow_dvd_pow p hr) (ZMod (p ^ r)) (a : ZMod (p ^ (n + 1))) =
      ((a : ZMod (p ^ (n + 1))).val : ZMod (p ^ r)) := by
    calc
      _ = castHom (pow_dvd_pow p hr) (ZMod (p ^ r))
          (((a : ZMod (p ^ (n + 1))).val : ℕ) : ZMod (p ^ (n + 1))) :=
        congrArg _ (natCast_zmod_val _).symm
      _ = _ := map_natCast _ _
  have hsub : (((a : ZMod (p ^ (n + 1))).val - 1 : ℕ) : ZMod (p ^ r)) =
      ((a : ZMod (p ^ (n + 1))).val : ZMod (p ^ r)) - 1 := by
    rw [Nat.cast_sub ht, Nat.cast_one]
  rw [MonoidHom.mem_ker, Units.ext_iff]
  change castHom (pow_dvd_pow p hr) (ZMod (p ^ r)) (a : ZMod (p ^ (n + 1))) = 1 ↔ _
  rw [hcast, ← sub_eq_zero, ← hsub, natCast_eq_zero_iff]

end ZMod
