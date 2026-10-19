/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FalseTateExtension.Kummer.Eisenstein
public import FalseTateExtension.Kummer.StepProfile
public import FontaineWintenberger.APF.BaseChange.Basic
public import FontaineWintenberger.APF.Elementary.PrimeDegree
public import FontaineWintenberger.APF.Galois.Union
public import FontaineWintenberger.APF.Strict
public import FontaineWintenberger.APF.Tower.TotallyRamified

/-!
# The upper ramification breaks of the Kummer extension

Let `K` be a complete discretely valued field, `p` a prime and `e_K = v_K(p)`. The upper
ramification breaks of `K(π^{1/p^∞})/K` are `u_j = e_K (j + 1/(p-1))` for `j ≥ 1`; the
step `K(π^{1/p^n}) ⊆ K(π^{1/p^{n+1}})` has its break at `t_n = p^{n+1} e_K / (p - 1)` in the
numbering of `K(π^{1/p^n})`, and `t_n = ψ_{K(π^{1/p^n})/K}(u_{n+1})`.

## Main results

* `radicalUpperBreak`: the upper break `u_j = e_K (j + 1/(p-1))`.
* `radicalRelativeBreak`: the break `t_n = p^{n+1} e_K / (p - 1)` of the step.
* `radicalUpperBreak_succ`: `u_{j+1} = u_j + e_K`.
* `radicalRelativeBreak_eq_affine`: `t_n = p^n e_K/(p-1) + p^n (u_{n+1} - u_n)`.
* `radicalUpperBreak_mono`: the breaks `u_j` increase with `j`.

## References

* Wintenberger, *Le corps des normes de certaines extensions infinies de corps locaux;
  applications*, §1.2.3.
-/

@[expose] public section

noncomputable section

namespace FalseTateExtension

open FontaineWintenberger IsDiscreteValuationRing

section Breaks

variable {K : Type*} [NontriviallyNormedField K] [IsCompleteDiscreteValuedField K]
variable (p : ℕ) [Fact p.Prime]

/-- The upper ramification break `u_j = e_K (j + 1/(p-1))` of `K(π^{1/p^∞})/K`. -/
def radicalUpperBreak (j : ℕ) : ℝ :=
  (absoluteRamificationIdx p K : ℝ) * ((j : ℝ) + 1 / ((p : ℝ) - 1))

/-- The ramification break `t_n = p^{n+1} e_K / (p - 1)` of `K(π^{1/p^{n+1}})/K(π^{1/p^n})`. -/
def radicalRelativeBreak (n : ℕ) : ℝ :=
  (p : ℝ) ^ (n + 1) * (absoluteRamificationIdx p K : ℝ) / ((p : ℝ) - 1)

omit [Fact p.Prime] in
/-- `u_{j+1} = u_j + e_K`. -/
theorem radicalUpperBreak_succ (n : ℕ) :
    radicalUpperBreak (K := K) p (n + 1) =
      radicalUpperBreak (K := K) p n + absoluteRamificationIdx p K := by
  simp only [radicalUpperBreak, Nat.cast_add, Nat.cast_one]
  ring

/-- `t_n = p^n e_K / (p - 1) + p^n (u_{n+1} - u_n)`. -/
theorem radicalRelativeBreak_eq_affine (n : ℕ) :
    radicalRelativeBreak (K := K) p n =
      (p : ℝ) ^ n * (absoluteRamificationIdx p K : ℝ) / ((p : ℝ) - 1) +
        (p : ℝ) ^ n * (radicalUpperBreak (K := K) p (n + 1) -
          radicalUpperBreak (K := K) p n) := by
  have hp : (p : ℝ) - 1 ≠ 0 := by
    have : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
    linarith
  rw [radicalUpperBreak_succ]
  dsimp only [radicalRelativeBreak]
  rw [pow_succ]
  field_simp
  ring

/-- `0 ≤ u_j`. -/
theorem radicalUpperBreak_nonneg (n : ℕ) : 0 ≤ radicalUpperBreak (K := K) p n := by
  have hp : 0 < (p : ℝ) - 1 := by
    have : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
    linarith
  exact mul_nonneg (Nat.cast_nonneg _) (add_nonneg (Nat.cast_nonneg _)
    (div_nonneg zero_le_one hp.le))

omit [Fact p.Prime] in
/-- The breaks `u_j` increase with `j`. -/
theorem radicalUpperBreak_mono : Monotone (radicalUpperBreak (K := K) p) := by
  apply monotone_nat_of_le_succ
  intro n
  rw [radicalUpperBreak_succ]
  exact le_add_of_nonneg_right (Nat.cast_nonneg _)

end Breaks

end FalseTateExtension
end
