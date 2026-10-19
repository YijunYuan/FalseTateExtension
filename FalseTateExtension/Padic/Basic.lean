/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FontaineWintenberger.LocalField.Basic
public import FontaineWintenberger.Mathlib.RingTheory.DiscreteValuationRing
public import Mathlib.NumberTheory.Padics.RingHoms
public import Mathlib.NumberTheory.Padics.ProperSpace

/-!
# The `p`-adic numbers as a local field

`ℚ_[p]` satisfies the standing hypotheses of `FontaineWintenberger`: it is a complete discretely
valued field with perfect (indeed finite) residue field `ZMod p`. Its valuation subring `𝒪[ℚ_[p]]`
is identified with `ℤ_[p]`, the normalized valuation of `p` is `exp (-1)`, and `ℤ_[p]ˣ` is
infinite.

## Main declarations

* `padicUnitBallEquiv : 𝒪[ℚ_[p]] ≃+* ℤ_[p]`
* `padicUnitBallResidueEquiv : 𝓀[ℚ_[p]] ≃+* ZMod p`
* instances `IsCompleteDiscreteValuedField ℚ_[p]`, `IsPerfectResidueLocalField ℚ_[p]`,
  `Finite 𝓀[ℚ_[p]]`, `CharP 𝓀[ℚ_[p]] p`, `Infinite ℤ_[p]ˣ`
* `residueChar_padic : residueChar ℚ_[p] = p`
* `padicUnitBall_normalizedValuation_p`
-/

@[expose] public section

namespace FalseTateExtension

noncomputable section

open FontaineWintenberger IsDiscreteValuationRing

variable (p : ℕ) [Fact p.Prime]

/-- The valuation subring of `ℚ_[p]` and `ℤ_[p]` have the same carrier. -/
theorem padic_valuationSubring_toSubring : 𝒪[ℚ_[p]].toSubring = PadicInt.subring p := by
  ext x
  rfl

/-- `𝒪[ℚ_[p]] ≃+* ℤ_[p]`, the identity on elements. -/
def padicUnitBallEquiv : 𝒪[ℚ_[p]] ≃+* ℤ_[p] :=
  RingEquiv.subringCongr (padic_valuationSubring_toSubring p)

/-- The residue field of `𝒪[ℚ_[p]]` is the prime field. -/
def padicUnitBallResidueEquiv : 𝓀[ℚ_[p]] ≃+* ZMod p :=
  (IsLocalRing.ResidueField.mapEquiv (padicUnitBallEquiv p)).trans (PadicInt.residueField (p := p))

instance padicUnitBall_isDiscreteValuationRing : IsDiscreteValuationRing 𝒪[ℚ_[p]] :=
  RingEquivClass.isDiscreteValuationRing (padicUnitBallEquiv p).symm

instance padic_isCompleteDiscreteValuedField : IsCompleteDiscreteValuedField ℚ_[p] where

instance padicUnitBall_residueFinite : Finite 𝓀[ℚ_[p]] :=
  Finite.of_injective (padicUnitBallResidueEquiv p) (padicUnitBallResidueEquiv p).injective

instance padicUnitBall_residueCharP : CharP 𝓀[ℚ_[p]] p where
  cast_eq_zero_iff n := by
    rw [← (padicUnitBallResidueEquiv p).injective.eq_iff, map_natCast, map_zero]
    exact CharP.cast_eq_zero_iff (ZMod p) p n

instance padic_isPerfectResidueLocalField : IsPerfectResidueLocalField ℚ_[p] :=
  IsPerfectResidueLocalField.of_charP ℚ_[p] p

@[simp] theorem residueChar_padic : residueChar ℚ_[p] = p :=
  residueChar_eq ℚ_[p] p

/-- The normalized valuation of `ℚ_[p]` sends `p` to `exp (-1)`. -/
theorem padicUnitBall_normalizedValuation_p :
    (maximalIdeal 𝒪[ℚ_[p]]).valuation ℚ_[p] (p : ℚ_[p]) = WithZero.exp (-1 : ℤ) := by
  let π : 𝒪[ℚ_[p]] := (padicUnitBallEquiv p).symm (p : ℤ_[p])
  have hπ : Irreducible π :=
    (MulEquiv.irreducible_iff (f := (padicUnitBallEquiv p).symm)).mpr PadicInt.irreducible_p
  change (maximalIdeal 𝒪[ℚ_[p]]).valuation ℚ_[p] (algebraMap 𝒪[ℚ_[p]] ℚ_[p] π) = _
  rw [IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap]
  exact (maximalIdeal 𝒪[ℚ_[p]]).intValuation_singleton hπ.ne_zero hπ.maximalIdeal_eq

/-- The principal units `1 + p n`, `n : ℕ`, are pairwise distinct. -/
instance padicUnits_infinite : Infinite ℤ_[p]ˣ := by
  have hu (n : ℕ) : IsUnit (1 + (p : ℤ_[p]) * n) := by
    have hp : ‖(p : ℤ_[p])‖ < 1 := PadicInt.mem_nonunits.mp PadicInt.p_nonunit
    have hn : ‖(p : ℤ_[p]) * n‖ < 1 := by
      rw [mul_comm]
      exact PadicInt.norm_lt_one_mul hp
    apply PadicInt.isUnit_iff.mpr
    rw [PadicInt.norm_add_eq_max_of_ne (by simpa only [norm_one] using ne_of_gt hn)]
    simp only [norm_one, max_eq_left hn.le]
  let f : ℕ → ℤ_[p]ˣ := fun n ↦ (hu n).unit
  apply Infinite.of_injective f
  intro n m h
  have hv : 1 + (p : ℤ_[p]) * n = 1 + (p : ℤ_[p]) * m := by
    simpa only [f, IsUnit.unit_spec] using congrArg Units.val h
  have hnm : (n : ℤ_[p]) = m :=
    mul_left_cancel₀ (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero) (add_left_cancel hv)
  exact_mod_cast hnm

end

end FalseTateExtension
