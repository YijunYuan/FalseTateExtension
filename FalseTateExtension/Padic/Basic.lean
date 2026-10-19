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

`ℚ_[p]` is a complete discretely valued field whose valuation subring `𝒪[ℚ_[p]]` is `ℤ_[p]` and
whose residue field `𝓀[ℚ_[p]]` is the prime field `ZMod p`; in particular the residue field is
finite and perfect, so `ℚ_[p]` satisfies the standing hypotheses of `FontaineWintenberger`. The
normalized valuation of `p` is `exp (-1)`, the residue characteristic is `p`, and the unit group
`ℤ_[p]ˣ` is infinite. A uniformizer `π : 𝒪[K]` of an ultrametric field is nonzero.

## Main results

* `padicUnitBallEquiv : 𝒪[ℚ_[p]] ≃+* ℤ_[p]` and `padicUnitBallResidueEquiv : 𝓀[ℚ_[p]] ≃+* ZMod p`
* `padic_isCompleteDiscreteValuedField`, `padic_isPerfectResidueLocalField`: the
  `FontaineWintenberger` instances for `ℚ_[p]`
* `padicUnitBall_residueFinite`, `padicUnitBall_residueCharP`: `𝓀[ℚ_[p]]` is finite of
  characteristic `p`
* `residueChar_padic : residueChar ℚ_[p] = p`
* `padicUnitBall_normalizedValuation_p`: the normalized valuation of `p` is `exp (-1)`
* `padicUnits_infinite`: `ℤ_[p]ˣ` is infinite
-/

@[expose] public section

namespace FalseTateExtension

noncomputable section

open FontaineWintenberger IsDiscreteValuationRing

variable (p : ℕ) [Fact p.Prime]

/-- The valuation subring `𝒪[ℚ_[p]]` and `ℤ_[p]` are the same subring of `ℚ_[p]`. -/
theorem padic_valuationSubring_toSubring : 𝒪[ℚ_[p]].toSubring = PadicInt.subring p := by
  ext x
  rfl

/-- The ring isomorphism `𝒪[ℚ_[p]] ≃+* ℤ_[p]`, the identity on elements of `ℚ_[p]`. -/
def padicUnitBallEquiv : 𝒪[ℚ_[p]] ≃+* ℤ_[p] :=
  RingEquiv.subringCongr (padic_valuationSubring_toSubring p)

/-- The residue field `𝓀[ℚ_[p]]` is the prime field `ZMod p`. -/
def padicUnitBallResidueEquiv : 𝓀[ℚ_[p]] ≃+* ZMod p :=
  (IsLocalRing.ResidueField.mapEquiv (padicUnitBallEquiv p)).trans (PadicInt.residueField (p := p))

/-- `𝒪[ℚ_[p]]` is a discrete valuation ring. -/
instance padicUnitBall_isDiscreteValuationRing : IsDiscreteValuationRing 𝒪[ℚ_[p]] :=
  RingEquivClass.isDiscreteValuationRing (padicUnitBallEquiv p).symm

/-- `ℚ_[p]` is a complete discretely valued field. -/
instance padic_isCompleteDiscreteValuedField : IsCompleteDiscreteValuedField ℚ_[p] where

/-- The residue field `𝓀[ℚ_[p]]` is finite. -/
instance padicUnitBall_residueFinite : Finite 𝓀[ℚ_[p]] :=
  Finite.of_injective (padicUnitBallResidueEquiv p) (padicUnitBallResidueEquiv p).injective

/-- The residue field `𝓀[ℚ_[p]]` has characteristic `p`. -/
instance padicUnitBall_residueCharP : CharP 𝓀[ℚ_[p]] p where
  cast_eq_zero_iff n := by
    rw [← (padicUnitBallResidueEquiv p).injective.eq_iff, map_natCast, map_zero]
    exact CharP.cast_eq_zero_iff (ZMod p) p n

/-- `ℚ_[p]` is a complete discretely valued field with perfect residue field. -/
instance padic_isPerfectResidueLocalField : IsPerfectResidueLocalField ℚ_[p] :=
  IsPerfectResidueLocalField.of_charP ℚ_[p] p

/-- The residue characteristic of `ℚ_[p]` is `p`. -/
@[simp] theorem residueChar_padic : residueChar ℚ_[p] = p :=
  residueChar_eq ℚ_[p] p

/-- The normalized valuation of `ℚ_[p]` takes the value `exp (-1)` at `p`. -/
theorem padicUnitBall_normalizedValuation_p :
    (maximalIdeal 𝒪[ℚ_[p]]).valuation ℚ_[p] (p : ℚ_[p]) = WithZero.exp (-1 : ℤ) := by
  let π : 𝒪[ℚ_[p]] := (padicUnitBallEquiv p).symm (p : ℤ_[p])
  have hπ : Irreducible π :=
    (MulEquiv.irreducible_iff (f := (padicUnitBallEquiv p).symm)).mpr PadicInt.irreducible_p
  change (maximalIdeal 𝒪[ℚ_[p]]).valuation ℚ_[p] (algebraMap 𝒪[ℚ_[p]] ℚ_[p] π) = _
  rw [IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap]
  exact (maximalIdeal 𝒪[ℚ_[p]]).intValuation_singleton hπ.ne_zero hπ.maximalIdeal_eq

/-- The unit group `ℤ_[p]ˣ` is infinite. -/
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

section Uniformizer

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] (π : 𝒪[K])
  [Fact (Irreducible π)]

/-- A uniformizer `π : 𝒪[K]` is nonzero. -/
instance neZero_of_irreducible : NeZero π := ⟨(Fact.out : Irreducible π).ne_zero⟩

/-- A uniformizer `π : 𝒪[K]` is nonzero as an element of `K`. -/
instance neZero_coe_of_irreducible : NeZero (π : K) :=
  ⟨fun h => (Fact.out : Irreducible π).ne_zero (Subtype.ext h)⟩

end Uniformizer

end

end FalseTateExtension
