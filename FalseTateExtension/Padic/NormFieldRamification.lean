/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FalseTateExtension.Padic.KummerRamification
public import FalseTateExtension.StrictAPF
public import FontaineWintenberger.FieldOfNorms.Basic.Ring
public import FontaineWintenberger.FieldOfNorms.Functor.Map
public import FontaineWintenberger.FieldOfNorms.Structure.Uniformizer

/-!
# Actual Kummer displacement on the original field of norms

The stable finite diagonal orders determine the displacement of every actual
norm-compatible uniformizer. The action is the literal original norm-field
action, and no general ramification-transfer theorem is assumed.

References: Yuan, Proposition 5.1; Viviani, Corollary 6.10.
-/

@[expose] public section

noncomputable section

namespace FalseTateExtension

open FontaineWintenberger IsDiscreteValuationRing

variable (p : ℕ) [Fact p.Prime]
variable {π : (NormedField.valuation (K := Padic p)).valuationSubring}

section DiagonalCoordinates

variable (π : Padic p)

/-- The original diagonal field inside the original infinite false Tate field. -/
def falseTateNormFiniteLayer (N : ℕ) :
    FiniteIntermediateField (Padic p) (falseTateExtension p π) := by
  let i := IntermediateField.inclusion (falseTateLayer_le_falseTateExtension p π N N)
  exact ⟨i.fieldRange, Module.Finite.equiv i.equivFieldRange.toLinearEquiv⟩

/-- The original inclusion, restricted to its exact field range. -/
def falseTateNormFiniteLayerEquiv (N : ℕ) :
    falseTateLayer p π N N ≃ₐ[Padic p] (falseTateNormFiniteLayer p π N).val :=
  (IntermediateField.inclusion (falseTateLayer_le_falseTateExtension p π N N)).equivFieldRange

/-- The diagonal fields are cofinal among all original finite subfields. -/
theorem exists_le_falseTateNormFiniteLayer
    (E : FiniteIntermediateField (Padic p) (falseTateExtension p π)) :
    ∃ N, E ≤ falseTateNormFiniteLayer p π N := by
  classical
  have hfg : E.val.FG := IntermediateField.essFiniteType_iff.mp inferInstance
  obtain ⟨s, hs⟩ := hfg
  have hx (x : falseTateExtension p π) :
      ∃ N, (x : AlgebraicClosure (Padic p)) ∈ falseTateLayer p π N N :=
    (mem_falseTateExtension_iff_diagonal p π (x : AlgebraicClosure (Padic p))).mp x.property
  choose level hlevel using hx
  refine ⟨s.sup level, ?_⟩
  change E.val ≤ (falseTateNormFiniteLayer p π (s.sup level)).val
  rw [← hs]
  apply IntermediateField.adjoin_le_iff.mpr
  intro x hx
  have hmem : (x : AlgebraicClosure (Padic p)) ∈
      falseTateLayer p π (s.sup level) (s.sup level) :=
    falseTateLayer_mono p π (Finset.le_sup (f := level) hx)
      (Finset.le_sup (f := level) hx) (hlevel x)
  change ∃ y : falseTateLayer p π (s.sup level) (s.sup level),
    IntermediateField.inclusion (falseTateLayer_le_falseTateExtension p π _ _) y = x
  exact ⟨⟨x, hmem⟩, Subtype.ext rfl⟩

theorem falseTateNormFiniteLayer_mono {M N : ℕ} (h : M ≤ N) :
    falseTateNormFiniteLayer p π M ≤ falseTateNormFiniteLayer p π N := by
  rintro x ⟨y, rfl⟩
  exact ⟨IntermediateField.inclusion (falseTateLayer_mono p π h h) y, rfl⟩

/-- The actual infinite false Tate extension is not a finite extension. -/
theorem not_finiteDimensional_falseTateExtension_padic :
    ¬ Module.Finite (Padic p) (falseTateExtension p π) := by
  intro h
  let := h
  obtain ⟨m, hm⟩ := cyclotomicLayer_padic_degrees_unbounded p
    (Module.finrank (Padic p) (falseTateExtension p π))
  exact (not_lt_of_ge (IntermediateField.finrank_le_of_le_right
    ((show cyclotomicLayer p m ≤ falseTateLayer p π m m from le_sup_right).trans
      (falseTateLayer_le_falseTateExtension p π m m)))) hm

/-- Original diagonal Galois normality is preserved by its inclusion. -/
theorem falseTateNormFiniteLayer_isGalois (hπ : π ≠ 0) (N : ℕ) :
    IsGalois (Padic p) (falseTateNormFiniteLayer p π N).val := by
  have := falseTateLayer_isGalois p π hπ N
  exact IsGalois.of_algEquiv (falseTateNormFiniteLayerEquiv p π N)

/-- At a normal original finite field the literal norm action is the
ordinary finite restriction, under its original inclusion. -/
theorem coe_normLimitEval_normLimitMap_of_normal
    (E : FiniteIntermediateField (Padic p) (falseTateExtension p π)) [Normal (Padic p) E.val]
    (g : falseTateExtension p π ≃ₐ[Padic p] falseTateExtension p π)
    (x : FieldOfNorms (Padic p) (falseTateExtension p π)) :
    (FieldOfNorms.coord (Padic p) (falseTateExtension p π) E (FieldOfNorms.mapFun g x) :
      falseTateExtension p π) =
      g (FieldOfNorms.coord (Padic p) (falseTateExtension p π) E x) := by
  have hmap : FiniteIntermediateField.map g.symm.toAlgHom E = E := by
    apply Subtype.ext
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      change g.symm z ∈ E.val
      simpa only [AlgEquiv.restrictNormal_apply] using
        (g.symm.restrictNormal E.val ⟨z, hz⟩).property
    · intro hy
      refine ⟨g y, ?_, g.symm_apply_apply y⟩
      change g y ∈ E.val
      simpa only [AlgEquiv.restrictNormal_apply] using
        (g.restrictNormal E.val ⟨y, hy⟩).property
  rw [FieldOfNorms.coe_coord_mapFun]
  exact congrArg g (congrArg
    (fun D : FiniteIntermediateField (Padic p) (falseTateExtension p π) =>
      (FieldOfNorms.coord (Padic p) (falseTateExtension p π) D x : falseTateExtension p π)) hmap)

/-- Original diagonal coordinates intertwine the actual infinite action
and the ordinary finite restriction. -/
theorem normLimitEval_normLimitMap_diagonal (hπ : π ≠ 0) (N : ℕ)
    (g : falseTateExtension p π ≃ₐ[Padic p] falseTateExtension p π)
    (x : FieldOfNorms (Padic p) (falseTateExtension p π)) :
    (falseTateNormFiniteLayerEquiv p π N).symm
        (FieldOfNorms.coord (Padic p) (falseTateExtension p π)
          (falseTateNormFiniteLayer p π N) (FieldOfNorms.mapFun g x)) =
      infiniteLayerRestriction p π hπ N g
        ((falseTateNormFiniteLayerEquiv p π N).symm
          (FieldOfNorms.coord (Padic p) (falseTateExtension p π)
            (falseTateNormFiniteLayer p π N) x)) := by
  let := falseTateNormFiniteLayer_isGalois p π hπ N
  let e := falseTateNormFiniteLayerEquiv p π N
  let i := IntermediateField.inclusion (falseTateLayer_le_falseTateExtension p π N N)
  have hi (y : (falseTateNormFiniteLayer p π N).val) :
      i (e.symm y) = (y : falseTateExtension p π) := by
    change (e (e.symm y) : falseTateExtension p π) = _
    rw [e.apply_symm_apply]
  apply i.injective
  calc
    _ = (FieldOfNorms.coord (Padic p) (falseTateExtension p π)
        (falseTateNormFiniteLayer p π N) (FieldOfNorms.mapFun g x) : falseTateExtension p π) := hi _
    _ = g (FieldOfNorms.coord (Padic p) (falseTateExtension p π)
        (falseTateNormFiniteLayer p π N) x) :=
      coe_normLimitEval_normLimitMap_of_normal p π _ g x
    _ = g (i (e.symm (FieldOfNorms.coord (Padic p) (falseTateExtension p π)
        (falseTateNormFiniteLayer p π N) x))) := congrArg g (hi _).symm
    _ = _ := (infiniteLayerRestriction_commutes p π hπ N g _).symm

end DiagonalCoordinates

private theorem irreducible_of_normalizedValuation_eq_exp_neg_one
    {F : Type*} [Field F] (A : ValuationSubring F) [IsDiscreteValuationRing A]
    (z : A) (hz : (maximalIdeal A).valuation F (z : F) = WithZero.exp (-1 : ℤ)) :
    Irreducible z := by
  have hne : z ≠ 0 := by
    intro h
    rw [h, ZeroMemClass.coe_zero, map_zero] at hz
    exact WithZero.exp_ne_zero hz.symm
  obtain ⟨ϖ, hϖ⟩ := exists_irreducible A
  obtain ⟨n, u, heq⟩ := eq_unit_mul_pow_irreducible hne hϖ
  have hv := hz
  change (maximalIdeal A).valuation F (algebraMap A F z) = _ at hv
  rw [IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap,
    intValuation_maximalIdeal, heq, addVal_def' u hϖ,
    ENat.recTopCoe_natCast] at hv
  have hn : n = 1 := by
    have hi := WithZero.exp_injective hv
    change -(n : ℤ) = -1 at hi
    omega
  rw [heq, hn, pow_one]
  exact (show Associated ϖ (↑u * ϖ) from ⟨u, mul_comm _ _⟩).irreducible hϖ

section ActualNormField

variable (hp₂ : p ≠ 2) (hπ : Irreducible π)

local notation "L" => falseTateExtension p (π : Padic p)
local notation "X" => FieldOfNorms (Padic p) L
local instance normFieldRamificationInfinite : Fact (¬ Module.Finite (Padic p) L) :=
  ⟨not_finiteDimensional_falseTateExtension_padic p (π : Padic p)⟩

/-- The ordinary diagonal-coordinate difference has its finite Kummer order
whenever that coordinate is an original uniformizer. -/
theorem normalizedValuation_normLimitMap_tau_diagonal (N k : ℕ) (hk : k + 2 ≤ N)
    (u : X)
    (hu : FieldOfNorms.coordinateValuation (Padic p) L
      (falseTateNormFiniteLayer p (π : Padic p) N) u = WithZero.exp (-1 : ℤ)) :
    (maximalIdeal (spectralIntegerRing (Padic p)
      (falseTateNormFiniteLayer p (π : Padic p) N).val)).valuation
        (falseTateNormFiniteLayer p (π : Padic p) N).val
        (FieldOfNorms.coord (Padic p) L (falseTateNormFiniteLayer p (π : Padic p) N)
          (FieldOfNorms.mapFun ((tau p hp₂ hπ).val ^ (p ^ k)) u) -
          FieldOfNorms.coord (Padic p) L (falseTateNormFiniteLayer p (π : Padic p) N) u) =
      WithZero.exp (-(kummerRamificationBreak p k + 1 : ℕ) : ℤ) := by
  let E := falseTateNormFiniteLayer p (π : Padic p) N
  let e := falseTateNormFiniteLayerEquiv p (π : Padic p) N
  let v := (maximalIdeal (spectralIntegerRing (Padic p) E.val)).valuation E.val
  have hule : v (FieldOfNorms.coord (Padic p) L E u) ≤ 1 := by
    change FieldOfNorms.coordinateValuation (Padic p) L E u ≤ 1
    rw [hu]
    change WithZero.exp (-1 : ℤ) ≤ WithZero.exp (0 : ℤ)
    exact WithZero.exp_le_exp.mpr (by omega)
  have hmem : FieldOfNorms.coord (Padic p) L E u ∈ spectralIntegerRing (Padic p) E.val := by
    rw [← ValuationSubring.normalizedValuation_valuationSubring
      (spectralIntegerRing (Padic p) E.val)]
    exact hule
  let zE : spectralIntegerRing (Padic p) E.val := ⟨FieldOfNorms.coord (Padic p) L E u, hmem⟩
  let zD := spectralIntegerRingEquiv (Padic p) e.symm zE
  have hzD : (maximalIdeal (spectralIntegerRing (Padic p)
      (falseTateLayer p (π : Padic p) N N))).valuation
        (falseTateLayer p (π : Padic p) N N) (zD : falseTateLayer p (π : Padic p) N N) =
      WithZero.exp (-1 : ℤ) := by
    rw [coe_spectralIntegerRingEquiv,
      spectral_normalizedValuation_algEquiv (Padic p) e.symm]
    exact hu
  have hirr := irreducible_of_normalizedValuation_eq_exp_neg_one _ zD hzD
  have hfin := normalizedValuation_kummerTauFinite_displacement p hp₂ hπ N k hk hirr
  have hv := spectral_normalizedValuation_algEquiv (Padic p) e.symm
    (FieldOfNorms.coord (Padic p) L E (FieldOfNorms.mapFun ((tau p hp₂ hπ).val ^ (p ^ k)) u) -
      FieldOfNorms.coord (Padic p) L E u)
  rw [map_sub e.symm] at hv
  rw [normLimitEval_normLimitMap_diagonal p (π : Padic p)
    (fun h => hπ.ne_zero (Subtype.ext h))] at hv
  have hzcoe : (zD : falseTateLayer p (π : Padic p) N N) =
      e.symm (FieldOfNorms.coord (Padic p) L E u) :=
    coe_spectralIntegerRingEquiv (Padic p) e.symm zE
  change (maximalIdeal (spectralIntegerRing (Padic p)
      (falseTateLayer p (π : Padic p) N N))).valuation
        (falseTateLayer p (π : Padic p) N N)
        (kummerTauFinite p hp₂ hπ N k
          (e.symm (FieldOfNorms.coord (Padic p) L E u)) -
            e.symm (FieldOfNorms.coord (Padic p) L E u)) = _ at hv
  rw [hzcoe] at hfin
  exact hv.symm.trans hfin

/-- Cofinal ordinary diagonal-coordinate differences have their exact
Kummer values, obtained from the actual stable valuation of a uniformizer. -/
theorem exists_normLimitMap_tau_coordinate_displacement (u : X)
    (hu : letI := isAPF_falseTateExtension p hπ
      FieldOfNorms.valuation (Padic p) L u = WithZero.exp (-1 : ℤ))
    (k : ℕ) (T : FiniteIntermediateField (Padic p) L) :
    letI := isAPF_falseTateExtension p hπ
    ∃ E : FiniteIntermediateField (Padic p) L, T ≤ E ∧
      (maximalIdeal (spectralIntegerRing (Padic p) E.val)).valuation E.val
        (FieldOfNorms.coord (Padic p) L E
          (FieldOfNorms.mapFun ((tau p hp₂ hπ).val ^ (p ^ k)) u) -
          FieldOfNorms.coord (Padic p) L E u) =
        WithZero.exp (-(kummerRamificationBreak p k + 1 : ℕ) : ℤ) := by
  have := isAPF_falseTateExtension p hπ
  obtain ⟨S, hS⟩ := FieldOfNorms.exists_valuation_eq_coordinateValuation (Padic p) L
  obtain ⟨M, hM⟩ := exists_le_falseTateNormFiniteLayer p (π : Padic p)
    (FiniteIntermediateField.sup T S)
  let N := max M (k + 2)
  let E := falseTateNormFiniteLayer p (π : Padic p) N
  have hME : falseTateNormFiniteLayer p (π : Padic p) M ≤ E :=
    falseTateNormFiniteLayer_mono p (π : Padic p) (Nat.le_max_left _ _)
  have hTE : T ≤ E := (FiniteIntermediateField.le_sup_left T S).trans (hM.trans hME)
  have hSE : S ≤ E := (FiniteIntermediateField.le_sup_right T S).trans (hM.trans hME)
  refine ⟨E, hTE, ?_⟩
  have hcoord := (hS E hSE u).symm.trans hu
  exact normalizedValuation_normLimitMap_tau_diagonal p hp₂ hπ N k
    (Nat.le_max_right M (k + 2)) u hcoord

/-- Every actual norm-family uniformizer has the exact displacement of the
prescribed Kummer power, on the same original norm-field carrier. -/
theorem normLimitValuation_tau_pow_displacement :
    letI := isAPF_falseTateExtension p hπ
    ∀ (u : X), FieldOfNorms.valuation (Padic p) L u = WithZero.exp (-1 : ℤ) →
      ∀ k : ℕ, FieldOfNorms.valuation (Padic p) L
        (FieldOfNorms.aut (Padic p) L ((tau p hp₂ hπ).val ^ (p ^ k)) u - u) =
          WithZero.exp (-(kummerRamificationBreak p k + 1 : ℕ) : ℤ) := by
  have := isAPF_falseTateExtension p hπ
  intro u hu k
  apply FieldOfNorms.valuation_sub_eq_of_cofinal_coordinate (Padic p) L
  intro T
  obtain ⟨E, hE, hv⟩ := exists_normLimitMap_tau_coordinate_displacement p hp₂ hπ u hu k T
  refine ⟨E, hE, ?_⟩
  have heq := FieldOfNorms.aut_apply
    ((tau p hp₂ hπ).val ^ (p ^ k)) u
  exact (congrArg (fun z : X =>
    (maximalIdeal (spectralIntegerRing (Padic p) E.val)).valuation E.val
      (FieldOfNorms.coord (Padic p) L E z - FieldOfNorms.coord (Padic p) L E u)) heq).trans hv

/-- Dividing the actual displacement by any original uniformizer gives the
source's shifted lower break. -/
theorem normLimitValuation_tau_pow_div_sub_one :
    letI := isAPF_falseTateExtension p hπ
    ∀ (u : X), FieldOfNorms.valuation (Padic p) L u = WithZero.exp (-1 : ℤ) →
      ∀ k : ℕ, FieldOfNorms.valuation (Padic p) L
        (FieldOfNorms.aut (Padic p) L ((tau p hp₂ hπ).val ^ (p ^ k)) u / u - 1) =
          WithZero.exp (-(kummerRamificationBreak p k : ℤ)) := by
  have := isAPF_falseTateExtension p hπ
  intro u hu k
  have hne : u ≠ 0 := by
    intro h
    rw [h, map_zero] at hu
    exact WithZero.exp_ne_zero hu.symm
  have heq : FieldOfNorms.aut (Padic p) L
      ((tau p hp₂ hπ).val ^ (p ^ k)) u / u - 1 =
      (FieldOfNorms.aut (Padic p) L
        ((tau p hp₂ hπ).val ^ (p ^ k)) u - u) / u := by field_simp
  change FieldOfNorms.fieldValuation (Padic p) L _ = _
  rw [heq, map_div₀]
  change FieldOfNorms.valuation (Padic p) L _ /
    FieldOfNorms.valuation (Padic p) L u = _
  rw [normLimitValuation_tau_pow_displacement p hp₂ hπ u hu k, hu,
    ← WithZero.exp_sub]
  congr 1
  push_cast
  ring

/-- Distinct prescribed prime-power iterates remain distinct under the
literal action on the same original norm field. -/
theorem normLimitTau_primePower_injective :
    letI := isAPF_falseTateExtension p hπ
    Function.Injective (fun k : ℕ =>
      (FieldOfNorms.aut (Padic p) L (tau p hp₂ hπ).val) ^ (p ^ k)) := by
  have := isAPF_falseTateExtension p hπ
  intro i j hij
  let u := FieldOfNorms.uniformizer (Padic p) L
  have hu := FieldOfNorms.valuation_uniformizer (Padic p) L
  have hi := normLimitValuation_tau_pow_displacement p hp₂ hπ u hu i
  have hj := normLimitValuation_tau_pow_displacement p hp₂ hπ u hu j
  have hpow : FieldOfNorms.aut (Padic p) L ((tau p hp₂ hπ).val ^ (p ^ i)) =
      FieldOfNorms.aut (Padic p) L ((tau p hp₂ hπ).val ^ (p ^ j)) := by
    simpa only [map_pow] using hij
  have hv := congrArg (fun a : X ≃+* X =>
    FieldOfNorms.valuation (Padic p) L (a u - u)) hpow
  have hd : kummerRamificationBreak p i = kummerRamificationBreak p j := by
    have he := WithZero.exp_injective (hi.symm.trans (hv.trans hj))
    change -((kummerRamificationBreak p i + 1 : ℕ) : ℤ) =
      -((kummerRamificationBreak p j + 1 : ℕ) : ℤ) at he
    omega
  exact (kummerRamificationBreak_strictMono p (Fact.out : p.Prime).two_le).injective hd

/-- The actual Kummer action on the original norm field has infinite order. -/
theorem normLimitTau_infiniteOrder :
    letI := isAPF_falseTateExtension p hπ
    ¬ IsOfFinOrder (FieldOfNorms.aut (Padic p) L (tau p hp₂ hπ).val) := by
  have := isAPF_falseTateExtension p hπ
  intro h
  apply h.finite_powers.not_infinite
  apply Set.infinite_of_injective_forall_mem (normLimitTau_primePower_injective p hp₂ hπ)
  intro k
  exact ⟨p ^ k, rfl⟩

end ActualNormField

end FalseTateExtension
