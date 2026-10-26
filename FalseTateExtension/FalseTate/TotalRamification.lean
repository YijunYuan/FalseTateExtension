/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FalseTateExtension.Cyclotomic.Filtration
public import FalseTateExtension.Cyclotomic.InfiniteCharacter
public import FalseTateExtension.FalseTate.FiniteGaloisGroup
public import FalseTateExtension.FalseTate.LiuLemma
public import FontaineWintenberger.APF.Tower.Residue
public import FontaineWintenberger.APF.Tower.TotallyRamified
public import FontaineWintenberger.Ramification.Different.Subextension
public import FontaineWintenberger.Ramification.Lower.FiniteResidue
public import FontaineWintenberger.Ramification.Lower.Inertia
public import FontaineWintenberger.Ramification.Upper.ResidueEquiv
public import Mathlib.Data.ZMod.Units
public import Mathlib.FieldTheory.Finite.Basic

/-!
# Total ramification of the false Tate extension of `ℚ_p`

Let `p ≠ 2` and let `π` be a uniformizer of `ℚ_p`. Every finite subextension `E` of
`K_FT = ℚ_p(π^{1/p^∞}, ζ_{p^∞})` is totally ramified over `ℚ_p`: its residue degree is `1`
(`finiteSubextension_falseTate_residueDegree_padic`) and its ramification index is `[E : ℚ_p]`
(`finiteSubextension_falseTate_ramificationIdx_padic`). Equivalently the residue field of the
valuation ring of `K_FT` is `𝔽_p` (`falseTateExtension_residueDegree_padic`).

The proof goes through the finite layers `ℚ_p(π^{1/p^{n+1}}, ζ_{p^{n+1}})`, whose Galois group is
`ℤ/p^{n+1} ⋊ (ℤ/p^{n+1})ˣ`: the translations are commutators (with the unit `2`, hence `p ≠ 2`)
and therefore lie in inertia. Their fixed field is the cyclotomic subfield, which is totally
ramified. Its residue degree then shows that inertia is the whole Galois group
(`lowerRamificationGroup_falseTateLayer_zero`).

## Main results

* `falseTateLayer_spectral_ramificationIdx`:
  `e(ℚ_p(π^{1/p^{n+1}}, ζ_{p^{n+1}})/ℚ_p) = p^{n+1} φ(p^{n+1})`.
* `falseTateExtension_residueDegree_padic`: the residue field of `K_FT` is `𝔽_p`.
* `finiteSubextension_falseTate_ramificationIdx_padic`: every finite subextension of `K_FT/ℚ_p`
  is totally ramified.

## References

* [Viviani, *Ramification groups and Artin conductors of radical extensions of
  ℚ*](https://doi.org/10.5802/jtnb.470), §6.
-/

@[expose] public section

noncomputable section

namespace FalseTateExtension

open FontaineWintenberger

section RationalTotalRamification

open scoped commutatorElement

variable (p : ℕ) [Fact p.Prime]
variable (π : 𝒪[ℚ_[p]])

/-- Oddness makes the affine multiplier two invertible at every
finite level, including the zeroth level. -/
def unitTwo [hp₂ : Fact (p ≠ 2)] (n : ℕ) : (ZMod (p ^ n))ˣ :=
  ZMod.unitOfCoprime 2 (by
    have hp : p.Coprime 2 := (Fact.out : p.Prime).coprime_iff_not_dvd.mpr (by
      intro h
      have hle := Nat.le_of_dvd (by decide : 0 < 2) h
      exact hp₂.out (le_antisymm hle (Fact.out : p.Prime).two_le))
    exact hp.symm.pow_right n)

/-- The unit `unitTwo p n` has underlying residue class `2`. -/
@[simp]
theorem coe_unitTwo [hp₂ : Fact (p ≠ 2)] (n : ℕ) :
    (unitTwo p n : ZMod (p ^ n)) = 2 := ZMod.coe_unitOfCoprime _ _

/-- Every translation in the rational finite Galois group
belongs to its inertia subgroup. -/
theorem finiteDiagonal_translation_mem_inertia
    [hp₂ : Fact (p ≠ 2)] [hπ : Fact (Irreducible π)] (n : ℕ) (b : ZMod (p ^ n)) :
    (finiteDiagonalGaloisEquivPadic p π n).symm
        (SemidirectProduct.inl (Multiplicative.ofAdd b)) ∈
      lowerRamificationGroup
        (falseTateLayer p (π : ℚ_[p]) n n ≃ₐ[ℚ_[p]] falseTateLayer p (π : ℚ_[p]) n n)
        (IsLocalRing.maximalIdeal (spectralIntegerRing (ℚ_[p])
          (falseTateLayer p (π : ℚ_[p]) n n))) 0 := by
  have := falseTateLayer_isGalois p (π : ℚ_[p]) n
  let e := finiteDiagonalGaloisEquivPadic p π n
  let δ := e.symm (SemidirectProduct.inr (unitTwo p n))
  let t₀ := e.symm (SemidirectProduct.inl (Multiplicative.ofAdd b))
  have h := commutatorElement_mem_lowerRamificationGroup_zero (ℚ_[p])
    (falseTateLayer p (π : ℚ_[p]) n n) δ t₀
  have heq : ⁅δ, t₀⁆ = t₀ := by
    apply e.injective
    rw [map_commutatorElement]
    change ⁅e (e.symm (SemidirectProduct.inr (unitTwo p n))),
      e (e.symm (SemidirectProduct.inl (Multiplicative.ofAdd b)))⁆ =
        e (e.symm (SemidirectProduct.inl (Multiplicative.ofAdd b)))
    rw [e.apply_symm_apply, e.apply_symm_apply, finiteAffine_commutator_inl]
    simp only [SemidirectProduct.right_inr, coe_unitTwo]
    rw [show (2 : ZMod (p ^ n)) - 1 = 1 by ring, one_mul]
  rwa [heq] at h

/-- The finite cyclotomic fixing subgroup lies in the
inertia group; no total ramification is assumed. -/
theorem finiteCyclotomicFixing_le_inertia [hp₂ : Fact (p ≠ 2)] [hπ : Fact (Irreducible π)] (n : ℕ) :
    (finiteCyclotomicInclusion p (π : ℚ_[p]) n).fieldRange.fixingSubgroup ≤
      lowerRamificationGroup
        (falseTateLayer p (π : ℚ_[p]) n n ≃ₐ[ℚ_[p]] falseTateLayer p (π : ℚ_[p]) n n)
        (IsLocalRing.maximalIdeal (spectralIntegerRing (ℚ_[p])
          (falseTateLayer p (π : ℚ_[p]) n n))) 0 := by
  intro g hg
  obtain ⟨b, hb⟩ := (finiteDiagonalGaloisEquivPadic_mem_translations p π n g).mpr hg
  have h := finiteDiagonal_translation_mem_inertia p π n b.toAdd
  have heq : (finiteDiagonalGaloisEquivPadic p π n).symm
      (SemidirectProduct.inl b) = g := by
    rw [hb, (finiteDiagonalGaloisEquivPadic p π n).symm_apply_apply]
  exact heq ▸ h

/-- Every positive rational diagonal layer has full inertia,
including the first layer, at an odd prime. -/
theorem lowerRamificationGroup_falseTateLayer_zero
    [hp₂ : Fact (p ≠ 2)] [hπ : Fact (Irreducible π)] (n : ℕ) :
    lowerRamificationGroup
      (falseTateLayer p (π : ℚ_[p]) (n + 1) (n + 1) ≃ₐ[ℚ_[p]]
        falseTateLayer p (π : ℚ_[p]) (n + 1) (n + 1))
      (IsLocalRing.maximalIdeal (spectralIntegerRing (ℚ_[p])
        (falseTateLayer p (π : ℚ_[p]) (n + 1) (n + 1)))) 0 = ⊤ := by
  let D := falseTateLayer p (π : ℚ_[p]) (n + 1) (n + 1)
  have := falseTateLayer_isGalois p (π : ℚ_[p]) (n + 1)
  let i := finiteCyclotomicInclusion p (π : ℚ_[p]) (n + 1)
  let I := lowerRamificationGroup (D ≃ₐ[ℚ_[p]] D)
    (IsLocalRing.maximalIdeal (spectralIntegerRing (ℚ_[p]) D)) 0
  have hidx := fixingSubgroup_sup_lowerRamificationGroup_zero_index_eq_residueDegree (ℚ_[p])
    D i.fieldRange
  rw [sup_eq_right.mpr (finiteCyclotomicFixing_le_inertia p π (n + 1)),
    spectral_residueDegree_algEquiv (ℚ_[p]) (cyclotomicLayer (K := ℚ_[p]) p (n + 1))
      i.equivFieldRange,
    cyclotomicLayer_spectral_residueDegree_eq_one] at hidx
  exact Subgroup.index_eq_one.mp hidx

/-- The spectral residue degree of each positive rational diagonal
layer is one at every odd prime. -/
theorem falseTateLayer_spectral_residueDegree
    [hp₂ : Fact (p ≠ 2)] [hπ : Fact (Irreducible π)] (n : ℕ) :
    Module.finrank
      (𝓀[ℚ_[p]])
      (IsLocalRing.ResidueField (spectralIntegerRing (ℚ_[p])
        (falseTateLayer p (π : ℚ_[p]) (n + 1) (n + 1)))) = 1 := by
  let D := falseTateLayer p (π : ℚ_[p]) (n + 1) (n + 1)
  have := falseTateLayer_isGalois p (π : ℚ_[p]) (n + 1)
  have h := fixingSubgroup_sup_lowerRamificationGroup_zero_index_eq_residueDegree (ℚ_[p]) D
    (⊤ : IntermediateField (ℚ_[p]) D)
  rw [lowerRamificationGroup_falseTateLayer_zero p π n, sup_top_eq, Subgroup.index_top,
    spectral_residueDegree_algEquiv (ℚ_[p]) D (IntermediateField.topEquiv :
      (⊤ : IntermediateField (ℚ_[p]) D) ≃ₐ[ℚ_[p]] D).symm] at h
  exact h.symm

/-- The spectral ramification index equals the full field degree
for every positive rational diagonal layer at an odd prime. -/
theorem falseTateLayer_spectral_ramificationIdx
    [hp₂ : Fact (p ≠ 2)] [hπ : Fact (Irreducible π)] (n : ℕ) :
    (IsLocalRing.maximalIdeal (spectralIntegerRing (ℚ_[p])
      (falseTateLayer p (π : ℚ_[p]) (n + 1) (n + 1)))).ramificationIdx
        𝒪[ℚ_[p]] =
      Module.finrank (ℚ_[p]) (falseTateLayer p (π : ℚ_[p]) (n + 1) (n + 1)) := by
  have h := extensionValuationSubring_ramificationIdx_mul_residueDegree (ℚ_[p])
    (falseTateLayer p (π : ℚ_[p]) (n + 1) (n + 1))
    (spectralValuation (ℚ_[p]) (falseTateLayer p (π : ℚ_[p]) (n + 1) (n + 1)))
  rwa [falseTateLayer_spectral_residueDegree p π n, mul_one] at h

end RationalTotalRamification

section RationalInfiniteTotalRamification

variable (p : ℕ) [Fact p.Prime]
variable (π : 𝒪[ℚ_[p]])

/-- The residue inclusion from a positive diagonal layer to the
infinite false Tate field. -/
def falseTateResidueFromLayer (n : ℕ) :
    IsLocalRing.ResidueField (spectralIntegerRing (ℚ_[p])
      (falseTateLayer p (π : ℚ_[p]) (n + 1) (n + 1))) →ₐ[
        𝓀[ℚ_[p]]]
      IsLocalRing.ResidueField (spectralIntegerRing (ℚ_[p])
        (falseTateExtension p (π : ℚ_[p]))) :=
  spectralResidueInclusion (ℚ_[p]) (IntermediateField.inclusion
    (falseTateLayer_le_falseTateExtension p (π : ℚ_[p]) (n + 1) (n + 1)))

/-- Every infinite residue class comes from a positive
diagonal layer, using the field and residue inclusions. -/
theorem exists_falseTateResidueFromLayer_preimage
    (z : IsLocalRing.ResidueField (spectralIntegerRing (ℚ_[p])
      (falseTateExtension p (π : ℚ_[p])))) :
    ∃ n, ∃ x, falseTateResidueFromLayer p π n x = z := by
  obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective z
  obtain ⟨m, hm⟩ :=
    (mem_falseTateExtension_iff_diagonal p (π : ℚ_[p])
      (((x : spectralIntegerRing (ℚ_[p]) (falseTateExtension p (π : ℚ_[p]))) :
        falseTateExtension p (π : ℚ_[p])) : AlgebraicClosure (ℚ_[p]))).mp
      (x : falseTateExtension p (π : ℚ_[p])).property
  let i := IntermediateField.inclusion
    (falseTateLayer_le_falseTateExtension p (π : ℚ_[p]) (m + 1) (m + 1))
  let y : falseTateLayer p (π : ℚ_[p]) (m + 1) (m + 1) :=
    ⟨x, falseTateLayer_mono p (π : ℚ_[p]) (Nat.le_succ m) (Nat.le_succ m) hm⟩
  have hyi : i y = (x : falseTateExtension p (π : ℚ_[p])) := Subtype.ext rfl
  let : Algebra (falseTateLayer p (π : ℚ_[p]) (m + 1) (m + 1))
      (falseTateExtension p (π : ℚ_[p])) := i.toRingHom.toAlgebra
  let : IsScalarTower (ℚ_[p]) (falseTateLayer p (π : ℚ_[p]) (m + 1) (m + 1))
      (falseTateExtension p (π : ℚ_[p])) :=
    IsScalarTower.of_algebraMap_eq (fun r => (i.commutes r).symm)
  have hy : y ∈ spectralIntegerRing (ℚ_[p]) (falseTateLayer p (π : ℚ_[p]) (m + 1) (m + 1)) := by
    rw [mem_spectralIntegerRing,
      spectralNorm.eq_of_tower (L := falseTateExtension p (π : ℚ_[p])) y]
    change spectralNorm (ℚ_[p]) (falseTateExtension p (π : ℚ_[p])) (i y) ≤ 1
    rw [hyi]
    exact (mem_spectralIntegerRing (ℚ_[p]) _ _).mp x.property
  refine ⟨m, IsLocalRing.residue _ ⟨y, hy⟩, ?_⟩
  change spectralResidueInclusion (ℚ_[p]) i (IsLocalRing.residue _ ⟨y, hy⟩) = _
  rw [spectralResidueInclusion_residue]
  congr 1

/-- The base-residue map onto the infinite false Tate
residue field is surjective at every odd prime. -/
theorem falseTateExtension_residue_algebraMap_surjective
    [hp₂ : Fact (p ≠ 2)] [hπ : Fact (Irreducible π)] :
    Function.Surjective (algebraMap
      (𝓀[ℚ_[p]])
      (IsLocalRing.ResidueField (spectralIntegerRing (ℚ_[p])
        (falseTateExtension p (π : ℚ_[p]))))) := by
  intro z
  obtain ⟨n, x, hx⟩ := exists_falseTateResidueFromLayer_preimage p π z
  have hsurj := (Algebra.finrank_eq_one_iff_bijective_algebraMap.mp
    (falseTateLayer_spectral_residueDegree p π n)).surjective
  obtain ⟨a, ha⟩ := hsurj x
  refine ⟨a, ?_⟩
  rw [← (falseTateResidueFromLayer p π n).commutes a, ha, hx]

/-- The infinite false Tate field has exactly the rational
residue field at an odd prime. -/
theorem falseTateExtension_residueDegree_padic [hp₂ : Fact (p ≠ 2)] [hπ : Fact (Irreducible π)] :
    Module.finrank
      (𝓀[ℚ_[p]])
      (IsLocalRing.ResidueField (spectralIntegerRing (ℚ_[p])
        (falseTateExtension p (π : ℚ_[p])))) = 1 := by
  apply Algebra.finrank_eq_one_iff_bijective_algebraMap.mpr
  exact ⟨(algebraMap
    (𝓀[ℚ_[p]])
    (IsLocalRing.ResidueField (spectralIntegerRing (ℚ_[p])
      (falseTateExtension p (π : ℚ_[p]))))).injective,
    falseTateExtension_residue_algebraMap_surjective p π⟩

/-- Every finite separable subextension of the odd rational false
Tate field has residue degree one under its specified embedding. -/
theorem finiteSubextension_falseTate_residueDegree_padic
    [hp₂ : Fact (p ≠ 2)] [hπ : Fact (Irreducible π)]
    (E : Type*) [Field E] [Algebra (ℚ_[p]) E] [FiniteDimensional (ℚ_[p]) E]
    (i : E →ₐ[ℚ_[p]] falseTateExtension p (π : ℚ_[p])) :
    Module.finrank
      (𝓀[ℚ_[p]])
      (IsLocalRing.ResidueField (spectralIntegerRing (ℚ_[p]) E)) = 1 := by
  apply Algebra.finrank_eq_one_iff_bijective_algebraMap.mpr
  refine ⟨(algebraMap
    (𝓀[ℚ_[p]])
    (IsLocalRing.ResidueField (spectralIntegerRing (ℚ_[p]) E))).injective, ?_⟩
  intro z
  obtain ⟨a, ha⟩ := falseTateExtension_residue_algebraMap_surjective p π
    (spectralResidueInclusion (ℚ_[p]) i z)
  refine ⟨a, (spectralResidueInclusion (ℚ_[p]) i).injective ?_⟩
  exact ((spectralResidueInclusion (ℚ_[p]) i).commutes a).trans ha

/-- Every finite subextension is totally ramified, with its own
spectral integer ring and its specified inclusion into the odd tower. -/
theorem finiteSubextension_falseTate_ramificationIdx_padic
    [hp₂ : Fact (p ≠ 2)] [hπ : Fact (Irreducible π)]
    (E : Type*) [Field E] [Algebra (ℚ_[p]) E] [FiniteDimensional (ℚ_[p]) E]
    (i : E →ₐ[ℚ_[p]] falseTateExtension p (π : ℚ_[p])) :
    (IsLocalRing.maximalIdeal (spectralIntegerRing (ℚ_[p]) E)).ramificationIdx
      𝒪[ℚ_[p]] = Module.finrank (ℚ_[p]) E := by
  have h := extensionValuationSubring_ramificationIdx_mul_residueDegree (ℚ_[p]) E
    (spectralValuation (ℚ_[p]) E)
  rwa [finiteSubextension_falseTate_residueDegree_padic p π E i, mul_one] at h

end RationalInfiniteTotalRamification

end FalseTateExtension
end
