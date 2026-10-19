/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FalseTateExtension.Coordinates.AffineKernel
public import FalseTateExtension.Cyclotomic.CyclicLayers
public import FalseTateExtension.FalseTate.RadicalNotCyclotomic
public import FalseTateExtension.FalseTate.TranslationKernel
public import FalseTateExtension.Mathlib.FieldTheory.Galois.InfiniteCorrespondence
public import FalseTateExtension.Mathlib.RingTheory.PowerBasis.Eigenvector
public import FalseTateExtension.FalseTate.StrictAPF
public import Mathlib.FieldTheory.Galois.Abelian
public import Mathlib.FieldTheory.LinearDisjoint
public import Mathlib.RingTheory.ZMod.UnitsCyclic

/-!
# Liu's Lemma 5.1.2: the relative Galois groups of `K_FT`

Let `K/ℚ_p` be finite with uniformizer `π`, `p ≠ 2`, `K_FT = K(π^{1/p^∞}, ζ_{p^∞})`,
`K_Kum = K(π^{1/p^∞})` and `K_cyc = K(ζ_{p^∞})`. The Galois group `Gal(K_FT/K_cyc)` is the
kernel of the cyclotomic character `χ` on `Gal(K_FT/K)`, and the Kummer exponent `b` is an
isomorphism of topological groups `Gal(K_FT/K_cyc) ≃ₜ* ℤ_[p]`; the element `τ` with `b(τ) = 1`
satisfies `τ(π^{1/p^n}) = ζ_{p^n} π^{1/p^n}` for all `n`, is determined by these equations, and
its integer powers are dense. The Galois group `Gal(K_FT/K_Kum)` is isomorphic, through `χ`, to
`χ(Gal(K_cyc/K)) ≅ Gal(K_cyc/K)` as a topological group.

## Main results

* `cyclotomicKernelRelativeEquiv`: `ker χ ≃ₜ* Gal(K_FT/K_cyc)`.
* `cyclotomicRelativeGaloisEquiv`: `Gal(K_FT/K_cyc) ≃ₜ* ℤ_[p]`.
* `kummerGeneratorRel`, `relativeTau_extensionRadical`, `relativeTau_unique`,
  `denseRange_relativeTau_zpow`: `τ ∈ Gal(K_FT/K_cyc)`.
* `cyclotomicRelativeGaloisEquiv_relativeTau`: `τ ↦ 1` under `Gal(K_FT/K_cyc) ≃ₜ* ℤ_[p]`.
* `kummerRelativeGaloisEquiv`: `Gal(K_FT/K_Kum) ≃ₜ* χ(Gal(K_cyc/K))`.

## References

* Liu, *On lattices in semi-stable representations: a proof of a conjecture of Breuil*,
  Lemma 5.1.2.
-/

@[expose] public section

noncomputable section

namespace FalseTateExtension

open Polynomial
open FontaineWintenberger

section RelativeCyclotomic

variable {K : Type*} [NontriviallyNormedField K] [IsCompleteDiscreteValuedField K] [CharZero K]
variable (p : ℕ) [Fact p.Prime] [Algebra (ℚ_[p]) K]
variable (π : 𝒪[K])

/-- The `K_cyc`-algebra structure on `K_FT` given by the inclusion `K_cyc ⊆ K_FT`. -/
local instance cyclotomicRelativeAlgebra :
    Algebra (cyclotomicExtension (K := K) p) (falseTateExtension p (π : K)) :=
  IntermediateField.algebraOfLE (cyclotomicExtension_le_falseTateExtension p (π : K))

/-- `K ⊆ K_cyc ⊆ K_FT` is a tower of algebras. -/
local instance cyclotomicRelativeScalarTower :
    IsScalarTower K (cyclotomicExtension (K := K) p) (falseTateExtension p (π : K)) :=
  IntermediateField.isScalarTower_of_le (cyclotomicExtension_le_falseTateExtension p (π : K))

omit [Algebra (ℚ_[p]) K] in
/-- The algebra map `K_cyc → K_FT` is the inclusion of intermediate fields. -/
theorem cyclotomicRelative_scalarHom_eq :
    IsScalarTower.toAlgHom K (cyclotomicExtension (K := K) p) (falseTateExtension p (π : K)) =
      IntermediateField.inclusion (cyclotomicExtension_le_falseTateExtension p (π : K)) := by
  apply AlgHom.ext
  intro x
  rfl

/-- The isomorphism of topological groups `ker χ ≃ₜ* Gal(K_FT/K_cyc)`, `Gal(K_FT/K_cyc)` with
its Krull topology. -/
def cyclotomicKernelRelativeEquiv [hπ : Fact (Irreducible π)] :
    (padicCyclotomicCharacter p (π : K)).ker ≃ₜ*
      (falseTateExtension p (π : K) ≃ₐ[cyclotomicExtension (K := K) p]
        falseTateExtension p (π : K)) := by
  have := falseTateExtension_isGalois p (π : K)
  let i := IntermediateField.inclusion (cyclotomicExtension_le_falseTateExtension p (π : K))
  let e : (padicCyclotomicCharacter p (π : K)).ker ≃ₜ* i.fieldRange.fixingSubgroup :=
    { MulEquiv.subgroupCongr (cyclotomicInclusion_fixingSubgroup p (π : K)).symm with
      continuous_toFun := continuous_subtype_val.subtype_mk _
      continuous_invFun := continuous_subtype_val.subtype_mk _ }
  exact e.trans (AlgEquiv.fixingSubgroupContinuousMulEquiv K (cyclotomicExtension (K := K) p)
    (falseTateExtension p (π : K)) i (AlgHom.congr_fun (cyclotomicRelative_scalarHom_eq p π)))

/-- For `p ≠ 2`, the Kummer exponent `b` is an isomorphism of topological groups
`Gal(K_FT/K_cyc) ≃ₜ* Multiplicative ℤ_[p]`. -/
def cyclotomicRelativeGaloisEquiv [hp₂ : Fact (p ≠ 2)] [hπ : Fact (Irreducible π)] :
    (falseTateExtension p (π : K) ≃ₐ[cyclotomicExtension (K := K) p]
      falseTateExtension p (π : K)) ≃ₜ* Multiplicative (ℤ_[p]) :=
  (cyclotomicKernelRelativeEquiv p π).symm.trans (kummerKernelMulEquivPadicInt p π)

/-- The generator `τ` as an element of `Gal(K_FT/K_cyc)`. -/
def kummerGeneratorRel [hp₂ : Fact (p ≠ 2)] [hπ : Fact (Irreducible π)] :
    falseTateExtension p (π : K) ≃ₐ[cyclotomicExtension (K := K) p]
      falseTateExtension p (π : K) :=
  cyclotomicKernelRelativeEquiv p π (kummerGenerator p π)

/-- `τ(π^{1/p^{n+1}}) = ζ_{p^{n+1}} π^{1/p^{n+1}}` for `τ ∈ Gal(K_FT/K_cyc)`. -/
theorem relativeTau_extensionRadical [hp₂ : Fact (p ≠ 2)] [hπ : Fact (Irreducible π)] (n : ℕ) :
    kummerGeneratorRel p π (pPowRootExt p (π : K) (n + 1)) =
      zetaExt p (π : K) (n + 1) * pPowRootExt p (π : K) (n + 1) :=
  tau_extensionRadical p π n

/-- The powers `τ^n`, `n ∈ ℤ`, are dense in `Gal(K_FT/K_cyc)`. -/
theorem denseRange_relativeTau_zpow [hp₂ : Fact (p ≠ 2)] [hπ : Fact (Irreducible π)] :
    DenseRange (fun n : ℤ => kummerGeneratorRel p π ^ n) := by
  have hd := (cyclotomicKernelRelativeEquiv p π).surjective.denseRange.comp
    (denseRange_tau_zpow p π) (cyclotomicKernelRelativeEquiv p π).continuous
  simpa only [Function.comp_def, map_zpow, kummerGeneratorRel] using hd

/-- `τ ↦ 1` under `Gal(K_FT/K_cyc) ≃ₜ* Multiplicative ℤ_[p]`. -/
theorem cyclotomicRelativeGaloisEquiv_relativeTau [hp₂ : Fact (p ≠ 2)] [hπ : Fact (Irreducible π)] :
    cyclotomicRelativeGaloisEquiv p π (kummerGeneratorRel p π) =
      Multiplicative.ofAdd (1 : ℤ_[p]) := by
  change kummerKernelMulEquivPadicInt p π
    ((cyclotomicKernelRelativeEquiv p π).symm
      (cyclotomicKernelRelativeEquiv p π (kummerGenerator p π))) = _
  rw [(cyclotomicKernelRelativeEquiv p π).symm_apply_apply]
  exact congrArg Multiplicative.ofAdd (padicKummerExponent_tau p π)

/-- An element `g ∈ Gal(K_FT/K_cyc)` with `g(π^{1/p^{n+1}}) = ζ_{p^{n+1}} π^{1/p^{n+1}}` for all
`n` is `τ`. -/
theorem relativeTau_unique [hp₂ : Fact (p ≠ 2)] [hπ : Fact (Irreducible π)]
    (g : falseTateExtension p (π : K) ≃ₐ[cyclotomicExtension (K := K) p]
      falseTateExtension p (π : K))
    (hg : ∀ n : ℕ, g (pPowRootExt p (π : K) (n + 1)) =
      zetaExt p (π : K) (n + 1) * pPowRootExt p (π : K) (n + 1)) :
    g = kummerGeneratorRel p π := by
  apply (cyclotomicKernelRelativeEquiv p π).symm.injective
  change (cyclotomicKernelRelativeEquiv p π).symm g =
    (cyclotomicKernelRelativeEquiv p π).symm
      (cyclotomicKernelRelativeEquiv p π (kummerGenerator p π))
  rw [(cyclotomicKernelRelativeEquiv p π).symm_apply_apply]
  apply tau_unique p π
  exact hg

end RelativeCyclotomic

section RelativeKummer

variable {K : Type*} [NontriviallyNormedField K] [IsCompleteDiscreteValuedField K] [CharZero K]
variable (p : ℕ) [Fact p.Prime] [Algebra (ℚ_[p]) K]
variable (π : 𝒪[K])

/-- The `K_Kum`-algebra structure on `K_FT` given by the inclusion `K_Kum ⊆ K_FT`. -/
local instance kummerRelativeAlgebra :
    Algebra (kummerExtension p (π : K)) (falseTateExtension p (π : K)) :=
  IntermediateField.algebraOfLE (kummerExtension_le_falseTateExtension p (π : K))

/-- `K ⊆ K_Kum ⊆ K_FT` is a tower of algebras. -/
local instance kummerRelativeScalarTower :
    IsScalarTower K (kummerExtension p (π : K)) (falseTateExtension p (π : K)) :=
  IntermediateField.isScalarTower_of_le (kummerExtension_le_falseTateExtension p (π : K))

omit [Algebra (ℚ_[p]) K] in
/-- The algebra map `K_Kum → K_FT` is the inclusion of intermediate fields. -/
theorem kummerRelative_scalarHom_eq :
    IsScalarTower.toAlgHom K (kummerExtension p (π : K)) (falseTateExtension p (π : K)) =
      falseTateKummerInclusion p (π : K) := by
  apply AlgHom.ext
  intro x
  rfl

/-- For `p ≠ 2`, `χ` induces an isomorphism of topological groups
`Gal(K_FT/K_Kum) ≃ₜ* χ(Gal(K_cyc/K))`. -/
def kummerRelativeGaloisEquiv [hp₂ : Fact (p ≠ 2)] [hπ : Fact (Irreducible π)] :
    (falseTateExtension p (π : K) ≃ₐ[kummerExtension p (π : K)]
      falseTateExtension p (π : K)) ≃ₜ* (cyclotomicExtensionCharacter (K := K) p).range := by
  have := falseTateExtension_isGalois p (π : K)
  exact (AlgEquiv.fixingSubgroupContinuousMulEquiv K (kummerExtension p (π : K))
    (falseTateExtension p (π : K)) (falseTateKummerInclusion p (π : K))
    (AlgHom.congr_fun (kummerRelative_scalarHom_eq p π))).symm.trans
      (kummerFixingEquivCyclotomicImage p π)

end RelativeKummer

end FalseTateExtension
end
