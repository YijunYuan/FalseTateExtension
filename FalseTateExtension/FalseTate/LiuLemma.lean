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
# Liu's Lemma 5.1.2: the relative Galois groups

`Gal(K_FT/K_cyc) ≅ ℤ_[p]` with generator `τ`, and `Gal(K_FT/K_Kum) ≅ Gal(K_cyc/K)`, as topological
groups, for `p ≠ 2`.

## References

* Liu, *On lattices in semi-stable representations: a proof of a conjecture of Breuil*, Lemma 5.1.2.
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

/-- The inclusion defines the relative cyclotomic scalar action. -/
local instance cyclotomicRelativeAlgebra :
    Algebra (cyclotomicExtension (K := K) p) (falseTateExtension p (π : K)) :=
  IntermediateField.algebraOfLE (cyclotomicExtension_le_falseTateExtension p (π : K))

local instance cyclotomicRelativeScalarTower :
    IsScalarTower K (cyclotomicExtension (K := K) p) (falseTateExtension p (π : K)) :=
  IntermediateField.isScalarTower_of_le (cyclotomicExtension_le_falseTateExtension p (π : K))

omit [Algebra (ℚ_[p]) K] in
/-- The relative scalar homomorphism is exactly the cyclotomic inclusion. -/
theorem cyclotomicRelative_scalarHom_eq :
    IsScalarTower.toAlgHom K (cyclotomicExtension (K := K) p) (falseTateExtension p (π : K)) =
      IntermediateField.inclusion (cyclotomicExtension_le_falseTateExtension p (π : K)) := by
  apply AlgHom.ext
  intro x
  rfl

/-- The character kernel is the relative cyclotomic Galois
group, with its own Krull topology and inclusion of scalars. -/
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

/-- The relative cyclotomic Galois group is the full p-adic
translation factor, normalized by the roots. -/
def cyclotomicRelativeGaloisEquiv [hp₂ : Fact (p ≠ 2)] [hπ : Fact (Irreducible π)] :
    (falseTateExtension p (π : K) ≃ₐ[cyclotomicExtension (K := K) p]
      falseTateExtension p (π : K)) ≃ₜ* Multiplicative (ℤ_[p]) :=
  (cyclotomicKernelRelativeEquiv p π).symm.trans (fullKummerKernelMulEquiv p π)

/-- The generator as an automorphism over the
cyclotomic field, rather than only as an element of its fixing subgroup. -/
def relativeTau [hp₂ : Fact (p ≠ 2)] [hπ : Fact (Irreducible π)] :
    falseTateExtension p (π : K) ≃ₐ[cyclotomicExtension (K := K) p]
      falseTateExtension p (π : K) :=
  cyclotomicKernelRelativeEquiv p π (tau p π)

/-- The relative generator has precisely the radical actions. -/
theorem relativeTau_extensionRadical [hp₂ : Fact (p ≠ 2)] [hπ : Fact (Irreducible π)] (n : ℕ) :
    relativeTau p π (extensionRadical p (π : K) (n + 1)) =
      extensionRootOfUnity p (π : K) (n + 1) * extensionRadical p (π : K) (n + 1) :=
  tau_extensionRadical p π n

/-- Integral powers are dense in the relative cyclotomic Galois group. -/
theorem denseRange_relativeTau_zpow [hp₂ : Fact (p ≠ 2)] [hπ : Fact (Irreducible π)] :
    DenseRange (fun n : ℤ => relativeTau p π ^ n) := by
  have hd := (cyclotomicKernelRelativeEquiv p π).surjective.denseRange.comp
    (denseRange_tau_zpow p π) (cyclotomicKernelRelativeEquiv p π).continuous
  simpa only [Function.comp_def, map_zpow, relativeTau] using hd

/-- The relative generator corresponds to exactly one under the
isomorphism normalized by the compatible roots. -/
theorem cyclotomicRelativeGaloisEquiv_relativeTau [hp₂ : Fact (p ≠ 2)] [hπ : Fact (Irreducible π)] :
    cyclotomicRelativeGaloisEquiv p π (relativeTau p π) =
      Multiplicative.ofAdd (1 : ℤ_[p]) := by
  change fullKummerKernelMulEquiv p π
    ((cyclotomicKernelRelativeEquiv p π).symm
      (cyclotomicKernelRelativeEquiv p π (tau p π))) = _
  rw [(cyclotomicKernelRelativeEquiv p π).symm_apply_apply]
  exact congrArg Multiplicative.ofAdd (padicKummerExponent_tau p π)

/-- The actions uniquely determine the generator in the
relative cyclotomic Galois group. -/
theorem relativeTau_unique [hp₂ : Fact (p ≠ 2)] [hπ : Fact (Irreducible π)]
    (g : falseTateExtension p (π : K) ≃ₐ[cyclotomicExtension (K := K) p]
      falseTateExtension p (π : K))
    (hg : ∀ n : ℕ, g (extensionRadical p (π : K) (n + 1)) =
      extensionRootOfUnity p (π : K) (n + 1) * extensionRadical p (π : K) (n + 1)) :
    g = relativeTau p π := by
  apply (cyclotomicKernelRelativeEquiv p π).symm.injective
  change (cyclotomicKernelRelativeEquiv p π).symm g =
    (cyclotomicKernelRelativeEquiv p π).symm
      (cyclotomicKernelRelativeEquiv p π (tau p π))
  rw [(cyclotomicKernelRelativeEquiv p π).symm_apply_apply]
  apply tau_unique p π
  exact hg

end RelativeCyclotomic

section RelativeKummer

variable {K : Type*} [NontriviallyNormedField K] [IsCompleteDiscreteValuedField K] [CharZero K]
variable (p : ℕ) [Fact p.Prime] [Algebra (ℚ_[p]) K]
variable (π : 𝒪[K])

/-- The inclusion defines the relative radical scalar action. -/
local instance kummerRelativeAlgebra :
    Algebra (kummerExtension p (π : K)) (falseTateExtension p (π : K)) :=
  IntermediateField.algebraOfLE (kummerExtension_le_falseTateExtension p (π : K))

local instance kummerRelativeScalarTower :
    IsScalarTower K (kummerExtension p (π : K)) (falseTateExtension p (π : K)) :=
  IntermediateField.isScalarTower_of_le (kummerExtension_le_falseTateExtension p (π : K))

omit [Algebra (ℚ_[p]) K] in
/-- The relative scalar homomorphism is exactly the radical inclusion. -/
theorem kummerRelative_scalarHom_eq :
    IsScalarTower.toAlgHom K (kummerExtension p (π : K)) (falseTateExtension p (π : K)) =
      falseTateKummerInclusion p (π : K) := by
  apply AlgHom.ext
  intro x
  rfl

/-- The Galois group over the radical field is the
cyclotomic character image, with both of their topologies. -/
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
