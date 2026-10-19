/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FalseTateExtension.Coordinates.AffineEmbedding
public import Mathlib.Topology.Algebra.Group.ClosedSubgroup

/-!
# The closed additive kernel of the affine embedding

The additive coordinates in the affine image with unit coordinate one form
a closed additive subgroup of the p-adic integers. The
Kummer coordinate identifies the cyclotomic-character kernel with this
subgroup as a topological additive group.
This proves blueprint `ft:affine-additive-kernel`, the kernel part of the
affine realization in Liu, Section 5.1.
-/

@[expose] public section

namespace FalseTateExtension

noncomputable section

variable {K : Type*} [Field K] [CharZero K] (p : ℕ) [Fact p.Prime] (π : K)

/-- The affine inclusion of the additive p-adic coordinate is continuous. -/
theorem continuous_padicAffine_inl : Continuous (fun a : ℤ_[p] ↦
    (SemidirectProduct.inl (Multiplicative.ofAdd a) : PadicAffineGroup p)) :=
  AffineGroup.continuous_inl _

/-- The closed additive subgroup of coordinates whose affine translation
belongs to the Galois image. -/
def affineAdditiveKernel [hπ : NeZero π] : ClosedAddSubgroup (ℤ_[p]) where
  toAddSubgroup := Subgroup.toAddSubgroup'
    ((affineGaloisHom p π).range.comap SemidirectProduct.inl)
  isClosed' := by
    change IsClosed ((fun a : ℤ_[p] ↦
      (SemidirectProduct.inl (Multiplicative.ofAdd a) : PadicAffineGroup p)) ⁻¹'
        Set.range (affineGaloisHom p π))
    exact (isClosedEmbedding_affineGaloisHom p π).isClosed_range.preimage
      (continuous_padicAffine_inl p)

/-- Membership is the defining condition in the affine Galois image. -/
theorem mem_affineAdditiveKernel_iff [hπ : NeZero π] (a : ℤ_[p]) :
    a ∈ affineAdditiveKernel p π ↔
      (SemidirectProduct.inl (Multiplicative.ofAdd a) : PadicAffineGroup p) ∈
        (affineGaloisHom p π).range := Iff.rfl

/-- The Kummer coordinate of a character-kernel element belongs to the
closed additive affine kernel. -/
theorem padicKummerExponent_mem_affineAdditiveKernel [hπ : NeZero π]
    (g : (padicCyclotomicCharacter p π).ker) :
    padicKummerExponent p π g ∈ affineAdditiveKernel p π := by
  rw [mem_affineAdditiveKernel_iff]
  refine ⟨g, ?_⟩
  apply SemidirectProduct.ext
  · rfl
  · exact g.property

/-- On the cyclotomic-character kernel the Kummer cocycle is additive. -/
def kummerKernelHom [hπ : NeZero π] :
    Additive (padicCyclotomicCharacter p π).ker →+ affineAdditiveKernel p π where
  toFun g := ⟨padicKummerExponent p π g.toMul,
    padicKummerExponent_mem_affineAdditiveKernel p π g.toMul⟩
  map_zero' := by
    apply Subtype.ext
    have h := congrArg (fun x : PadicAffineGroup p ↦ x.left.toAdd)
      (map_one (affineGaloisHom p π))
    exact h
  map_add' g h := by
    apply Subtype.ext
    change padicKummerExponent p π (g.toMul.val * h.toMul.val) = _
    rw [padicKummerExponent_mul,
      show padicCyclotomicCharacter p π g.toMul.val = 1 from g.toMul.property]
    simp

/-- The additive kernel homomorphism is the Kummer coordinate. -/
theorem kummerKernelHom_apply [hπ : NeZero π]
    (g : Additive (padicCyclotomicCharacter p π).ker) :
    (kummerKernelHom p π g : ℤ_[p]) = padicKummerExponent p π g.toMul := rfl

/-- The affine image and coordinate injectivity make the kernel
coordinate map bijective onto precisely the closed subgroup. -/
theorem kummerKernelHom_bijective [hπ : NeZero π] :
    Function.Bijective (kummerKernelHom p π) := by
  constructor
  · intro g h heq
    apply Additive.toMul.injective
    apply Subtype.ext
    apply padicCoordinates_injective p π
    exact Prod.ext (congrArg Subtype.val heq) (g.toMul.property.trans h.toMul.property.symm)
  · intro a
    obtain ⟨g, hg⟩ := (mem_affineAdditiveKernel_iff p π a).mp a.property
    have hχ : g ∈ (padicCyclotomicCharacter p π).ker :=
      congrArg SemidirectProduct.right hg
    have hb : padicKummerExponent p π g = a :=
      congrArg (fun x : PadicAffineGroup p ↦ x.left.toAdd) hg
    exact ⟨Additive.ofMul ⟨g, hχ⟩, Subtype.ext hb⟩

/-- Restricting the continuous Kummer coordinate gives a continuous
map on the character kernel and into the additive kernel. -/
theorem continuous_kummerKernelHom [hπ : NeZero π] :
    Continuous (kummerKernelHom p π) := by
  apply Continuous.subtype_mk
  exact (continuous_padicKummerExponent p π).comp
    (continuous_subtype_val.comp continuous_toMul)

/-- The Kummer coordinate identifies the character kernel with its
closed additive affine kernel as a topological additive group. -/
def kummerKernelEquiv [hπ : NeZero π] :
    Additive (padicCyclotomicCharacter p π).ker ≃ₜ+ affineAdditiveKernel p π := by
  have := falseTateExtension_isGalois p π
  have hker : IsClosed ((padicCyclotomicCharacter p π).ker :
      Set (falseTateExtension p π ≃ₐ[K] falseTateExtension p π)) :=
    isClosed_singleton.preimage (continuous_padicCyclotomicCharacter p π)
  have : CompactSpace (padicCyclotomicCharacter p π).ker :=
    isCompact_iff_compactSpace.mp hker.isCompact
  let e := AddEquiv.ofBijective (kummerKernelHom p π) (kummerKernelHom_bijective p π)
  have hc : Continuous e := continuous_kummerKernelHom p π
  exact
    { e with
      continuous_toFun := hc
      continuous_invFun := hc.continuous_symm_of_equiv_compact_to_t2 }

/-- The topological additive identification evaluates to the
Kummer coordinate. -/
theorem kummerKernelEquiv_apply [hπ : NeZero π]
    (g : Additive (padicCyclotomicCharacter p π).ker) :
    (kummerKernelEquiv p π g : ℤ_[p]) = padicKummerExponent p π g.toMul := rfl

end

end FalseTateExtension
