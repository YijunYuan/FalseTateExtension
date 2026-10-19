/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FalseTateExtension.Coordinates.AffineEmbedding
public import Mathlib.Topology.Algebra.Group.ClosedSubgroup

/-!
# The kernel of the cyclotomic character as a closed subgroup of `ℤ_[p]`

Let `K` be a field of characteristic zero, `π ∈ K` nonzero and `K_FT = K(π^{1/p^∞}, ζ_{p^∞})`,
with Kummer exponent `b` and cyclotomic character `χ` on `Gal(K_FT/K)`. The set
`affineAdditiveKernel p π = {a ∈ ℤ_[p] | (a, 1) = (b(g), χ(g)) for some g}` is a closed additive
subgroup of `ℤ_[p]`, and `b` restricts to an isomorphism of topological groups
`ker χ ≃ₜ+ affineAdditiveKernel p π`; `ker χ = Gal(K_FT/K_cyc)` is thus a closed subgroup of
`ℤ_[p]`. For `p ≠ 2` and `π` a uniformizer of a finite extension of `ℚ_[p]` this subgroup is all
of `ℤ_[p]` (`FalseTate/TranslationKernel`).

## Main results

* `affineAdditiveKernel`: the closed additive subgroup `{a | (a, 1) ∈ im (b, χ)}` of `ℤ_[p]`.
* `kummerKernelHom`: `b` restricted to `ker χ` is an additive homomorphism into it.
* `kummerKernelHom_bijective`: this restriction is bijective.
* `kummerKernelEquiv`: the isomorphism of topological groups `ker χ ≃ₜ+ affineAdditiveKernel`.

## References

* Liu, *On lattices in semi-stable representations: a proof of a conjecture of Breuil*, §5.1.
-/

@[expose] public section

namespace FalseTateExtension

noncomputable section

variable {K : Type*} [Field K] [CharZero K] (p : ℕ) [Fact p.Prime] (π : K)

/-- The inclusion `ℤ_[p] → ℤ_[p] ⋊ ℤ_[p]ˣ`, `a ↦ (a, 1)`, is continuous. -/
theorem continuous_padicAffine_inl : Continuous (fun a : ℤ_[p] ↦
    (SemidirectProduct.inl (Multiplicative.ofAdd a) : PadicAffineGroup p)) :=
  AffineGroup.continuous_inl _

/-- The closed additive subgroup `{a ∈ ℤ_[p] | (a, 1) ∈ im (b, χ)}` of `ℤ_[p]`: the translation
kernel of the image of `Gal(K_FT/K)` in `ℤ_[p] ⋊ ℤ_[p]ˣ`. -/
def affineAdditiveKernel [hπ : NeZero π] : ClosedAddSubgroup (ℤ_[p]) where
  toAddSubgroup := Subgroup.toAddSubgroup'
    ((affineGaloisHom p π).range.comap SemidirectProduct.inl)
  isClosed' := by
    change IsClosed ((fun a : ℤ_[p] ↦
      (SemidirectProduct.inl (Multiplicative.ofAdd a) : PadicAffineGroup p)) ⁻¹'
        Set.range (affineGaloisHom p π))
    exact (isClosedEmbedding_affineGaloisHom p π).isClosed_range.preimage
      (continuous_padicAffine_inl p)

/-- `a ∈ affineAdditiveKernel p π` if and only if `(a, 1)` is in the image of `Gal(K_FT/K)`. -/
theorem mem_affineAdditiveKernel_iff [hπ : NeZero π] (a : ℤ_[p]) :
    a ∈ affineAdditiveKernel p π ↔
      (SemidirectProduct.inl (Multiplicative.ofAdd a) : PadicAffineGroup p) ∈
        (affineGaloisHom p π).range := Iff.rfl

/-- For `g ∈ ker χ`, `b(g) ∈ affineAdditiveKernel p π`. -/
theorem padicKummerExponent_mem_affineAdditiveKernel [hπ : NeZero π]
    (g : (padicCyclotomicCharacter p π).ker) :
    padicKummerExponent p π g ∈ affineAdditiveKernel p π := by
  rw [mem_affineAdditiveKernel_iff]
  refine ⟨g, ?_⟩
  apply SemidirectProduct.ext
  · rfl
  · exact g.property

/-- The restriction of the Kummer exponent `b` to `ker χ`, an additive homomorphism
`ker χ →+ affineAdditiveKernel p π`. -/
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

/-- `kummerKernelHom g = b(g)` for `g ∈ ker χ`. -/
theorem kummerKernelHom_apply [hπ : NeZero π]
    (g : Additive (padicCyclotomicCharacter p π).ker) :
    (kummerKernelHom p π g : ℤ_[p]) = padicKummerExponent p π g.toMul := rfl

/-- `b : ker χ → affineAdditiveKernel p π` is bijective. -/
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

/-- `b : ker χ → affineAdditiveKernel p π` is continuous. -/
theorem continuous_kummerKernelHom [hπ : NeZero π] :
    Continuous (kummerKernelHom p π) := by
  apply Continuous.subtype_mk
  exact (continuous_padicKummerExponent p π).comp
    (continuous_subtype_val.comp continuous_toMul)

/-- The isomorphism of topological additive groups `ker χ ≃ₜ+ affineAdditiveKernel p π`
given by the Kummer exponent `b`. -/
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

/-- `kummerKernelEquiv g = b(g)` for `g ∈ ker χ`. -/
theorem kummerKernelEquiv_apply [hπ : NeZero π]
    (g : Additive (padicCyclotomicCharacter p π).ker) :
    (kummerKernelEquiv p π g : ℤ_[p]) = padicKummerExponent p π g.toMul := rfl

end

end FalseTateExtension
