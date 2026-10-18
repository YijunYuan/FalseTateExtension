module

public import FalseTateExtension.AffineEmbedding
public import Mathlib.Topology.Algebra.Group.ClosedSubgroup

/-!
# The closed additive kernel of the actual affine embedding

The additive coordinates in the affine image with unit coordinate one form
a canonical closed additive subgroup of the p-adic integers. The actual
Kummer coordinate identifies the cyclotomic-character kernel with this
subgroup as a topological additive group.
This proves blueprint `ft:affine-additive-kernel`, the kernel part of the
affine realization in Liu, Section 5.1.
-/

@[expose] public section

namespace FalseTateExtension

noncomputable section

variable {K : Type*} [Field K] [CharZero K] (p : ℕ) [Fact p.Prime] (π : K)

/-- The actual affine inclusion of the additive p-adic coordinate is continuous. -/
theorem continuous_padicAffine_inl : Continuous (fun a : PadicInt p ↦
    (SemidirectProduct.inl (Multiplicative.ofAdd a) : PadicAffineGroup p)) := by
  apply continuous_induced_rng.mpr
  exact continuous_id.prodMk continuous_const

/-- The closed additive subgroup of coordinates whose affine translation
belongs to the actual Galois image. -/
def affineAdditiveKernel (hπ : π ≠ 0) : ClosedAddSubgroup (PadicInt p) where
  toAddSubgroup := Subgroup.toAddSubgroup'
    ((affineGaloisHom p π hπ).range.comap SemidirectProduct.inl)
  isClosed' := by
    change IsClosed ((fun a : PadicInt p ↦
      (SemidirectProduct.inl (Multiplicative.ofAdd a) : PadicAffineGroup p)) ⁻¹'
        Set.range (affineGaloisHom p π hπ))
    exact (isClosedEmbedding_affineGaloisHom p π hπ).isClosed_range.preimage
      (continuous_padicAffine_inl p)

/-- Membership is the defining condition in the actual affine Galois image. -/
theorem mem_affineAdditiveKernel_iff (hπ : π ≠ 0) (a : PadicInt p) :
    a ∈ affineAdditiveKernel p π hπ ↔
      (SemidirectProduct.inl (Multiplicative.ofAdd a) : PadicAffineGroup p) ∈
        (affineGaloisHom p π hπ).range := Iff.rfl

/-- The actual Kummer coordinate of a character-kernel element belongs to the
closed additive affine kernel. -/
theorem padicKummerExponent_mem_affineAdditiveKernel (hπ : π ≠ 0)
    (g : (padicCyclotomicCharacter p π).ker) :
    padicKummerExponent p π hπ g ∈ affineAdditiveKernel p π hπ := by
  rw [mem_affineAdditiveKernel_iff]
  refine ⟨g, ?_⟩
  apply SemidirectProduct.ext
  · rfl
  · exact g.property

/-- On the actual cyclotomic-character kernel the Kummer cocycle is additive. -/
def kummerKernelHom (hπ : π ≠ 0) :
    Additive (padicCyclotomicCharacter p π).ker →+ affineAdditiveKernel p π hπ where
  toFun g := ⟨padicKummerExponent p π hπ g.toMul,
    padicKummerExponent_mem_affineAdditiveKernel p π hπ g.toMul⟩
  map_zero' := by
    apply Subtype.ext
    have h := congrArg (fun x : PadicAffineGroup p ↦ x.left.toAdd)
      (map_one (affineGaloisHom p π hπ))
    exact h
  map_add' g h := by
    apply Subtype.ext
    change padicKummerExponent p π hπ (g.toMul.val * h.toMul.val) = _
    rw [padicKummerExponent_mul,
      show padicCyclotomicCharacter p π g.toMul.val = 1 from g.toMul.property]
    simp

/-- The additive kernel homomorphism is the actual Kummer coordinate. -/
theorem kummerKernelHom_apply (hπ : π ≠ 0)
    (g : Additive (padicCyclotomicCharacter p π).ker) :
    (kummerKernelHom p π hπ g : PadicInt p) = padicKummerExponent p π hπ g.toMul := rfl

/-- The actual affine image and coordinate injectivity make the kernel
coordinate map bijective onto precisely the displayed closed subgroup. -/
theorem kummerKernelHom_bijective (hπ : π ≠ 0) :
    Function.Bijective (kummerKernelHom p π hπ) := by
  constructor
  · intro g h heq
    apply Additive.toMul.injective
    apply Subtype.ext
    apply padicCoordinates_injective p π hπ
    exact Prod.ext (congrArg Subtype.val heq) (g.toMul.property.trans h.toMul.property.symm)
  · intro a
    obtain ⟨g, hg⟩ := (mem_affineAdditiveKernel_iff p π hπ a).mp a.property
    have hχ : g ∈ (padicCyclotomicCharacter p π).ker :=
      congrArg SemidirectProduct.right hg
    have hb : padicKummerExponent p π hπ g = a :=
      congrArg (fun x : PadicAffineGroup p ↦ x.left.toAdd) hg
    exact ⟨Additive.ofMul ⟨g, hχ⟩, Subtype.ext hb⟩

/-- Restricting the actual continuous Kummer coordinate gives a continuous
map on the actual character kernel and into the actual additive kernel. -/
theorem continuous_kummerKernelHom (hπ : π ≠ 0) :
    Continuous (kummerKernelHom p π hπ) := by
  apply Continuous.subtype_mk
  exact (continuous_padicKummerExponent p π hπ).comp
    (continuous_subtype_val.comp continuous_toMul)

/-- The Kummer coordinate identifies the actual character kernel with its
closed additive affine kernel as a topological additive group. -/
def kummerKernelEquiv (hπ : π ≠ 0) :
    Additive (padicCyclotomicCharacter p π).ker ≃ₜ+ affineAdditiveKernel p π hπ := by
  have := falseTateExtension_isGalois p π hπ
  have hker : IsClosed ((padicCyclotomicCharacter p π).ker :
      Set (falseTateExtension p π ≃ₐ[K] falseTateExtension p π)) :=
    isClosed_singleton.preimage (continuous_padicCyclotomicCharacter p π)
  have : CompactSpace (padicCyclotomicCharacter p π).ker :=
    isCompact_iff_compactSpace.mp hker.isCompact
  let e := AddEquiv.ofBijective (kummerKernelHom p π hπ) (kummerKernelHom_bijective p π hπ)
  have hc : Continuous e := continuous_kummerKernelHom p π hπ
  exact
    { e with
      continuous_toFun := hc
      continuous_invFun := hc.continuous_symm_of_equiv_compact_to_t2 }

/-- The topological additive identification evaluates to the original actual
Kummer coordinate. -/
theorem kummerKernelEquiv_apply (hπ : π ≠ 0)
    (g : Additive (padicCyclotomicCharacter p π).ker) :
    (kummerKernelEquiv p π hπ g : PadicInt p) = padicKummerExponent p π hπ g.toMul := rfl

end

end FalseTateExtension
