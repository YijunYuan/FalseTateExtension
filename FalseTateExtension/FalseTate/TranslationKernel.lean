/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FalseTateExtension.Coordinates.AffineKernel
public import FalseTateExtension.Cyclotomic.CyclicLayers
public import FalseTateExtension.FalseTate.RadicalNotCyclotomic
public import FalseTateExtension.Mathlib.FieldTheory.Galois.InfiniteCorrespondence
public import FalseTateExtension.Mathlib.RingTheory.PowerBasis.Eigenvector
public import FalseTateExtension.FalseTate.StrictAPF
public import Mathlib.FieldTheory.Galois.Abelian
public import Mathlib.FieldTheory.LinearDisjoint
public import Mathlib.RingTheory.ZMod.UnitsCyclic

/-!
# The translation kernel of `Gal(K_FT/K)` and the generator `τ`

Let `K/ℚ_p` be finite with uniformizer `π`, `p ≠ 2`, `K_FT = K(π^{1/p^∞}, ζ_{p^∞})`,
`K_Kum = K(π^{1/p^∞})`, `K_cyc = K(ζ_{p^∞})`, and let `b`, `χ` be the Kummer exponent and the
cyclotomic character on `Γ = Gal(K_FT/K)`. The translation kernel
`{a ∈ ℤ_[p] | (a, 1) ∈ im (b, χ)}` of the affine image of `Γ` is all of `ℤ_[p]`: every closed
subgroup of `ℤ_[p]` other than `ℤ_[p]` lies in `p ℤ_[p]`, and a translation kernel inside
`p ℤ_[p]` would put `π^{1/p}` in `K_cyc`, contradicting `FalseTate/RadicalNotCyclotomic`.
Hence `b : ker χ = Gal(K_FT/K_cyc) → ℤ_[p]` is an isomorphism of topological groups. The
generator `τ = kummerGenerator p π` is the element of `ker χ` with `b(τ) = 1`; it satisfies
`τ(π^{1/p^n}) = ζ_{p^n} π^{1/p^n}` for all `n`, is determined by these equations, and its
integer powers are dense in `ker χ`. Moreover every pair `(a, u)` with `a ∈ ℤ_[p]` and
`u ∈ χ(Gal(K_cyc/K))` is `(b(g), χ(g))` for some `g ∈ Γ`, so `Γ ≅ ℤ_[p] ⋊ χ(Gal(K_cyc/K))` as
topological groups, `Γ = Gal(K_FT/K_cyc) · Gal(K_FT/K_Kum)`, and `K_Kum ∩ K_cyc = K`.

## Main results

* `padicKummerExponent_spec`: `g(π^{1/p^n}) = ζ_{p^n}^{b(g)} π^{1/p^n}`.
* `cyclotomicInclusion_fixingSubgroup`: `Gal(K_FT/K_cyc) = ker χ`.
* `affineAdditiveKernel_eq_top`: the translation kernel of the affine image is `ℤ_[p]`.
* `kummerKernelEquivPadicInt`: `b : ker χ ≃ₜ+ ℤ_[p]`.
* `kummerGenerator`, `tau_extensionRadical`, `tau_unique`, `denseRange_tau_zpow`: the
  generator `τ`.
* `kummerExtension_inf_cyclotomicExtension`: `K_Kum ∩ K_cyc = K`.
* `falseTateGaloisEquivSemidirectProduct`: `Gal(K_FT/K) ≃ₜ* ℤ_[p] ⋊ χ(Gal(K_cyc/K))`.
* `kummerFixingEquivCyclotomicImage`: `Gal(K_FT/K_Kum) ≃ₜ* χ(Gal(K_cyc/K))`.

## References

* Liu, *On lattices in semi-stable representations: a proof of a conjecture of Breuil*,
  Lemma 5.1.2.
-/

@[expose] public section

noncomputable section

namespace FalseTateExtension

open Polynomial
open FontaineWintenberger

section InfiniteCoordinates

variable {K : Type*} [Field K] [CharZero K] (p : ℕ) [Fact p.Prime] (π : K)

/-- `π^{1/p^n}` as an element of `K_FT`. -/
def pPowRootExt (n : ℕ) : falseTateExtension p π :=
  IntermediateField.inclusion (falseTateLayer_le_falseTateExtension p π n n)
    (pPowRootLayer p π n)

/-- `pPowRootExt p π n` is `π^{1/p^n}` in the algebraic closure. -/
@[simp]
theorem coe_extensionRadical (n : ℕ) :
    (pPowRootExt p π n : AlgebraicClosure K) = pPowRoot p π n := rfl

/-- `g(π^{1/p^n}) = ζ_{p^n}^{b(g)} π^{1/p^n}` in `K_FT`, where `b(g) ∈ ℤ_[p]` is reduced
modulo `p^n`. -/
theorem padicKummerExponent_spec [hπ : NeZero π]
    (g : falseTateExtension p π ≃ₐ[K] falseTateExtension p π) (n : ℕ) :
    g (pPowRootExt p π n) = zetaExt p π n ^
      (PadicInt.toZModPow n (padicKummerExponent p π g)).val *
        pPowRootExt p π n := by
  rw [padicKummerExponent_toZModPow p π]
  rw [pPowRootExt, ← infiniteLayerRestriction_commutes p π]
  rw [finiteKummerExponent_spec p π n, map_mul, map_pow]
  rfl

/-- The subgroup `Gal(K_FT/K_cyc)` of `Gal(K_FT/K)` fixing `K_cyc` is `ker χ`. -/
theorem cyclotomicInclusion_fixingSubgroup :
    (IntermediateField.inclusion
      (cyclotomicExtension_le_falseTateExtension p π)).fieldRange.fixingSubgroup =
        (padicCyclotomicCharacter p π).ker := by
  rw [padicCyclotomicCharacter_ker]
  let i := IntermediateField.inclusion (cyclotomicExtension_le_falseTateExtension p π)
  ext g
  rw [MonoidHom.mem_ker]
  constructor
  · intro hg
    apply AlgEquiv.ext
    intro x
    apply i.injective
    change i (cyclotomicRestriction p π g x) = i x
    rw [cyclotomicRestriction_commutes]
    exact (IntermediateField.mem_fixingSubgroup_iff i.fieldRange g).mp hg (i x) ⟨x, rfl⟩
  · intro hg
    rw [IntermediateField.mem_fixingSubgroup_iff]
    rintro x ⟨y, rfl⟩
    have h := cyclotomicRestriction_commutes p π g y
    rw [hg] at h
    exact h.symm

/-- If `b(g) ≡ 0 mod p^n`, then `g` fixes `π^{1/p^n}`. -/
theorem extensionRadical_fixed_of_toZModPow_eq_zero [hπ : NeZero π]
    (g : falseTateExtension p π ≃ₐ[K] falseTateExtension p π) (n : ℕ)
    (hb : PadicInt.toZModPow n (padicKummerExponent p π g) = 0) :
    g (pPowRootExt p π n) = pPowRootExt p π n := by
  rw [padicKummerExponent_spec p π, hb]
  simp

/-- If every `g ∈ ker χ` fixes `π^{1/p^n}`, then `π^{1/p^n} ∈ K_cyc`. -/
theorem radical_mem_cyclotomicExtension_of_fixed [hπ : NeZero π] (n : ℕ)
    (hf : ∀ g : (padicCyclotomicCharacter p π).ker,
      g.val (pPowRootExt p π n) = pPowRootExt p π n) :
    pPowRoot p π n ∈ cyclotomicExtension (K := K) p := by
  have := falseTateExtension_isGalois p π
  apply IntermediateField.mem_of_fixed_by_inclusion
    (cyclotomicExtension_le_falseTateExtension p π)
    (pPowRootExt p π n)
  intro g hg
  have hg' : g ∈ (padicCyclotomicCharacter p π).ker := by
    rwa [← cyclotomicInclusion_fixingSubgroup p π]
  exact hf ⟨g, hg'⟩

end InfiniteCoordinates

section RestrictedAffineGroup

variable (p : ℕ) [Fact p.Prime] (H : Subgroup (ℤ_[p])ˣ)

/-- The affine group `ℤ_[p] ⋊ H` for a subgroup `H ≤ ℤ_[p]ˣ`. -/
abbrev RestrictedPadicAffineGroup : Type := AffineGroup ℤ_[p] H.subtype

end RestrictedAffineGroup

section RestrictedCoordinates

variable {K : Type*} [Field K] [CharZero K] (p : ℕ) [Fact p.Prime] (π : K)

/-- The homomorphism `Gal(K_FT/K) →* ℤ_[p] ⋊ χ(Gal(K_cyc/K))`, `g ↦ (b(g), χ(g))`. -/
def restrictedAffineGaloisHom [hπ : NeZero π] :
    (falseTateExtension p π ≃ₐ[K] falseTateExtension p π) →*
      RestrictedPadicAffineGroup p (cyclotomicExtensionCharacter (K := K) p).range where
  toFun g := ⟨Multiplicative.ofAdd (padicKummerExponent p π g),
    ⟨padicCyclotomicCharacter p π g, by
      rw [← padicCyclotomicCharacter_range p π]
      exact ⟨g, rfl⟩⟩⟩
  map_one' := by
    apply SemidirectProduct.ext
    · exact congrArg (fun x : PadicAffineGroup p => x.left) (map_one (affineGaloisHom p π))
    · apply Subtype.ext
      exact map_one (padicCyclotomicCharacter p π)
  map_mul' g h := by
    apply SemidirectProduct.ext
    · exact congrArg (fun x : PadicAffineGroup p => x.left) (map_mul (affineGaloisHom p π) g h)
    · apply Subtype.ext
      exact map_mul (padicCyclotomicCharacter p π) g h

/-- `g ↦ (b(g), χ(g))` is continuous into `ℤ_[p] ⋊ χ(Gal(K_cyc/K))`. -/
theorem continuous_restrictedAffineGaloisHom [hπ : NeZero π] :
    Continuous (restrictedAffineGaloisHom p π) := by
  apply continuous_induced_rng.mpr
  exact (continuous_padicKummerExponent p π).prodMk
    ((continuous_padicCyclotomicCharacter p π).subtype_mk _)

end RestrictedCoordinates

section FullTranslation

variable {K : Type*} [NontriviallyNormedField K] [IsCompleteDiscreteValuedField K] [CharZero K]
variable (p : ℕ) [Fact p.Prime] [Algebra (ℚ_[p]) K]
variable (π : 𝒪[K])

/-- A closed additive subgroup `M ≠ ℤ_[p]` of `ℤ_[p]` lies in `p ℤ_[p]`: `a ≡ 0 mod p` for
`a ∈ M`. -/
theorem closedAddSubgroup_toZModPow_one_eq_zero
    (M : ClosedAddSubgroup (ℤ_[p])) (hM : M.toAddSubgroup ≠ ⊤)
    {a : ℤ_[p]} (ha : a ∈ M) : PadicInt.toZModPow 1 a = 0 := by
  let J := PadicInt.closedAddSubgroupIdeal M
  have hJ : J ≠ ⊤ := by
    intro h
    apply hM
    exact congrArg (fun I : Ideal (ℤ_[p]) => I.toAddSubgroup) h
  have hle : J ≤ RingHom.ker (PadicInt.toZModPow 1 : ℤ_[p] →+* ZMod (p ^ 1)) := by
    rw [PadicInt.ker_toZModPow, pow_one, ← PadicInt.maximalIdeal_eq_span_p]
    exact IsLocalRing.le_maximalIdeal hJ
  exact hle ha

/-- For `p ≠ 2`, the translation kernel `{a | (a, 1) ∈ im (b, χ)}` of the affine image of
`Gal(K_FT/K)` is all of `ℤ_[p]`. -/
theorem affineAdditiveKernel_eq_top [hp₂ : Fact (p ≠ 2)] [hπ : Fact (Irreducible π)] :
    (affineAdditiveKernel p (π : K)).toAddSubgroup = ⊤ := by
  let hπ₀ : (π : K) ≠ 0 := fun h => hπ.out.ne_zero (Subtype.ext h)
  by_contra hM
  apply radical_one_not_mem_cyclotomicExtension p π
  apply radical_mem_cyclotomicExtension_of_fixed p (π : K) 1
  intro g
  apply extensionRadical_fixed_of_toZModPow_eq_zero p (π : K) g.val 1
  exact closedAddSubgroup_toZModPow_one_eq_zero p
    (affineAdditiveKernel p (π : K)) hM
    (padicKummerExponent_mem_affineAdditiveKernel p (π : K) g)

/-- For `p ≠ 2`, the Kummer exponent `b` is an isomorphism of topological additive groups
`ker χ ≃ₜ+ ℤ_[p]`. -/
def kummerKernelEquivPadicInt [hp₂ : Fact (p ≠ 2)] [hπ : Fact (Irreducible π)] :
    Additive (padicCyclotomicCharacter p (π : K)).ker ≃ₜ+ ℤ_[p] := by
  let hπ₀ : (π : K) ≠ 0 := fun h => hπ.out.ne_zero (Subtype.ext h)
  let f : Additive (padicCyclotomicCharacter p (π : K)).ker →+ ℤ_[p] :=
    (affineAdditiveKernel p (π : K)).toAddSubgroup.subtype.comp
      (kummerKernelHom p (π : K))
  have hf : Function.Bijective f := by
    constructor
    · intro g h heq
      apply (kummerKernelHom_bijective p (π : K)).injective
      exact Subtype.ext heq
    · intro a
      have ha : a ∈ affineAdditiveKernel p (π : K) := by
        change a ∈ (affineAdditiveKernel p (π : K)).toAddSubgroup
        rw [affineAdditiveKernel_eq_top p π]
        trivial
      obtain ⟨g, hg⟩ := (kummerKernelHom_bijective p (π : K)).surjective ⟨a, ha⟩
      exact ⟨g, congrArg Subtype.val hg⟩
  have := falseTateExtension_isGalois p (π : K)
  have hclosed : IsClosed ((padicCyclotomicCharacter p (π : K)).ker :
      Set (falseTateExtension p (π : K) ≃ₐ[K] falseTateExtension p (π : K))) :=
    isClosed_singleton.preimage (continuous_padicCyclotomicCharacter p (π : K))
  have : CompactSpace (padicCyclotomicCharacter p (π : K)).ker :=
    isCompact_iff_compactSpace.mp hclosed.isCompact
  let e := AddEquiv.ofBijective f hf
  have hc : Continuous e := continuous_subtype_val.comp
    (continuous_kummerKernelHom p (π : K))
  exact { e with
    continuous_toFun := hc
    continuous_invFun := hc.continuous_symm_of_equiv_compact_to_t2 }

/-- `kummerKernelEquivPadicInt g = b(g)` for `g ∈ ker χ`. -/
@[simp]
theorem fullKummerKernelEquiv_apply [hp₂ : Fact (p ≠ 2)] [hπ : Fact (Irreducible π)]
    (g : Additive (padicCyclotomicCharacter p (π : K)).ker) :
    kummerKernelEquivPadicInt p π g =
      padicKummerExponent p (π : K) g.toMul := rfl

/-- The generator `τ` of `ker χ = Gal(K_FT/K_cyc)`: the element with `b(τ) = 1`. -/
def kummerGenerator [hp₂ : Fact (p ≠ 2)] [hπ : Fact (Irreducible π)] :
    (padicCyclotomicCharacter p (π : K)).ker :=
  ((kummerKernelEquivPadicInt p π).symm 1).toMul

/-- `b(τ) = 1`. -/
@[simp]
theorem padicKummerExponent_tau [hp₂ : Fact (p ≠ 2)] [hπ : Fact (Irreducible π)] :
    padicKummerExponent p (π : K)
      (kummerGenerator p π).val = 1 :=
  (kummerKernelEquivPadicInt p π).apply_symm_apply 1

/-- `τ(π^{1/p^{n+1}}) = ζ_{p^{n+1}} π^{1/p^{n+1}}` in `K_FT`. -/
theorem tau_extensionRadical [hp₂ : Fact (p ≠ 2)] [hπ : Fact (Irreducible π)] (n : ℕ) :
    (kummerGenerator p π).val (pPowRootExt p (π : K) (n + 1)) =
      zetaExt p (π : K) (n + 1) * pPowRootExt p (π : K) (n + 1) := by
  rw [padicKummerExponent_spec p (π : K),
    padicKummerExponent_tau, map_one]
  have hpow : 1 < p ^ (n + 1) := one_lt_pow₀ (Fact.out : p.Prime).one_lt (Nat.succ_ne_zero n)
  simp only [ZMod.val_one'' (ne_of_gt hpow), pow_one]

/-- The powers `τ^n`, `n ∈ ℤ`, are dense in `ker χ = Gal(K_FT/K_cyc)`. -/
theorem denseRange_tau_zpow [hp₂ : Fact (p ≠ 2)] [hπ : Fact (Irreducible π)] :
    DenseRange (fun n : ℤ => kummerGenerator p π ^ n) := by
  let e := kummerKernelEquivPadicInt p π
  have hd (a : ℤ_[p]) :
      (e.symm a).toMul ∈ closure (Set.range (fun n : ℤ => kummerGenerator p π ^ n)) := by
    apply (PadicInt.denseRange_intCast (p := p)).induction_on
      (p := fun a => (e.symm a).toMul ∈
        closure (Set.range (fun n : ℤ => kummerGenerator p π ^ n))) a
    · exact isClosed_closure.preimage (continuous_toMul.comp e.symm.continuous)
    · intro n
      apply subset_closure
      refine ⟨n, ?_⟩
      have hn : (n : ℤ_[p]) = n • (1 : ℤ_[p]) := by simp
      rw [hn, map_zsmul]
      change kummerGenerator p π ^ n = kummerGenerator p π ^ n
      rfl
  intro g
  have hg := hd (e (Additive.ofMul g))
  rw [e.symm_apply_apply] at hg
  exact hg

/-- For `p ≠ 2`, every `a ∈ ℤ_[p]` and `u ∈ χ(Gal(K_cyc/K))` are the coordinates
`(b(g), χ(g))` of some `g ∈ Gal(K_FT/K)`. -/
theorem exists_padicCoordinates_eq [hp₂ : Fact (p ≠ 2)] [hπ : Fact (Irreducible π)]
    (b : ℤ_[p]) (u : (ℤ_[p])ˣ)
    (hu : u ∈ (cyclotomicExtensionCharacter (K := K) p).range) :
    ∃ g : falseTateExtension p (π : K) ≃ₐ[K] falseTateExtension p (π : K),
      padicKummerExponent p (π : K) g = b ∧
        padicCyclotomicCharacter p (π : K) g = u := by
  let hπ₀ : (π : K) ≠ 0 := fun h => hπ.out.ne_zero (Subtype.ext h)
  rw [← padicCyclotomicCharacter_range p (π : K)] at hu
  obtain ⟨g, rfl⟩ := hu
  let a := b - padicKummerExponent p (π : K) g
  have ha : a ∈ affineAdditiveKernel p (π : K) := by
    change a ∈ (affineAdditiveKernel p (π : K)).toAddSubgroup
    rw [affineAdditiveKernel_eq_top p π]
    trivial
  obtain ⟨t, ht⟩ := (mem_affineAdditiveKernel_iff p (π : K) a).mp ha
  have htb : padicKummerExponent p (π : K) t = a :=
    congrArg (fun x : PadicAffineGroup p => x.left.toAdd) ht
  have htχ : padicCyclotomicCharacter p (π : K) t = 1 :=
    congrArg SemidirectProduct.right ht
  refine ⟨t * g, ?_, ?_⟩
  · rw [padicKummerExponent_mul, htb, htχ]
    simp only [Units.val_one, one_mul]
    exact sub_add_cancel b _
  · rw [map_mul, htχ, one_mul]

/-- `Gal(K_FT/K) = Gal(K_FT/K_cyc) · Gal(K_FT/K_Kum)`, i.e. `ker χ ⊔ Gal(K_FT/K_Kum) = ⊤`. -/
theorem cyclotomicKernel_sup_kummerFixing [hp₂ : Fact (p ≠ 2)] [hπ : Fact (Irreducible π)] :
    (padicCyclotomicCharacter p (π : K)).ker ⊔ falseTateKummerFixing p (π : K) = ⊤ := by
  let hπ₀ : (π : K) ≠ 0 := fun h => hπ.out.ne_zero (Subtype.ext h)
  apply top_unique
  intro g _
  have hχg : padicCyclotomicCharacter p (π : K) g ∈
      (cyclotomicExtensionCharacter (K := K) p).range := by
    rw [← padicCyclotomicCharacter_range p (π : K)]
    exact ⟨g, rfl⟩
  obtain ⟨s, hsb, hsχ⟩ := exists_padicCoordinates_eq p π 0 _ hχg
  have hs : s ∈ falseTateKummerFixing p (π : K) :=
    (mem_falseTateKummerFixing_iff p (π : K) s).mpr hsb
  have ht : g * s⁻¹ ∈ (padicCyclotomicCharacter p (π : K)).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hsχ, mul_inv_cancel]
  have h := Subgroup.mul_mem_sup ht hs
  simpa only [inv_mul_cancel_right] using h

/-- For `p ≠ 2`, `K_Kum ∩ K_cyc = K`. -/
theorem kummerExtension_inf_cyclotomicExtension [hp₂ : Fact (p ≠ 2)] [hπ : Fact (Irreducible π)] :
    kummerExtension p (π : K) ⊓ cyclotomicExtension (K := K) p = ⊥ := by
  have := falseTateExtension_isGalois p (π : K)
  apply IntermediateField.inf_eq_bot_of_inclusion_fixingSubgroup_sup_eq_top
    (kummerExtension_le_falseTateExtension p (π : K))
    (cyclotomicExtension_le_falseTateExtension p (π : K))
  rw [cyclotomicInclusion_fixingSubgroup, sup_comm]
  exact cyclotomicKernel_sup_kummerFixing p π

/-- For `p ≠ 2`, `g ↦ (b(g), χ(g))` is an isomorphism of topological groups
`Gal(K_FT/K) ≃ₜ* ℤ_[p] ⋊ χ(Gal(K_cyc/K))`. -/
def falseTateGaloisEquivSemidirectProduct [hp₂ : Fact (p ≠ 2)] [hπ : Fact (Irreducible π)] :
    (falseTateExtension p (π : K) ≃ₐ[K] falseTateExtension p (π : K)) ≃ₜ*
      RestrictedPadicAffineGroup p (cyclotomicExtensionCharacter (K := K) p).range := by
  let hπ₀ : (π : K) ≠ 0 := fun h => hπ.out.ne_zero (Subtype.ext h)
  let f := restrictedAffineGaloisHom p (π : K)
  have hf : Function.Bijective f := by
    constructor
    · intro g h heq
      apply padicCoordinates_injective p (π : K)
      exact Prod.ext (congrArg (fun x => x.left.toAdd) heq)
        (congrArg (fun x => x.right.val) heq)
    · intro x
      obtain ⟨g, hb, hχ⟩ := exists_padicCoordinates_eq p π x.left.toAdd x.right.val
        x.right.property
      refine ⟨g, ?_⟩
      apply SemidirectProduct.ext
      · exact congrArg Multiplicative.ofAdd hb
      · exact Subtype.ext hχ
  have := falseTateExtension_isGalois p (π : K)
  let e := MulEquiv.ofBijective f hf
  have hc : Continuous e := continuous_restrictedAffineGaloisHom p (π : K)
  exact { e with
    continuous_toFun := hc
    continuous_invFun := hc.continuous_symm_of_equiv_compact_to_t2 }

/-- The translation coordinate of `falseTateGaloisEquivSemidirectProduct g` is `b(g)`. -/
theorem falseTateGaloisEquiv_left [hp₂ : Fact (p ≠ 2)] [hπ : Fact (Irreducible π)]
    (g : falseTateExtension p (π : K) ≃ₐ[K] falseTateExtension p (π : K)) :
    (falseTateGaloisEquivSemidirectProduct p π g).left.toAdd =
      padicKummerExponent p (π : K) g := rfl

/-- The unit coordinate of `falseTateGaloisEquivSemidirectProduct g` is `χ(g)`. -/
theorem falseTateGaloisEquiv_right [hp₂ : Fact (p ≠ 2)] [hπ : Fact (Irreducible π)]
    (g : falseTateExtension p (π : K) ≃ₐ[K] falseTateExtension p (π : K)) :
    (falseTateGaloisEquivSemidirectProduct p π g).right.val =
      padicCyclotomicCharacter p (π : K) g := rfl

/-- `(b(g), χ(g))` lies in the translation factor `ℤ_[p] ⋊ 1` if and only if `g ∈ ker χ`. -/
theorem falseTateGaloisEquiv_mem_translations [hp₂ : Fact (p ≠ 2)] [hπ : Fact (Irreducible π)]
    (g : falseTateExtension p (π : K) ≃ₐ[K] falseTateExtension p (π : K)) :
    falseTateGaloisEquivSemidirectProduct p π g ∈
      (SemidirectProduct.inl : Multiplicative (ℤ_[p]) →*
        RestrictedPadicAffineGroup p (cyclotomicExtensionCharacter (K := K) p).range).range ↔
      g ∈ (padicCyclotomicCharacter p (π : K)).ker := by
  rw [SemidirectProduct.range_inl_eq_ker_rightHom, MonoidHom.mem_ker, MonoidHom.mem_ker]
  constructor
  · exact fun h => congrArg Subtype.val h
  · exact fun h => Subtype.ext h

/-- `(b(g), χ(g))` lies in the unit factor `0 ⋊ χ(Gal(K_cyc/K))` if and only if
`g ∈ Gal(K_FT/K_Kum)`. -/
theorem falseTateGaloisEquiv_mem_units [hp₂ : Fact (p ≠ 2)] [hπ : Fact (Irreducible π)]
    (g : falseTateExtension p (π : K) ≃ₐ[K] falseTateExtension p (π : K)) :
    falseTateGaloisEquivSemidirectProduct p π g ∈
      (SemidirectProduct.inr : (cyclotomicExtensionCharacter (K := K) p).range →*
        RestrictedPadicAffineGroup p (cyclotomicExtensionCharacter (K := K) p).range).range ↔
      g ∈ falseTateKummerFixing p (π : K) := by
  rw [mem_falseTateKummerFixing_iff p (π : K)]
  constructor
  · rintro ⟨u, hu⟩
    exact (congrArg (fun x => x.left.toAdd) hu).symm
  · intro hb
    refine ⟨(falseTateGaloisEquivSemidirectProduct p π g).right, ?_⟩
    apply SemidirectProduct.ext
    · exact congrArg Multiplicative.ofAdd hb.symm
    · rfl

/-- For `p ≠ 2`, `χ` restricts to an isomorphism of topological groups
`Gal(K_FT/K_Kum) ≃ₜ* χ(Gal(K_cyc/K))`. -/
def kummerFixingEquivCyclotomicImage [hp₂ : Fact (p ≠ 2)] [hπ : Fact (Irreducible π)] :
    falseTateKummerFixing p (π : K) ≃ₜ* (cyclotomicExtensionCharacter (K := K) p).range := by
  let hπ₀ : (π : K) ≠ 0 := fun h => hπ.out.ne_zero (Subtype.ext h)
  let f : falseTateKummerFixing p (π : K) →*
      (cyclotomicExtensionCharacter (K := K) p).range :=
    ((SemidirectProduct.rightHom.comp (restrictedAffineGaloisHom p (π : K))).comp
      (falseTateKummerFixing p (π : K)).subtype)
  have hf : Function.Bijective f := by
    constructor
    · intro g h heq
      apply Subtype.ext
      apply padicCoordinates_injective p (π : K)
      refine Prod.ext ?_ (congrArg Subtype.val heq)
      exact ((mem_falseTateKummerFixing_iff p (π : K) g.val).mp g.property).trans
        ((mem_falseTateKummerFixing_iff p (π : K) h.val).mp h.property).symm
    · intro u
      obtain ⟨g, hb, hχ⟩ := exists_padicCoordinates_eq p π 0 u.val u.property
      refine ⟨⟨g, (mem_falseTateKummerFixing_iff p (π : K) g).mpr hb⟩, ?_⟩
      exact Subtype.ext hχ
  have := falseTateExtension_isGalois p (π : K)
  have hclosed : IsClosed (falseTateKummerFixing p (π : K) :
      Set (falseTateExtension p (π : K) ≃ₐ[K] falseTateExtension p (π : K))) := by
    have heq : (falseTateKummerFixing p (π : K) :
        Set (falseTateExtension p (π : K) ≃ₐ[K] falseTateExtension p (π : K))) =
        (padicKummerExponent p (π : K)) ⁻¹' {0} := by
      ext g
      exact mem_falseTateKummerFixing_iff p (π : K) g
    rw [heq]
    exact isClosed_singleton.preimage (continuous_padicKummerExponent p (π : K))
  have : CompactSpace (falseTateKummerFixing p (π : K)) :=
    isCompact_iff_compactSpace.mp hclosed.isCompact
  let e := MulEquiv.ofBijective f hf
  have hc : Continuous e := ((continuous_padicCyclotomicCharacter p (π : K)).comp
    continuous_subtype_val).subtype_mk _
  exact { e with
    continuous_toFun := hc
    continuous_invFun := hc.continuous_symm_of_equiv_compact_to_t2 }

/-- `kummerFixingEquivCyclotomicImage g = χ(g)` for `g ∈ Gal(K_FT/K_Kum)`. -/
theorem kummerFixingEquivCyclotomicImage_apply [hp₂ : Fact (p ≠ 2)] [hπ : Fact (Irreducible π)]
    (g : falseTateKummerFixing p (π : K)) :
    (kummerFixingEquivCyclotomicImage p π g).val =
      padicCyclotomicCharacter p (π : K) g.val := rfl

/-- `τ` fixes `K_cyc` pointwise. -/
theorem tau_fixes_cyclotomicExtension [hp₂ : Fact (p ≠ 2)] [hπ : Fact (Irreducible π)]
    (x : cyclotomicExtension (K := K) p) :
    (kummerGenerator p π).val
      (IntermediateField.inclusion (cyclotomicExtension_le_falseTateExtension p (π : K)) x) =
      IntermediateField.inclusion (cyclotomicExtension_le_falseTateExtension p (π : K)) x := by
  have hg : (kummerGenerator p π).val ∈
      (IntermediateField.inclusion
        (cyclotomicExtension_le_falseTateExtension p (π : K))).fieldRange.fixingSubgroup := by
    rw [cyclotomicInclusion_fixingSubgroup]
    exact (kummerGenerator p π).property
  exact (IntermediateField.mem_fixingSubgroup_iff _ _).mp hg _ ⟨x, rfl⟩

/-- An element `g ∈ ker χ` with `g(π^{1/p^{n+1}}) = ζ_{p^{n+1}} π^{1/p^{n+1}}` for all `n`
is `τ`. -/
theorem tau_unique [hp₂ : Fact (p ≠ 2)] [hπ : Fact (Irreducible π)]
    (g : (padicCyclotomicCharacter p (π : K)).ker)
    (hg : ∀ n : ℕ, g.val (pPowRootExt p (π : K) (n + 1)) =
      zetaExt p (π : K) (n + 1) * pPowRootExt p (π : K) (n + 1)) :
    g = kummerGenerator p π := by
  let hπ₀ : (π : K) ≠ 0 := fun h => hπ.out.ne_zero (Subtype.ext h)
  apply Subtype.ext
  apply padicCoordinates_injective p (π : K)
  refine Prod.ext ?_ (g.property.trans (kummerGenerator p π).property.symm)
  change padicKummerExponent p (π : K) g.val =
    padicKummerExponent p (π : K) (kummerGenerator p π).val
  rw [padicKummerExponent_tau]
  apply PadicInt.ext_of_toZModPow.mp
  intro n
  rw [map_one]
  cases n with
  | zero =>
    have : Subsingleton (ZMod (p ^ 0)) := by
      simpa only [pow_zero] using (inferInstance : Subsingleton (ZMod 1))
    exact Subsingleton.elim _ _
  | succ n =>
    rw [padicKummerExponent_toZModPow]
    apply finiteKummerExponent_unique p (π : K) (n + 1) _ 1
    let i := IntermediateField.inclusion
      (falseTateLayer_le_falseTateExtension p (π : K) (n + 1) (n + 1))
    apply (show Function.Injective i from i.injective)
    have hpow : 1 < p ^ (n + 1) :=
      one_lt_pow₀ (Fact.out : p.Prime).one_lt (Nat.succ_ne_zero n)
    calc
      _ = g.val (i (pPowRootLayer p (π : K) (n + 1))) :=
        infiniteLayerRestriction_commutes p (π : K) (n + 1) g.val _
      _ = i (zetaLayer p (π : K) (n + 1)) * i (pPowRootLayer p (π : K) (n + 1)) := hg n
      _ = _ := by rw [map_mul, map_pow, ZMod.val_one'' (ne_of_gt hpow), pow_one]

/-- For `p ≠ 2`, the Kummer exponent `b` as an isomorphism of topological groups
`ker χ ≃ₜ* Multiplicative ℤ_[p]`. -/
def kummerKernelMulEquivPadicInt [hp₂ : Fact (p ≠ 2)] [hπ : Fact (Irreducible π)] :
    (padicCyclotomicCharacter p (π : K)).ker ≃ₜ* Multiplicative (ℤ_[p]) := by
  let e := kummerKernelEquivPadicInt p π
  exact
    { AddEquiv.toMultiplicativeRight e.toAddEquiv with
      continuous_toFun := continuous_ofAdd.comp (e.continuous.comp continuous_ofMul)
      continuous_invFun := continuous_toMul.comp (e.symm.continuous.comp continuous_toAdd) }

end FullTranslation

end FalseTateExtension
end
