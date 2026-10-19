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
# The translation kernel and the generator τ

For `p ≠ 2`, the additive kernel of the affine image of `Gal(K_FT/K)` is all of `ℤ_[p]`: the kernel
of the cyclotomic character is isomorphic to `ℤ_[p]` as a topological group, with the generator `τ`
characterised by `τ(π^{1/p^n}) = ζ_{p^n} π^{1/p^n}`. Consequently `K_Kum ∩ K_cyc = K` and
`Gal(K_FT/K) ≅ ℤ_[p] ⋊ Gal(K_cyc/K)`.

## References

* Liu, *On lattices in semi-stable representations: a proof of a conjecture of Breuil*, Lemma 5.1.2.
-/

@[expose] public section

noncomputable section

namespace FalseTateExtension

open Polynomial
open FontaineWintenberger

section InfiniteCoordinates

variable {K : Type*} [Field K] [CharZero K] (p : ℕ) [Fact p.Prime] (π : K)

/-- The radical, viewed in the infinite false Tate field. -/
def extensionRadical (n : ℕ) : falseTateExtension p π :=
  IntermediateField.inclusion (falseTateLayer_le_falseTateExtension p π n n)
    (layerRadical p π n)

@[simp]
theorem coe_extensionRadical (n : ℕ) :
    (extensionRadical p π n : AlgebraicClosure K) = radical p π n := rfl

/-- The infinite Kummer coordinate evaluates on each radical. -/
theorem padicKummerExponent_spec [hπ : NeZero π]
    (g : falseTateExtension p π ≃ₐ[K] falseTateExtension p π) (n : ℕ) :
    g (extensionRadical p π n) = extensionRootOfUnity p π n ^
      (PadicInt.toZModPow n (padicKummerExponent p π g)).val *
        extensionRadical p π n := by
  rw [padicKummerExponent_toZModPow p π]
  rw [extensionRadical, ← infiniteLayerRestriction_commutes p π]
  rw [finiteKummerExponent_spec p π n, map_mul, map_pow]
  rfl

/-- The cyclotomic subfield has precisely the character kernel
as its fixing subgroup in the false Tate field. -/
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

/-- Vanishing of the finite Kummer coordinate fixes the corresponding radical. -/
theorem extensionRadical_fixed_of_toZModPow_eq_zero [hπ : NeZero π]
    (g : falseTateExtension p π ≃ₐ[K] falseTateExtension p π) (n : ℕ)
    (hb : PadicInt.toZModPow n (padicKummerExponent p π g) = 0) :
    g (extensionRadical p π n) = extensionRadical p π n := by
  rw [padicKummerExponent_spec p π, hb]
  simp

/-- Fixing by the character kernel places a radical in the
cyclotomic subfield, by infinite Galois correspondence. -/
theorem radical_mem_cyclotomicExtension_of_fixed [hπ : NeZero π] (n : ℕ)
    (hf : ∀ g : (padicCyclotomicCharacter p π).ker,
      g.val (extensionRadical p π n) = extensionRadical p π n) :
    radical p π n ∈ cyclotomicExtension (K := K) p := by
  have := falseTateExtension_isGalois p π
  apply IntermediateField.mem_of_fixed_by_inclusion
    (cyclotomicExtension_le_falseTateExtension p π)
    (extensionRadical p π n)
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

/-- The affine coordinates, with unit coordinate in the
cyclotomic character image rather than in the whole p-adic unit group. -/
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

/-- Restricting the unit coordinate retains continuity in the product topology. -/
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

/-- At an odd prime the closed translation kernel is the whole p-adic
additive group, with the coordinate normalization fixed by the roots. -/
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

/-- The Kummer coordinate is a topological additive isomorphism onto
all p-adic integers at an odd prime. -/
def fullKummerKernelEquiv [hp₂ : Fact (p ≠ 2)] [hπ : Fact (Irreducible π)] :
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

@[simp]
theorem fullKummerKernelEquiv_apply [hp₂ : Fact (p ≠ 2)] [hπ : Fact (Irreducible π)]
    (g : Additive (padicCyclotomicCharacter p (π : K)).ker) :
    fullKummerKernelEquiv p π g =
      padicKummerExponent p (π : K) g.toMul := rfl

/-- The character-kernel automorphism whose Kummer coordinate
is exactly one. -/
def tau [hp₂ : Fact (p ≠ 2)] [hπ : Fact (Irreducible π)] :
    (padicCyclotomicCharacter p (π : K)).ker :=
  ((fullKummerKernelEquiv p π).symm 1).toMul

@[simp]
theorem padicKummerExponent_tau [hp₂ : Fact (p ≠ 2)] [hπ : Fact (Irreducible π)] :
    padicKummerExponent p (π : K)
      (tau p π).val = 1 :=
  (fullKummerKernelEquiv p π).apply_symm_apply 1

/-- The generator acts on every positive-level radical
by multiplication by the corresponding root of unity. -/
theorem tau_extensionRadical [hp₂ : Fact (p ≠ 2)] [hπ : Fact (Irreducible π)] (n : ℕ) :
    (tau p π).val (extensionRadical p (π : K) (n + 1)) =
      extensionRootOfUnity p (π : K) (n + 1) * extensionRadical p (π : K) (n + 1) := by
  rw [padicKummerExponent_spec p (π : K),
    padicKummerExponent_tau, map_one]
  have hpow : 1 < p ^ (n + 1) := one_lt_pow₀ (Fact.out : p.Prime).one_lt (Nat.succ_ne_zero n)
  simp only [ZMod.val_one'' (ne_of_gt hpow), pow_one]

/-- Integral powers of the automorphism are dense in the
cyclotomic-character kernel. -/
theorem denseRange_tau_zpow [hp₂ : Fact (p ≠ 2)] [hπ : Fact (Irreducible π)] :
    DenseRange (fun n : ℤ => tau p π ^ n) := by
  let e := fullKummerKernelEquiv p π
  have hd (a : ℤ_[p]) :
      (e.symm a).toMul ∈ closure (Set.range (fun n : ℤ => tau p π ^ n)) := by
    apply (PadicInt.denseRange_intCast (p := p)).induction_on
      (p := fun a => (e.symm a).toMul ∈
        closure (Set.range (fun n : ℤ => tau p π ^ n))) a
    · exact isClosed_closure.preimage (continuous_toMul.comp e.symm.continuous)
    · intro n
      apply subset_closure
      refine ⟨n, ?_⟩
      have hn : (n : ℤ_[p]) = n • (1 : ℤ_[p]) := by simp
      rw [hn, map_zsmul]
      change tau p π ^ n = tau p π ^ n
      rfl
  intro g
  have hg := hd (e (Additive.ofMul g))
  rw [e.symm_apply_apply] at hg
  exact hg

/-- Every translation coordinate and every cyclotomic unit coordinate
occur together in the Galois group. -/
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

/-- The cyclotomic fixer and radical fixer generate the whole
false Tate Galois group. -/
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

/-- The infinite radical and cyclotomic subfields meet exactly in
the base field, for every odd prime and every uniformizer. -/
theorem kummerExtension_inf_cyclotomicExtension [hp₂ : Fact (p ≠ 2)] [hπ : Fact (Irreducible π)] :
    kummerExtension p (π : K) ⊓ cyclotomicExtension (K := K) p = ⊥ := by
  have := falseTateExtension_isGalois p (π : K)
  apply IntermediateField.inf_eq_bot_of_inclusion_fixingSubgroup_sup_eq_top
    (kummerExtension_le_falseTateExtension p (π : K))
    (cyclotomicExtension_le_falseTateExtension p (π : K))
  rw [cyclotomicInclusion_fixingSubgroup, sup_comm]
  exact cyclotomicKernel_sup_kummerFixing p π

/-- The Krull Galois group is the affine semidirect product
of all translations by the cyclotomic character image. -/
def falseTateGaloisEquiv [hp₂ : Fact (p ≠ 2)] [hπ : Fact (Irreducible π)] :
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

/-- The semidirect isomorphism retains the Kummer coordinate. -/
theorem falseTateGaloisEquiv_left [hp₂ : Fact (p ≠ 2)] [hπ : Fact (Irreducible π)]
    (g : falseTateExtension p (π : K) ≃ₐ[K] falseTateExtension p (π : K)) :
    (falseTateGaloisEquiv p π g).left.toAdd =
      padicKummerExponent p (π : K) g := rfl

/-- The semidirect isomorphism retains the cyclotomic character. -/
theorem falseTateGaloisEquiv_right [hp₂ : Fact (p ≠ 2)] [hπ : Fact (Irreducible π)]
    (g : falseTateExtension p (π : K) ≃ₐ[K] falseTateExtension p (π : K)) :
    (falseTateGaloisEquiv p π g).right.val = padicCyclotomicCharacter p (π : K) g := rfl

/-- The cyclotomic fixer is exactly the translation factor under
the topological semidirect isomorphism. -/
theorem falseTateGaloisEquiv_mem_translations [hp₂ : Fact (p ≠ 2)] [hπ : Fact (Irreducible π)]
    (g : falseTateExtension p (π : K) ≃ₐ[K] falseTateExtension p (π : K)) :
    falseTateGaloisEquiv p π g ∈
      (SemidirectProduct.inl : Multiplicative (ℤ_[p]) →*
        RestrictedPadicAffineGroup p (cyclotomicExtensionCharacter (K := K) p).range).range ↔
      g ∈ (padicCyclotomicCharacter p (π : K)).ker := by
  rw [SemidirectProduct.range_inl_eq_ker_rightHom, MonoidHom.mem_ker, MonoidHom.mem_ker]
  constructor
  · exact fun h => congrArg Subtype.val h
  · exact fun h => Subtype.ext h

/-- The radical fixer is exactly the pure cyclotomic-unit factor. -/
theorem falseTateGaloisEquiv_mem_units [hp₂ : Fact (p ≠ 2)] [hπ : Fact (Irreducible π)]
    (g : falseTateExtension p (π : K) ≃ₐ[K] falseTateExtension p (π : K)) :
    falseTateGaloisEquiv p π g ∈
      (SemidirectProduct.inr : (cyclotomicExtensionCharacter (K := K) p).range →*
        RestrictedPadicAffineGroup p (cyclotomicExtensionCharacter (K := K) p).range).range ↔
      g ∈ falseTateKummerFixing p (π : K) := by
  rw [mem_falseTateKummerFixing_iff p (π : K)]
  constructor
  · rintro ⟨u, hu⟩
    exact (congrArg (fun x => x.left.toAdd) hu).symm
  · intro hb
    refine ⟨(falseTateGaloisEquiv p π g).right, ?_⟩
    apply SemidirectProduct.ext
    · exact congrArg Multiplicative.ofAdd hb.symm
    · rfl

/-- Restriction of the cyclotomic character identifies the
radical fixer with the cyclotomic character image. -/
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

/-- On the radical fixer the factor isomorphism is the
cyclotomic character, with its image as codomain. -/
theorem kummerFixingEquivCyclotomicImage_apply [hp₂ : Fact (p ≠ 2)] [hπ : Fact (Irreducible π)]
    (g : falseTateKummerFixing p (π : K)) :
    (kummerFixingEquivCyclotomicImage p π g).val =
      padicCyclotomicCharacter p (π : K) g.val := rfl

/-- The generator fixes the embedded cyclotomic field. -/
theorem tau_fixes_cyclotomicExtension [hp₂ : Fact (p ≠ 2)] [hπ : Fact (Irreducible π)]
    (x : cyclotomicExtension (K := K) p) :
    (tau p π).val
      (IntermediateField.inclusion (cyclotomicExtension_le_falseTateExtension p (π : K)) x) =
      IntermediateField.inclusion (cyclotomicExtension_le_falseTateExtension p (π : K)) x := by
  have hg : (tau p π).val ∈
      (IntermediateField.inclusion
        (cyclotomicExtension_le_falseTateExtension p (π : K))).fieldRange.fixingSubgroup := by
    rw [cyclotomicInclusion_fixingSubgroup]
    exact (tau p π).property
  exact (IntermediateField.mem_fixingSubgroup_iff _ _).mp hg _ ⟨x, rfl⟩

/-- Fixing the cyclotomic field and the actions on all compatible
positive-level radicals uniquely specify the automorphism. -/
theorem tau_unique [hp₂ : Fact (p ≠ 2)] [hπ : Fact (Irreducible π)]
    (g : (padicCyclotomicCharacter p (π : K)).ker)
    (hg : ∀ n : ℕ, g.val (extensionRadical p (π : K) (n + 1)) =
      extensionRootOfUnity p (π : K) (n + 1) * extensionRadical p (π : K) (n + 1)) :
    g = tau p π := by
  let hπ₀ : (π : K) ≠ 0 := fun h => hπ.out.ne_zero (Subtype.ext h)
  apply Subtype.ext
  apply padicCoordinates_injective p (π : K)
  refine Prod.ext ?_ (g.property.trans (tau p π).property.symm)
  change padicKummerExponent p (π : K) g.val =
    padicKummerExponent p (π : K) (tau p π).val
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
      _ = g.val (i (layerRadical p (π : K) (n + 1))) :=
        infiniteLayerRestriction_commutes p (π : K) (n + 1) g.val _
      _ = i (layerRootOfUnity p (π : K) (n + 1)) * i (layerRadical p (π : K) (n + 1)) := hg n
      _ = _ := by rw [map_mul, map_pow, ZMod.val_one'' (ne_of_gt hpow), pow_one]

/-- Multiplicative notation for the topological Kummer-coordinate isomorphism
on the character kernel. -/
def fullKummerKernelMulEquiv [hp₂ : Fact (p ≠ 2)] [hπ : Fact (Irreducible π)] :
    (padicCyclotomicCharacter p (π : K)).ker ≃ₜ* Multiplicative (ℤ_[p]) := by
  let e := fullKummerKernelEquiv p π
  exact
    { AddEquiv.toMultiplicativeRight e.toAddEquiv with
      continuous_toFun := continuous_ofAdd.comp (e.continuous.comp continuous_ofMul)
      continuous_invFun := continuous_toMul.comp (e.symm.continuous.comp continuous_toAdd) }

end FullTranslation

end FalseTateExtension
end
