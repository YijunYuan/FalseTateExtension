/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FalseTateExtension.Coordinates.AffineEmbedding
public import FalseTateExtension.Mathlib.FieldTheory.RestrictNormal

/-!
# Restriction to the cyclotomic extension

Let `K` be a field of characteristic zero, `p` a prime, `π ∈ K` nonzero, `K_cyc = K(ζ_{p^∞})`
and `K_FT = K(π^{1/p^∞}, ζ_{p^∞})`. The cyclotomic character `Gal(K_cyc/K) → ℤ_p^×` is
injective and continuous, hence a closed embedding of the Krull topology. Restriction
`Gal(K_FT/K) → Gal(K_cyc/K)` is a continuous surjection through which the cyclotomic character
`χ` of `Gal(K_FT/K)` factors; its kernel is `ker χ`. Consequently `Gal(K_cyc/K)` is isomorphic,
as a topological group, to the image `χ(Gal(K_FT/K)) ⊆ ℤ_p^×`.

## Main results

* `cyclotomicExtensionCharacter`, `cyclotomicExtensionCharacter_injective`,
  `isClosedEmbedding_cyclotomicExtensionCharacter`: the cyclotomic character of
  `Gal(K_cyc/K)` is a closed embedding into `ℤ_p^×`.
* `cyclotomicRestriction`, `cyclotomicRestriction_surjective`,
  `continuous_cyclotomicRestriction`: restriction `Gal(K_FT/K) → Gal(K_cyc/K)`.
* `padicCyclotomicCharacter_eq_comp`, `padicCyclotomicCharacter_ker`: `χ` factors through
  restriction, with the same kernel.
* `cyclotomicImageEquiv`: `Gal(K_cyc/K) ≅ χ(Gal(K_FT/K))` as topological groups.

## References

* [Tong Liu, *On lattices in semi-stable representations: a proof of a conjecture of
  Breuil*](https://doi.org/10.1112/S0010437X0700317X), §5.1.
-/

@[expose] public section

namespace FalseTateExtension

noncomputable section

variable {K : Type*} [Field K] [CharZero K] (p : ℕ) [Fact p.Prime]

/-- `ζ_{p^n}` as an element of `K_cyc = K(ζ_{p^∞})`. -/
def zetaCycExt (n : ℕ) : cyclotomicExtension (K := K) p :=
  ⟨zeta p n, cyclotomicLayer_le_cyclotomicExtension p n
    (zeta_mem_cyclotomicLayer p n)⟩

/-- `ζ_{p^n}` is a primitive `p^n`-th root of unity in `K_cyc`. -/
theorem isPrimitiveRoot_zetaCycExt (n : ℕ) :
    IsPrimitiveRoot (zetaCycExt (K := K) p n) (p ^ n) :=
  (isPrimitiveRoot_zeta (K := K) p n).of_map_of_injective
    (f := (cyclotomicExtension (K := K) p).val) (cyclotomicExtension p).val.injective

/-- `K_cyc` contains a primitive `p^n`-th root of unity for every `n`. -/
instance cyclotomicExtension_hasEnoughRootsOfUnity (n : ℕ) :
    HasEnoughRootsOfUnity (cyclotomicExtension (K := K) p) (p ^ n) :=
  ⟨⟨zetaCycExt p n, isPrimitiveRoot_zetaCycExt p n⟩,
    rootsOfUnity.isCyclic _ _⟩

/-- The cyclotomic character `Gal(K_cyc/K) → ℤ_p^×`, given by `g(ζ) = ζ^{χ(g)}` for every
`p`-power root of unity `ζ`. -/
abbrev cyclotomicExtensionCharacter :
    (cyclotomicExtension (K := K) p ≃ₐ[K] cyclotomicExtension (K := K) p) →* (ℤ_[p])ˣ :=
  intermediateFieldCyclotomicCharacter p (cyclotomicExtension (K := K) p)

/-- The cyclotomic character of `Gal(K_cyc/K)` is continuous for the Krull topology. -/
theorem continuous_cyclotomicExtensionCharacter :
    Continuous (cyclotomicExtensionCharacter (K := K) p) :=
  continuous_intermediateFieldCyclotomicCharacter p _

/-- `g(ζ_{p^n}) = ζ_{p^n}^{χ(g)}` for `g ∈ Gal(K_cyc/K)`. -/
theorem cyclotomicExtensionCharacter_spec (n : ℕ)
    (g : cyclotomicExtension (K := K) p ≃ₐ[K] cyclotomicExtension (K := K) p) :
    g (zetaCycExt p n) = zetaCycExt p n ^
      (PadicInt.toZModPow n (cyclotomicExtensionCharacter p g : ℤ_[p])).val :=
  _root_.cyclotomicCharacter.spec p g.toRingEquiv (zetaCycExt p n)
    (isPrimitiveRoot_zetaCycExt p n).pow_eq_one

/-- The cyclotomic character of `Gal(K_cyc/K)` is injective. -/
theorem cyclotomicExtensionCharacter_injective :
    Function.Injective (cyclotomicExtensionCharacter (K := K) p) := by
  intro g h heq
  have hroot (n : ℕ) : g (zetaCycExt p n) = h (zetaCycExt p n) := by
    rw [cyclotomicExtensionCharacter_spec, cyclotomicExtensionCharacter_spec, heq]
  apply AlgEquiv.ext
  intro x
  obtain ⟨n, hn⟩ := (mem_cyclotomicExtension_iff p (x : AlgebraicClosure K)).mp x.property
  let i := IntermediateField.inclusion (cyclotomicLayer_le_cyclotomicExtension (K := K) p n)
  have hres : g.toAlgHom.comp i = h.toAlgHom.comp i := by
    apply IntermediateField.algHom_ext_of_eq_adjoin (F := K)
      (rfl : cyclotomicLayer (K := K) p n =
      IntermediateField.adjoin K {zeta p n})
    intro y hy
    obtain rfl := Set.mem_singleton_iff.mp hy
    exact hroot n
  exact congrArg (fun f : cyclotomicLayer p n →ₐ[K] cyclotomicExtension p ↦ f ⟨x, hn⟩) hres

/-- The cyclotomic character is a closed embedding `Gal(K_cyc/K) → ℤ_p^×`. -/
theorem isClosedEmbedding_cyclotomicExtensionCharacter :
    Topology.IsClosedEmbedding (cyclotomicExtensionCharacter (K := K) p) :=
  (continuous_cyclotomicExtensionCharacter p).isClosedEmbedding
    (cyclotomicExtensionCharacter_injective p)

variable (π : K)

/-- `K_cyc ⊆ K_FT`. -/
theorem cyclotomicExtension_le_falseTateExtension :
    cyclotomicExtension (K := K) p ≤ falseTateExtension p π := by
  rw [falseTateExtension_eq_sup]
  exact le_sup_right

/-- Restriction `Gal(K_FT/K) → Gal(K_cyc/K)`. -/
def cyclotomicRestriction :
    (falseTateExtension p π ≃ₐ[K] falseTateExtension p π) →*
      (cyclotomicExtension (K := K) p ≃ₐ[K] cyclotomicExtension (K := K) p) :=
  IntermediateField.restrictNormalHomOfLE (cyclotomicExtension_le_falseTateExtension p π)

/-- `g|_{K_cyc}(x) = g(x)` for `x ∈ K_cyc ⊆ K_FT`. -/
theorem cyclotomicRestriction_commutes
    (g : falseTateExtension p π ≃ₐ[K] falseTateExtension p π)
    (x : cyclotomicExtension (K := K) p) :
    IntermediateField.inclusion (cyclotomicExtension_le_falseTateExtension p π)
        (cyclotomicRestriction p π g x) =
      g (IntermediateField.inclusion (cyclotomicExtension_le_falseTateExtension p π) x) :=
  IntermediateField.restrictNormalHomOfLE_commutes _ g x

/-- Restriction `Gal(K_FT/K) → Gal(K_cyc/K)` is surjective. -/
theorem cyclotomicRestriction_surjective [hπ : NeZero π] :
    Function.Surjective (cyclotomicRestriction p π) :=
  IntermediateField.restrictNormalHomOfLE_surjective _

/-- The cyclotomic character of `Gal(K_FT/K)` is the cyclotomic character of `Gal(K_cyc/K)`
composed with restriction. -/
theorem padicCyclotomicCharacter_eq_comp :
    padicCyclotomicCharacter p π =
      (cyclotomicExtensionCharacter p).comp (cyclotomicRestriction p π) := by
  apply MonoidHom.ext
  intro g
  apply Units.ext
  apply PadicInt.ext_of_toZModPow.mp
  intro n
  have : NeZero (p ^ n) := ⟨pow_ne_zero n (Fact.out : p.Prime).ne_zero⟩
  let i := IntermediateField.inclusion (cyclotomicExtension_le_falseTateExtension p π)
  have hi : i (zetaCycExt p n) = zetaExt p π n := rfl
  have hpow : zetaExt p π n ^
      (PadicInt.toZModPow n (padicCyclotomicCharacter p π g : ℤ_[p])).val =
      zetaExt p π n ^
        (PadicInt.toZModPow n
          (cyclotomicExtensionCharacter p (cyclotomicRestriction p π g) : ℤ_[p])).val := by
    calc
      _ = g (zetaExt p π n) :=
        (_root_.cyclotomicCharacter.spec p g.toRingEquiv (zetaExt p π n)
          (isPrimitiveRoot_zetaExt p π n).pow_eq_one).symm
      _ = i (cyclotomicRestriction p π g (zetaCycExt p n)) := by
        rw [cyclotomicRestriction_commutes, hi]
      _ = _ := by rw [cyclotomicExtensionCharacter_spec, map_pow, hi]
  have hv := (isPrimitiveRoot_zetaExt p π n).pow_inj
    (ZMod.val_lt _) (ZMod.val_lt _) hpow
  simpa only [ZMod.natCast_zmod_val, MonoidHom.comp_apply] using
    congrArg (fun k : ℕ ↦ (k : ZMod (p ^ n))) hv

/-- Restriction `Gal(K_FT/K) → Gal(K_cyc/K)` is continuous. -/
theorem continuous_cyclotomicRestriction : Continuous (cyclotomicRestriction p π) := by
  apply (isClosedEmbedding_cyclotomicExtensionCharacter (K := K) p).isEmbedding.continuous_iff.mpr
  change Continuous ((cyclotomicExtensionCharacter p).comp (cyclotomicRestriction p π))
  rw [← padicCyclotomicCharacter_eq_comp]
  exact continuous_padicCyclotomicCharacter p π

/-- `ker χ = Gal(K_FT/K_cyc)`: the kernel of the cyclotomic character of `Gal(K_FT/K)` is
the kernel of restriction to `K_cyc`. -/
theorem padicCyclotomicCharacter_ker :
    (padicCyclotomicCharacter p π).ker = (cyclotomicRestriction p π).ker := by
  ext g
  rw [MonoidHom.mem_ker, MonoidHom.mem_ker, padicCyclotomicCharacter_eq_comp,
    MonoidHom.comp_apply, ← map_one (cyclotomicExtensionCharacter (K := K) p)]
  exact (cyclotomicExtensionCharacter_injective p).eq_iff

/-- The cyclotomic characters of `Gal(K_FT/K)` and of `Gal(K_cyc/K)` have the same image in
`ℤ_p^×`. -/
theorem padicCyclotomicCharacter_range [hπ : NeZero π] :
    (padicCyclotomicCharacter p π).range =
      (cyclotomicExtensionCharacter (K := K) p).range := by
  ext u
  constructor
  · rintro ⟨g, rfl⟩
    exact ⟨cyclotomicRestriction p π g,
      (congrArg (fun f ↦ f g) (padicCyclotomicCharacter_eq_comp p π)).symm⟩
  · rintro ⟨g, rfl⟩
    obtain ⟨h, rfl⟩ := cyclotomicRestriction_surjective p π g
    exact ⟨h, congrArg (fun f ↦ f h) (padicCyclotomicCharacter_eq_comp p π)⟩

/-- The isomorphism of topological groups `Gal(K_cyc/K) ≅ χ(Gal(K_FT/K)) ⊆ ℤ_p^×` induced by
the cyclotomic character. -/
def cyclotomicImageEquiv [hπ : NeZero π] :
    (cyclotomicExtension (K := K) p ≃ₐ[K] cyclotomicExtension (K := K) p) ≃ₜ*
      (padicCyclotomicCharacter p π).range := by
  let f : (cyclotomicExtension (K := K) p ≃ₐ[K] cyclotomicExtension (K := K) p) →*
      (padicCyclotomicCharacter p π).range :=
    { toFun := fun g ↦ ⟨cyclotomicExtensionCharacter p g, by
        rw [padicCyclotomicCharacter_range p π]
        exact ⟨g, rfl⟩⟩
      map_one' := Subtype.ext (map_one (cyclotomicExtensionCharacter (K := K) p))
      map_mul' := fun g h ↦ Subtype.ext (map_mul (cyclotomicExtensionCharacter p) g h) }
  have hf : Function.Bijective f := by
    constructor
    · intro g h heq
      exact cyclotomicExtensionCharacter_injective p (congrArg Subtype.val heq)
    · intro u
      have hu : u.val ∈ (cyclotomicExtensionCharacter (K := K) p).range := by
        rw [← padicCyclotomicCharacter_range p π]
        exact u.property
      obtain ⟨g, hg⟩ := hu
      exact ⟨g, Subtype.ext hg⟩
  let e := MulEquiv.ofBijective f hf
  have hc : Continuous e := (continuous_cyclotomicExtensionCharacter (K := K) p).subtype_mk _
  exact
    { e with
      continuous_toFun := hc
      continuous_invFun := hc.continuous_symm_of_equiv_compact_to_t2 }

/-- `cyclotomicImageEquiv` sends `g ∈ Gal(K_cyc/K)` to its cyclotomic character. -/
theorem cyclotomicImageEquiv_apply [hπ : NeZero π]
    (g : cyclotomicExtension (K := K) p ≃ₐ[K] cyclotomicExtension (K := K) p) :
    (cyclotomicImageEquiv p π g : (ℤ_[p])ˣ) = cyclotomicExtensionCharacter p g := rfl

/-- `cyclotomicImageEquiv` sends `g|_{K_cyc}` to `χ(g)` for `g ∈ Gal(K_FT/K)`. -/
theorem cyclotomicImageEquiv_restrict [hπ : NeZero π]
    (g : falseTateExtension p π ≃ₐ[K] falseTateExtension p π) :
    (cyclotomicImageEquiv p π (cyclotomicRestriction p π g) : (ℤ_[p])ˣ) =
      padicCyclotomicCharacter p π g := by
  rw [cyclotomicImageEquiv_apply, padicCyclotomicCharacter_eq_comp, MonoidHom.comp_apply]

end

end FalseTateExtension
