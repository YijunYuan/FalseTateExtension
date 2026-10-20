/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FalseTateExtension.Layers.Galois

/-!
# Coordinates on the Galois group of a diagonal layer

Let `K` be a field of characteristic zero, `p` a prime, `π ∈ K` nonzero, and
`L_n = K(π^{1/p^n}, ζ_{p^n})` the diagonal layer. An automorphism `g ∈ Gal(L_n/K)` is
determined by two coordinates: its cyclotomic character `χ_n(g) ∈ (ℤ/p^n)ˣ`, defined by
`g(ζ_{p^n}) = ζ_{p^n}^{χ_n(g)}`, and its Kummer exponent `b_n(g) ∈ ℤ/p^n`, defined by
`g(π^{1/p^n}) = ζ_{p^n}^{b_n(g)} π^{1/p^n}`. The character is a homomorphism and the exponent
satisfies the cocycle rule `b_n(gh) = b_n(g) + χ_n(g) b_n(h)`.

## Main results

* `finiteCyclotomicCharacter`, `finiteCyclotomicCharacter_spec`: the character `χ_n` and its
  defining identity.
* `finiteKummerExponent`, `finiteKummerExponent_spec`: the exponent `b_n` and its defining
  identity.
* `finiteKummerExponent_mul`: the cocycle rule `b_n(gh) = b_n(g) + χ_n(g) b_n(h)`.
* `finiteLayer_aut_ext`: an automorphism is determined by its values on `π^{1/p^n}` and
  `ζ_{p^n}`.
* `finiteCoordinates_injective`: `g ↦ (b_n(g), χ_n(g))` is injective.

## References

* Liu, *On lattices in semi-stable representations: a proof of a conjecture of Breuil*, §5.1.
-/

@[expose] public section

namespace FalseTateExtension

noncomputable section

variable {K : Type*} [Field K] [CharZero K] (p : ℕ) [Fact p.Prime] (π : K) (n : ℕ)

/-- `π^{1/p^n}` as an element of `K(π^{1/p^n}, ζ_{p^n})`. -/
def pPowRootLayer : falseTateLayer p π n n :=
  ⟨pPowRoot p π n, pPowRoot_mem_falseTateLayer p π n n⟩

/-- `ζ_{p^n}` as an element of `K(π^{1/p^n}, ζ_{p^n})`. -/
def zetaLayer : falseTateLayer p π n n :=
  ⟨zeta p n, zeta_mem_falseTateLayer p π n n⟩

/-- `pPowRootLayer p π n` is `π^{1/p^n}` in the algebraic closure. -/
@[simp]
theorem coe_pPowRootLayer : (pPowRootLayer p π n : AlgebraicClosure K) = pPowRoot p π n := rfl

/-- `zetaLayer p π n` is `ζ_{p^n}` in the algebraic closure. -/
@[simp]
theorem coe_zetaLayer :
    (zetaLayer p π n : AlgebraicClosure K) = zeta p n := rfl

/-- `ζ_{p^n}` is a primitive `p^n`-th root of unity in `K(π^{1/p^n}, ζ_{p^n})`. -/
theorem isPrimitiveRoot_zetaLayer :
    IsPrimitiveRoot (zetaLayer p π n) (p ^ n) := by
  exact (isPrimitiveRoot_zeta (K := K) p n).of_map_of_injective
    (f := (falseTateLayer p π n n).val) (falseTateLayer p π n n).val.injective

/-- `(π^{1/p^n})^{p^n} = π` in `K(π^{1/p^n}, ζ_{p^n})`. -/
theorem pPowRootLayer_pow :
    pPowRootLayer p π n ^ (p ^ n) = algebraMap K (falseTateLayer p π n n) π := by
  apply Subtype.ext
  exact pPowRoot_pow p π n

/-- `π^{1/p^n} ≠ 0` in `K(π^{1/p^n}, ζ_{p^n})` when `π ≠ 0`. -/
theorem pPowRootLayer_ne_zero [hπ : NeZero π] : pPowRootLayer p π n ≠ 0 := by
  intro h
  exact pPowRoot_ne_zero p π n (congrArg Subtype.val h)

/-- The cyclotomic character `χ_n : Gal(K(π^{1/p^n}, ζ_{p^n})/K) → (ℤ/p^n)ˣ`, given by
`g(ζ_{p^n}) = ζ_{p^n}^{χ_n(g)}`. -/
def finiteCyclotomicCharacter :
    (falseTateLayer p π n n ≃ₐ[K] falseTateLayer p π n n) →* (ZMod (p ^ n))ˣ := by
  have : NeZero (p ^ n) := ⟨pow_ne_zero n (Fact.out : p.Prime).ne_zero⟩
  exact (isPrimitiveRoot_zetaLayer p π n).autToPow K

/-- `g(ζ_{p^n}) = ζ_{p^n}^{χ_n(g)}`. -/
theorem finiteCyclotomicCharacter_spec
    (g : falseTateLayer p π n n ≃ₐ[K] falseTateLayer p π n n) :
    g (zetaLayer p π n) = zetaLayer p π n ^
      (finiteCyclotomicCharacter p π n g : ZMod (p ^ n)).val := by
  have : NeZero (p ^ n) := ⟨pow_ne_zero n (Fact.out : p.Prime).ne_zero⟩
  exact ((isPrimitiveRoot_zetaLayer p π n).autToPow_spec K g).symm

/-- `ζ_{p^n}` as a unit of `K(π^{1/p^n}, ζ_{p^n})`. -/
def layerRootUnit : (falseTateLayer p π n n)ˣ :=
  Units.mk0 (zetaLayer p π n)
    ((isPrimitiveRoot_zetaLayer p π n).ne_zero
      (pow_ne_zero n (Fact.out : p.Prime).ne_zero))

/-- The unit `layerRootUnit p π n` is `ζ_{p^n}`. -/
@[simp]
theorem coe_layerRootUnit :
    (layerRootUnit p π n : falseTateLayer p π n n) = zetaLayer p π n := rfl

/-- `ζ_{p^n}` is a primitive `p^n`-th root of unity in the unit group of the diagonal layer. -/
theorem isPrimitiveRoot_layerRootUnit : IsPrimitiveRoot (layerRootUnit p π n) (p ^ n) :=
  IsPrimitiveRoot.coe_units_iff.mp (isPrimitiveRoot_zetaLayer p π n)

/-- The unit `g(π^{1/p^n}) / π^{1/p^n}` of `K(π^{1/p^n}, ζ_{p^n})`, a `p^n`-th root of unity. -/
def kummerRatio [hπ : NeZero π]
    (g : falseTateLayer p π n n ≃ₐ[K] falseTateLayer p π n n) :
    (falseTateLayer p π n n)ˣ :=
  Units.map g.toMonoidHom (Units.mk0 (pPowRootLayer p π n) (pPowRootLayer_ne_zero p π n)) /
    Units.mk0 (pPowRootLayer p π n) (pPowRootLayer_ne_zero p π n)

/-- `kummerRatio p π n g` is `g(π^{1/p^n}) / π^{1/p^n}`. -/
@[simp]
theorem coe_kummerRatio [hπ : NeZero π]
    (g : falseTateLayer p π n n ≃ₐ[K] falseTateLayer p π n n) :
    (kummerRatio p π n g : falseTateLayer p π n n) =
      g (pPowRootLayer p π n) / pPowRootLayer p π n := rfl

/-- `(g(π^{1/p^n}) / π^{1/p^n})^{p^n} = 1`. -/
theorem kummerRatio_pow [hπ : NeZero π]
    (g : falseTateLayer p π n n ≃ₐ[K] falseTateLayer p π n n) :
    kummerRatio p π n g ^ (p ^ n) = 1 := by
  apply Units.ext
  change (g (pPowRootLayer p π n) / pPowRootLayer p π n) ^ (p ^ n) = 1
  rw [div_pow, ← map_pow, pPowRootLayer_pow, g.commutes]
  apply div_self
  rw [← pPowRootLayer_pow p π n]
  exact pow_ne_zero _ (pPowRootLayer_ne_zero p π n)

/-- `g(π^{1/p^n}) / π^{1/p^n}` is a power of `ζ_{p^n}`. -/
theorem kummerRatio_mem_zpowers [hπ : NeZero π]
    (g : falseTateLayer p π n n ≃ₐ[K] falseTateLayer p π n n) :
    kummerRatio p π n g ∈ Subgroup.zpowers (layerRootUnit p π n) := by
  have : NeZero (p ^ n) := ⟨pow_ne_zero n (Fact.out : p.Prime).ne_zero⟩
  rw [(isPrimitiveRoot_layerRootUnit p π n).zpowers_eq, mem_rootsOfUnity]
  exact kummerRatio_pow p π n g

/-- The Kummer exponent `b_n(g) ∈ ℤ/p^n` of `g ∈ Gal(K(π^{1/p^n}, ζ_{p^n})/K)`, given by
`g(π^{1/p^n}) = ζ_{p^n}^{b_n(g)} π^{1/p^n}`. -/
def finiteKummerExponent [hπ : NeZero π]
    (g : falseTateLayer p π n n ≃ₐ[K] falseTateLayer p π n n) : ZMod (p ^ n) :=
  (isPrimitiveRoot_layerRootUnit p π n).zmodEquivZPowers.symm
    (Additive.ofMul ⟨kummerRatio p π n g, kummerRatio_mem_zpowers p π n g⟩)

/-- The isomorphism `ℤ/p^n ≃ ⟨ζ_{p^n}⟩` sends `a` to `ζ_{p^n}^a`. -/
theorem zmodEquivZPowers_val (a : ZMod (p ^ n)) :
    (((isPrimitiveRoot_layerRootUnit p π n).zmodEquivZPowers a).toMul :
      (falseTateLayer p π n n)ˣ) = layerRootUnit p π n ^ a.val := by
  have : NeZero (p ^ n) := ⟨pow_ne_zero n (Fact.out : p.Prime).ne_zero⟩
  have h := (isPrimitiveRoot_layerRootUnit p π n).zmodEquivZPowers_apply_coe_nat a.val
  rw [ZMod.natCast_zmod_val] at h
  exact congrArg (fun z : Additive (Subgroup.zpowers (layerRootUnit p π n)) ↦
    (z.toMul : (falseTateLayer p π n n)ˣ)) h

/-- `g(π^{1/p^n}) = ζ_{p^n}^{b_n(g)} π^{1/p^n}`. -/
theorem finiteKummerExponent_spec [hπ : NeZero π]
    (g : falseTateLayer p π n n ≃ₐ[K] falseTateLayer p π n n) :
    g (pPowRootLayer p π n) = zetaLayer p π n ^
      (finiteKummerExponent p π n g).val * pPowRootLayer p π n := by
  have h := congrArg
    (fun z : Additive (Subgroup.zpowers (layerRootUnit p π n)) ↦
      (z.toMul : (falseTateLayer p π n n)ˣ))
    ((isPrimitiveRoot_layerRootUnit p π n).zmodEquivZPowers.apply_symm_apply
      (Additive.ofMul ⟨kummerRatio p π n g, kummerRatio_mem_zpowers p π n g⟩))
  rw [zmodEquivZPowers_val] at h
  have hf := congrArg Units.val h
  simp only [Units.val_pow_eq_pow_val] at hf
  change zetaLayer p π n ^ (finiteKummerExponent p π n g).val =
    g (pPowRootLayer p π n) / pPowRootLayer p π n at hf
  have hm := congrArg (· * pPowRootLayer p π n) hf
  rw [div_mul_cancel₀ _ (pPowRootLayer_ne_zero p π n)] at hm
  exact hm.symm

/-- `a ↦ ζ_{p^n}^a` is injective on `ℤ/p^n`. -/
theorem zetaLayer_pow_injective :
    Function.Injective (fun a : ZMod (p ^ n) ↦ zetaLayer p π n ^ a.val) := by
  have : NeZero (p ^ n) := ⟨pow_ne_zero n (Fact.out : p.Prime).ne_zero⟩
  intro a b hab
  have hv := (isPrimitiveRoot_zetaLayer p π n).pow_inj
    (ZMod.val_lt a) (ZMod.val_lt b) hab
  simpa only [ZMod.natCast_zmod_val] using congrArg (fun i : ℕ ↦ (i : ZMod (p ^ n))) hv

/-- If `g(π^{1/p^n}) = ζ_{p^n}^a π^{1/p^n}` then `b_n(g) = a`. -/
theorem finiteKummerExponent_unique [hπ : NeZero π]
    (g : falseTateLayer p π n n ≃ₐ[K] falseTateLayer p π n n)
    (a : ZMod (p ^ n))
    (ha : g (pPowRootLayer p π n) = zetaLayer p π n ^ a.val * pPowRootLayer p π n) :
    finiteKummerExponent p π n g = a := by
  apply zetaLayer_pow_injective p π n
  have h := (finiteKummerExponent_spec p π n g).symm.trans ha
  have hd := congrArg (· / pPowRootLayer p π n) h
  simpa only [mul_div_cancel_right₀ _ (pPowRootLayer_ne_zero p π n)] using hd

/-- If `g(ζ_{p^n}) = ζ_{p^n}^a` then `χ_n(g) = a`. -/
theorem finiteCyclotomicCharacter_unique
    (g : falseTateLayer p π n n ≃ₐ[K] falseTateLayer p π n n)
    (a : (ZMod (p ^ n))ˣ)
    (ha : g (zetaLayer p π n) = zetaLayer p π n ^ (a : ZMod (p ^ n)).val) :
    finiteCyclotomicCharacter p π n g = a := by
  apply Units.ext
  exact zetaLayer_pow_injective p π n
    ((finiteCyclotomicCharacter_spec p π n g).symm.trans ha)

/-- The cocycle rule `b_n(gh) = b_n(g) + χ_n(g) b_n(h)`. -/
theorem finiteKummerExponent_mul [hπ : NeZero π]
    (g h : falseTateLayer p π n n ≃ₐ[K] falseTateLayer p π n n) :
    finiteKummerExponent p π n (g * h) = finiteKummerExponent p π n g +
      (finiteCyclotomicCharacter p π n g : ZMod (p ^ n)) *
        finiteKummerExponent p π n h := by
  have : NeZero (p ^ n) := ⟨pow_ne_zero n (Fact.out : p.Prime).ne_zero⟩
  have heval : (g * h) (pPowRootLayer p π n) =
      zetaLayer p π n ^
        ((finiteCyclotomicCharacter p π n g : ZMod (p ^ n)).val *
          (finiteKummerExponent p π n h).val + (finiteKummerExponent p π n g).val) *
        pPowRootLayer p π n := by
    change g (h (pPowRootLayer p π n)) = _
    rw [finiteKummerExponent_spec p π n h, map_mul, map_pow,
      finiteCyclotomicCharacter_spec p π n g, finiteKummerExponent_spec p π n g,
      ← pow_mul, ← mul_assoc, ← pow_add]
  have hpow := congrArg (· / pPowRootLayer p π n)
    ((finiteKummerExponent_spec p π n (g * h)).symm.trans heval)
  simp only [mul_div_cancel_right₀ _ (pPowRootLayer_ne_zero p π n)] at hpow
  have hu : layerRootUnit p π n ^ (finiteKummerExponent p π n (g * h)).val =
      layerRootUnit p π n ^
        ((finiteCyclotomicCharacter p π n g : ZMod (p ^ n)).val *
          (finiteKummerExponent p π n h).val + (finiteKummerExponent p π n g).val) := by
    apply Units.ext
    simpa only [Units.val_pow_eq_pow_val, coe_layerRootUnit] using hpow
  have hm := pow_eq_pow_iff_modEq.mp hu
  rw [← (isPrimitiveRoot_layerRootUnit p π n).eq_orderOf] at hm
  have hz : ((finiteKummerExponent p π n (g * h)).val : ZMod (p ^ n)) =
      (((finiteCyclotomicCharacter p π n g : ZMod (p ^ n)).val *
        (finiteKummerExponent p π n h).val + (finiteKummerExponent p π n g).val : ℕ) :
          ZMod (p ^ n)) := (ZMod.natCast_eq_natCast_iff ..).mpr hm
  simpa only [Nat.cast_add, Nat.cast_mul, ZMod.natCast_zmod_val, add_comm] using hz

/-- Two automorphisms of `K(π^{1/p^n}, ζ_{p^n})` agreeing on `π^{1/p^n}` and `ζ_{p^n}` are
equal. -/
theorem finiteLayer_aut_ext
    {g h : falseTateLayer p π n n ≃ₐ[K] falseTateLayer p π n n}
    (hα : g (pPowRootLayer p π n) = h (pPowRootLayer p π n))
    (hζ : g (zetaLayer p π n) = h (zetaLayer p π n)) : g = h := by
  have hE : falseTateLayer p π n n =
      IntermediateField.adjoin K {pPowRoot p π n, zeta p n} := by
    unfold falseTateLayer radicalLayer cyclotomicLayer
    rw [← IntermediateField.adjoin_union, Set.singleton_union]
  apply AlgEquiv.coe_toAlgHom_injective
  apply IntermediateField.algHom_ext_of_eq_adjoin (F := K) hE
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl
  · exact hα
  · exact hζ

/-- The coordinates `g ↦ (b_n(g), χ_n(g)) ∈ ℤ/p^n × (ℤ/p^n)ˣ` of `g ∈ Gal(L_n/K)`. -/
abbrev finiteCoordinates [hπ : NeZero π]
    (g : falseTateLayer p π n n ≃ₐ[K] falseTateLayer p π n n) :
    ZMod (p ^ n) × (ZMod (p ^ n))ˣ :=
  (finiteKummerExponent p π n g, finiteCyclotomicCharacter p π n g)

/-- `g ↦ (b_n(g), χ_n(g))` is injective on `Gal(K(π^{1/p^n}, ζ_{p^n})/K)`. -/
theorem finiteCoordinates_injective [hπ : NeZero π] :
    Function.Injective (finiteCoordinates p π n) := by
  intro g h hgh
  have hb := congrArg Prod.fst hgh
  have hχ := congrArg Prod.snd hgh
  change finiteKummerExponent p π n g = finiteKummerExponent p π n h at hb
  change finiteCyclotomicCharacter p π n g = finiteCyclotomicCharacter p π n h at hχ
  apply finiteLayer_aut_ext p π n
  · rw [finiteKummerExponent_spec p π n g, finiteKummerExponent_spec p π n h, hb]
  · rw [finiteCyclotomicCharacter_spec p π n g, finiteCyclotomicCharacter_spec p π n h, hχ]

end

end FalseTateExtension
