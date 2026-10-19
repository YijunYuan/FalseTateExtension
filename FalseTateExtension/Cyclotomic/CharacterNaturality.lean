/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FalseTateExtension.Cyclotomic.InfiniteCharacter
public import FalseTateExtension.Mathlib.NumberTheory.Cyclotomic.CharacterNaturality
public import FalseTateExtension.Mathlib.FieldTheory.Galois.RestrictScalars
public import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

/-!
# The image of the cyclotomic character over a finite extension of `ℚ_[p]`

The cyclotomic character `Gal(Ω/ℚ_[p]) → ℤ_[p]ˣ` of any algebraic closure `Ω` of `ℚ_[p]` is
surjective. For a field `K` of characteristic zero, the cyclotomic character of `K(ζ_{p^∞})/K`
is the restriction of the cyclotomic character of `Gal(K̄/K)`. When `K/ℚ_[p]` is finite, the
image of `χ : Gal(K(ζ_{p^∞})/K) → ℤ_[p]ˣ` is the image of the subgroup `Gal(K̄/K)` of
`Gal(K̄/ℚ_[p])`; it is an open subgroup of `ℤ_[p]ˣ` of finite index dividing `[K : ℚ_[p]]`.

## Main results

* `cyclotomicCharacter_surjective_of_isAlgClosure`: the cyclotomic character of `Gal(Ω/ℚ_[p])`
  is surjective for every algebraic closure `Ω` of `ℚ_[p]`
* `cyclotomicCharacter_restrict_cyclotomicExtension`: the character of `K(ζ_{p^∞})/K` is the
  restriction of the character of `K̄/K`
* `cyclotomicExtensionCharacter_finiteIndex`, `cyclotomicExtensionCharacter_index_dvd`: for
  `K/ℚ_[p]` finite, the image of `χ` has finite index dividing `[K : ℚ_[p]]`
* `isOpen_cyclotomicExtensionCharacter_range`: the image of `χ` is open in `ℤ_[p]ˣ`

## References

* Liu, *On lattices in semi-stable representations*, §5.1.
-/

@[expose] public section

noncomputable section

namespace FalseTateExtension

variable (p : ℕ) [Fact p.Prime]

/-- The cyclotomic character `Gal(ℚ̄_p/ℚ_[p]) → ℤ_[p]ˣ` of `AlgebraicClosure ℚ_[p]` is
surjective. -/
theorem cyclotomicCharacter_algebraicClosure_padic_surjective :
    Function.Surjective ((_root_.cyclotomicCharacter (AlgebraicClosure (ℚ_[p])) p).comp
      (MulSemiringAction.toRingAut
        (AlgebraicClosure (ℚ_[p]) ≃ₐ[ℚ_[p]] AlgebraicClosure (ℚ_[p]))
        (AlgebraicClosure (ℚ_[p])))) := by
  intro u
  obtain ⟨g, hg⟩ := cyclotomicExtensionCharacter_surjective_padic p u
  obtain ⟨h, rfl⟩ := AlgEquiv.restrictNormalHom_surjective (AlgebraicClosure (ℚ_[p])) g
  refine ⟨h, ?_⟩
  change _root_.cyclotomicCharacter (AlgebraicClosure (ℚ_[p])) p h.toRingEquiv = u
  have hc := cyclotomicCharacter_eq_of_intertwines p
    (algebraMap (cyclotomicExtension (K := ℚ_[p]) p) (AlgebraicClosure (ℚ_[p])))
    (h.restrictNormal (cyclotomicExtension (K := ℚ_[p]) p)).toRingEquiv h.toRingEquiv
    (AlgEquiv.restrictNormal_commutes h (cyclotomicExtension (K := ℚ_[p]) p))
  exact hc.symm.trans hg

/-- For every algebraic closure `Ω` of `ℚ_[p]`, the cyclotomic character `Gal(Ω/ℚ_[p]) → ℤ_[p]ˣ`
is surjective. -/
theorem cyclotomicCharacter_surjective_of_isAlgClosure
    (Ω : Type*) [Field Ω] [Algebra (ℚ_[p]) Ω] [IsAlgClosure (ℚ_[p]) Ω] :
    Function.Surjective ((_root_.cyclotomicCharacter Ω p).comp
      (MulSemiringAction.toRingAut (Ω ≃ₐ[ℚ_[p]] Ω) Ω)) := by
  let e := IsAlgClosure.equiv (ℚ_[p]) (AlgebraicClosure (ℚ_[p])) Ω
  let : IsAlgClosed Ω := IsAlgClosure.isAlgClosed (ℚ_[p])
  let : CharZero Ω := charZero_of_injective_algebraMap (algebraMap (ℚ_[p]) Ω).injective
  have : NeZero (p : Ω) := ⟨Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero⟩
  intro u
  obtain ⟨g, hg⟩ := cyclotomicCharacter_algebraicClosure_padic_surjective p u
  refine ⟨e.autCongr g, ?_⟩
  change _root_.cyclotomicCharacter Ω p (e.autCongr g).toRingEquiv = u
  have hc := cyclotomicCharacter_eq_of_intertwines p e.toRingHom g.toRingEquiv
    (e.autCongr g).toRingEquiv (fun x ↦ by simp)
  exact hc.symm.trans hg

variable {K : Type*} [Field K] [CharZero K]

/-- For `g ∈ Gal(K̄/K)`, the cyclotomic character of `K(ζ_{p^∞})/K` at the restriction of `g`
to `K(ζ_{p^∞})` equals the cyclotomic character of `K̄` at `g`. -/
theorem cyclotomicCharacter_restrict_cyclotomicExtension
    (g : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) :
    cyclotomicExtensionCharacter p (g.restrictNormal (cyclotomicExtension (K := K) p)) =
      _root_.cyclotomicCharacter (AlgebraicClosure K) p g.toRingEquiv := by
  have : NeZero (p : K) := ⟨Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero⟩
  exact cyclotomicCharacter_eq_of_intertwines p
    (algebraMap (cyclotomicExtension (K := K) p) (AlgebraicClosure K))
    (g.restrictNormal (cyclotomicExtension (K := K) p)).toRingEquiv g.toRingEquiv
    (AlgEquiv.restrictNormal_commutes g (cyclotomicExtension (K := K) p))

variable [Algebra (ℚ_[p]) K]

/-- For `K/ℚ_[p]`, the image of the cyclotomic character of `Gal(K(ζ_{p^∞})/K)` is the image of
the subgroup `Gal(K̄/K) ≤ Gal(K̄/ℚ_[p])` under the cyclotomic character of `K̄`. -/
theorem cyclotomicExtensionCharacter_range_eq_map :
    (cyclotomicExtensionCharacter (K := K) p).range =
      (AlgEquiv.restrictScalarsHom (ℚ_[p]) (S := K) (A := AlgebraicClosure K)).range.map
        ((_root_.cyclotomicCharacter (AlgebraicClosure K) p).comp
          (MulSemiringAction.toRingAut
            (AlgebraicClosure K ≃ₐ[ℚ_[p]] AlgebraicClosure K) (AlgebraicClosure K))) := by
  ext u
  constructor
  · rintro ⟨g, rfl⟩
    obtain ⟨h, rfl⟩ := AlgEquiv.restrictNormalHom_surjective (AlgebraicClosure K) g
    refine ⟨h.restrictScalars (ℚ_[p]), ⟨h, rfl⟩, ?_⟩
    exact (cyclotomicCharacter_restrict_cyclotomicExtension p h).symm
  · rintro ⟨g, ⟨h, rfl⟩, rfl⟩
    exact ⟨h.restrictNormal (cyclotomicExtension (K := K) p),
      cyclotomicCharacter_restrict_cyclotomicExtension p h⟩

variable [FiniteDimensional (ℚ_[p]) K]

/-- For `K/ℚ_[p]` finite, the image of the cyclotomic character `Gal(K(ζ_{p^∞})/K) → ℤ_[p]ˣ`
has finite index. -/
instance cyclotomicExtensionCharacter_finiteIndex :
    (cyclotomicExtensionCharacter (K := K) p).range.FiniteIndex := by
  let S := (AlgEquiv.restrictScalarsHom (ℚ_[p]) (S := K) (A := AlgebraicClosure K)).range
  have hS : S.index = Module.finrank (ℚ_[p]) K :=
    AlgEquiv.index_range_restrictScalarsHom (ℚ_[p]) K (AlgebraicClosure K)
  let : S.FiniteIndex := ⟨by rw [hS]; exact Module.finrank_pos.ne'⟩
  rw [cyclotomicExtensionCharacter_range_eq_map]
  exact Subgroup.FiniteIndex.map_of_surjective S
    (cyclotomicCharacter_surjective_of_isAlgClosure p (AlgebraicClosure K))

/-- For `K/ℚ_[p]` finite, the index of the image of the cyclotomic character
`Gal(K(ζ_{p^∞})/K) → ℤ_[p]ˣ` divides `[K : ℚ_[p]]`. -/
theorem cyclotomicExtensionCharacter_index_dvd :
    (cyclotomicExtensionCharacter (K := K) p).range.index ∣ Module.finrank (ℚ_[p]) K := by
  rw [cyclotomicExtensionCharacter_range_eq_map]
  have h :=
    (AlgEquiv.restrictScalarsHom (ℚ_[p]) (S := K) (A := AlgebraicClosure K)).range.index_map_dvd
    (cyclotomicCharacter_surjective_of_isAlgClosure p (AlgebraicClosure K))
  simpa only [AlgEquiv.index_range_restrictScalarsHom] using h

/-- For `K/ℚ_[p]` finite, the index of the image of the cyclotomic character of
`Gal(K(ζ_{p^∞})/K)` is positive. -/
theorem cyclotomicExtensionCharacter_index_pos :
    0 < (cyclotomicExtensionCharacter (K := K) p).range.index :=
  Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite

/-- For `K/ℚ_[p]` finite, the image of the cyclotomic character `Gal(K(ζ_{p^∞})/K) → ℤ_[p]ˣ`
is an open subgroup of `ℤ_[p]ˣ`. -/
theorem isOpen_cyclotomicExtensionCharacter_range :
    IsOpen ((cyclotomicExtensionCharacter (K := K) p).range : Set (ℤ_[p])ˣ) :=
  Subgroup.isOpen_of_isClosed_of_finiteIndex _
    (isClosedEmbedding_cyclotomicExtensionCharacter (K := K) p).isClosed_range

end FalseTateExtension

end
