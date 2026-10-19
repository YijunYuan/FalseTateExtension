/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import Mathlib.RingTheory.PowerBasis
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

/-!
# Eigenvectors of an automorphism scaling a power basis generator

Let `B` be a power basis of `E/F` of dimension `d` and `σ` an `F`-automorphism with
`σ B.gen = ζ • B.gen` for a primitive `d`-th root of unity `ζ ∈ F`. Then the eigenvectors of `σ`
are, up to scalars, the powers `B.gen ^ i`, `i < d`.

Upstream candidate: `Mathlib.RingTheory.PowerBasis`.
-/

@[expose] public section

namespace PowerBasis

/-- A nonzero eigenvector of an automorphism scaling the generator of a power basis by a
primitive root of unity is a scalar multiple of a power of the generator. -/
theorem eigenvector_eq_smul_pow {F E : Type*} [Field F] [Field E] [Algebra F E]
    (B : PowerBasis F E) (σ : E ≃ₐ[F] E) {ζ μ : F}
    (hζ : IsPrimitiveRoot ζ B.dim) (hgen : σ B.gen = ζ • B.gen)
    {x : E} (hx : x ≠ 0) (heigen : σ x = μ • x) :
    ∃ i : Fin B.dim, ∃ a : F, x = a • B.gen ^ (i : ℕ) := by
  classical
  have hb (j : Fin B.dim) : σ (B.basis j) = ζ ^ (j : ℕ) • B.basis j := by
    simp only [B.basis_eq_pow, map_pow, hgen, smul_pow]
  have hcoord (i : Fin B.dim) : (B.basis.coord i).comp σ.toLinearMap =
      ζ ^ (i : ℕ) • B.basis.coord i := by
    apply B.basis.ext
    intro j
    change B.basis.coord i (σ (B.basis j)) = ζ ^ (i : ℕ) * B.basis.coord i (B.basis j)
    rw [hb, map_smul]
    simp only [Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply,
      smul_eq_mul]
    by_cases hj : j = i
    · subst j
      simp only [ite_true]
    · simp only [hj, ite_false, mul_zero]
  have hc (i : Fin B.dim) : (ζ ^ (i : ℕ) - μ) * B.basis.repr x i = 0 := by
    have hi := congrArg (fun f : E →ₗ[F] F ↦ f x) (hcoord i)
    change B.basis.repr (σ x) i = ζ ^ (i : ℕ) * B.basis.repr x i at hi
    rw [heigen, map_smul] at hi
    change μ * B.basis.repr x i = ζ ^ (i : ℕ) * B.basis.repr x i at hi
    linear_combination -hi
  have hsome : ∃ i : Fin B.dim, B.basis.repr x i ≠ 0 := by
    by_contra! h
    apply hx
    apply B.basis.repr.injective
    ext i
    simp [h]
  obtain ⟨i, hi⟩ := hsome
  have hμ : ζ ^ (i : ℕ) = μ :=
    sub_eq_zero.mp ((mul_eq_zero.mp (hc i)).resolve_right hi)
  have hz (j : Fin B.dim) (hj : j ≠ i) : B.basis.repr x j = 0 := by
    apply (mul_eq_zero.mp (hc j)).resolve_left
    intro heq
    apply hj
    exact Fin.ext (hζ.pow_inj j.isLt i.isLt ((sub_eq_zero.mp heq).trans hμ.symm))
  refine ⟨i, B.basis.repr x i, ?_⟩
  rw [← B.basis_eq_pow i]
  apply B.basis.repr.injective
  ext j
  simp only [map_smul, Finsupp.smul_apply, Module.Basis.repr_self, Finsupp.single_apply,
    smul_eq_mul]
  by_cases hj : j = i
  · subst j
    simp only [ite_true, mul_one]
  · simp only [Ne.symm hj, ite_false, mul_zero, hz j hj]

end PowerBasis
