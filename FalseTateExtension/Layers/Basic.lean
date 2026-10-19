/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FalseTateExtension.Layers.CompatibleRoots
public import FalseTateExtension.Mathlib.FieldTheory.IntermediateField.Supremum

/-!
# Finite layers of the false Tate extension

Let `K` be a field and `p` a prime. For `π ∈ K`, `pPowRoot p π n = π^{1/p^n}` is a compatible
system of `p`-power roots of `π` in the algebraic closure of `K`, and, when `K` has
characteristic zero, `zeta p n = ζ_{p^n}` is a compatible system of primitive `p`-power
roots of unity. The finite layers are `radicalLayer p π n = K(π^{1/p^n})`,
`cyclotomicLayer p n = K(ζ_{p^n})` and `falseTateLayer p π m n = K(π^{1/p^m}, ζ_{p^n})`; the
infinite extensions `kummerExtension p π = K(π^{1/p^∞})`, `cyclotomicExtension p = K(ζ_{p^∞})`
and `falseTateExtension p π = K_FT` are their unions. `K_FT` is the compositum of the Kummer
and cyclotomic extensions and is the union of the diagonal layers
`falseTateDiagonalLayer p π n = K(π^{1/p^n}, ζ_{p^n})`.

## Main results

* `pPowRoot_pow`, `isPrimitiveRoot_zeta`: the defining properties of the two systems.
* `radicalLayer_mono`, `cyclotomicLayer_mono`, `falseTateLayer_mono`: the layers increase.
* `mem_kummerExtension_iff`, `mem_cyclotomicExtension_iff`, `mem_falseTateExtension_iff`:
  the infinite extensions are the unions of their finite layers.
* `falseTateExtension_eq_iSup_diagonal`: `K_FT = ⋃_n K(π^{1/p^n}, ζ_{p^n})`.
* `falseTateExtension_eq_sup`: `K_FT = K(π^{1/p^∞}) K(ζ_{p^∞})`.
* `FalseTateGaloisGroup`: the Galois group `Gal(K_FT/K)`.

## References

* Liu, *On lattices in semi-stable representations: a proof of a conjecture of Breuil*, §5.1.
-/

@[expose] public section

namespace FalseTateExtension

noncomputable section

variable {K : Type*} [Field K] (p : ℕ) [Fact p.Prime]

/-- A compatible system `π^{1/p^n}` of `p`-power roots of `π` in the algebraic closure of
`K`: `pPowRoot p π 0 = π` and `pPowRoot p π (n + 1) ^ p = pPowRoot p π n`. -/
def pPowRoot (π : K) : ℕ → AlgebraicClosure K :=
  Classical.choose (exists_compatible_radicals p (algebraMap K (AlgebraicClosure K) π))

/-- The zeroth radical is `π` itself. -/
@[simp]
theorem pPowRoot_zero (π : K) : pPowRoot p π 0 = algebraMap K (AlgebraicClosure K) π :=
  (Classical.choose_spec
    (exists_compatible_radicals p (algebraMap K (AlgebraicClosure K) π))).1

/-- `(π^{1/p^{n+1}})^p = π^{1/p^n}`. -/
theorem pPowRoot_succ_pow (π : K) (n : ℕ) : pPowRoot p π (n + 1) ^ p = pPowRoot p π n :=
  (Classical.choose_spec
    (exists_compatible_radicals p (algebraMap K (AlgebraicClosure K) π))).2.1 n

/-- `(π^{1/p^n})^{p^n} = π`. -/
theorem pPowRoot_pow (π : K) (n : ℕ) :
    pPowRoot p π n ^ (p ^ n) = algebraMap K (AlgebraicClosure K) π :=
  (Classical.choose_spec
    (exists_compatible_radicals p (algebraMap K (AlgebraicClosure K) π))).2.2 n

/-- The Kummer layer `K(π^{1/p^n})`. -/
def radicalLayer (π : K) (n : ℕ) : IntermediateField K (AlgebraicClosure K) :=
  IntermediateField.adjoin K {pPowRoot p π n}

/-- `π^{1/p^n} ∈ K(π^{1/p^n})`. -/
theorem pPowRoot_mem_radicalLayer (π : K) (n : ℕ) : pPowRoot p π n ∈ radicalLayer p π n :=
  IntermediateField.subset_adjoin K _ (Set.mem_singleton _)

/-- The zeroth Kummer layer is `K`. -/
@[simp]
theorem radicalLayer_zero (π : K) : radicalLayer p π 0 = ⊥ := by
  apply IntermediateField.adjoin_simple_eq_bot_iff.mpr
  rw [pPowRoot_zero]
  exact IntermediateField.algebraMap_mem _ π

/-- `K(π^{1/p^n}) ⊆ K(π^{1/p^{n+1}})`. -/
theorem radicalLayer_le_succ (π : K) (n : ℕ) :
    radicalLayer p π n ≤ radicalLayer p π (n + 1) := by
  apply IntermediateField.adjoin_simple_le_iff.mpr
  rw [← pPowRoot_succ_pow p π n]
  exact (radicalLayer p π (n + 1)).toSubalgebra.pow_mem
    (pPowRoot_mem_radicalLayer p π (n + 1)) p

/-- The Kummer layers `K(π^{1/p^n})` increase with `n`. -/
theorem radicalLayer_mono (π : K) : Monotone (radicalLayer p π) :=
  monotone_nat_of_le_succ (radicalLayer_le_succ p π)

/-- `K(π^{1/p^n})/K` is finite. -/
instance radicalLayer_finiteDimensional (π : K) (n : ℕ) :
    FiniteDimensional K (radicalLayer p π n) :=
  inferInstanceAs (FiniteDimensional K (IntermediateField.adjoin K {pPowRoot p π n}))

/-- The Kummer extension `K(π^{1/p^∞}) = ⋃_n K(π^{1/p^n})`. -/
def kummerExtension (π : K) : IntermediateField K (AlgebraicClosure K) :=
  ⨆ n, radicalLayer p π n

/-- `K(π^{1/p^n}) ⊆ K(π^{1/p^∞})`. -/
theorem radicalLayer_le_kummerExtension (π : K) (n : ℕ) :
    radicalLayer p π n ≤ kummerExtension p π := le_iSup _ n

/-- An element lies in `K(π^{1/p^∞})` if and only if it lies in some `K(π^{1/p^n})`. -/
theorem mem_kummerExtension_iff (π : K) (x : AlgebraicClosure K) :
    x ∈ kummerExtension p π ↔ ∃ n, x ∈ radicalLayer p π n :=
  IntermediateField.mem_iSup_of_monotone (radicalLayer_mono p π)

variable [CharZero K]

/-- A compatible system `ζ_{p^n}` of primitive `p^n`-th roots of unity in the algebraic
closure of `K`: `zeta p 0 = 1` and `zeta p (n + 1) ^ p = zeta p n`. -/
def zeta : ℕ → AlgebraicClosure K :=
  Classical.choose (exists_compatible_primitive_roots (Ω := AlgebraicClosure K) p)

/-- `ζ_{p^0} = 1`. -/
@[simp]
theorem zeta_zero : zeta (K := K) p 0 = 1 :=
  (Classical.choose_spec
    (exists_compatible_primitive_roots (Ω := AlgebraicClosure K) p)).1

/-- `ζ_{p^{n+1}}^p = ζ_{p^n}`. -/
theorem zeta_succ_pow (n : ℕ) :
    zeta (K := K) p (n + 1) ^ p = zeta p n :=
  (Classical.choose_spec
    (exists_compatible_primitive_roots (Ω := AlgebraicClosure K) p)).2.1 n

/-- `ζ_{p^n}` is a primitive `p^n`-th root of unity. -/
theorem isPrimitiveRoot_zeta (n : ℕ) :
    IsPrimitiveRoot (zeta (K := K) p n) (p ^ n) :=
  (Classical.choose_spec
    (exists_compatible_primitive_roots (Ω := AlgebraicClosure K) p)).2.2 n

/-- `ζ_{p^n}^{p^n} = 1`. -/
theorem zeta_pow_eq_one (n : ℕ) : zeta (K := K) p n ^ (p ^ n) = 1 :=
  (isPrimitiveRoot_zeta (K := K) p n).pow_eq_one

/-- The cyclotomic layer `K(ζ_{p^n})`. -/
def cyclotomicLayer (n : ℕ) : IntermediateField K (AlgebraicClosure K) :=
  IntermediateField.adjoin K {zeta (K := K) p n}

/-- `ζ_{p^n} ∈ K(ζ_{p^n})`. -/
theorem zeta_mem_cyclotomicLayer (n : ℕ) :
    zeta (K := K) p n ∈ cyclotomicLayer p n :=
  IntermediateField.subset_adjoin K _ (Set.mem_singleton _)

/-- The zeroth cyclotomic layer is `K`. -/
@[simp]
theorem cyclotomicLayer_zero : cyclotomicLayer (K := K) p 0 = ⊥ := by
  simp [cyclotomicLayer]

/-- `K(ζ_{p^n}) ⊆ K(ζ_{p^{n+1}})`. -/
theorem cyclotomicLayer_le_succ (n : ℕ) :
    cyclotomicLayer (K := K) p n ≤ cyclotomicLayer p (n + 1) := by
  apply IntermediateField.adjoin_simple_le_iff.mpr
  rw [← zeta_succ_pow (K := K) p n]
  exact (cyclotomicLayer (K := K) p (n + 1)).toSubalgebra.pow_mem
    (zeta_mem_cyclotomicLayer p (n + 1)) p

/-- The cyclotomic layers `K(ζ_{p^n})` increase with `n`. -/
theorem cyclotomicLayer_mono : Monotone (cyclotomicLayer (K := K) p) :=
  monotone_nat_of_le_succ (cyclotomicLayer_le_succ p)

/-- `K(ζ_{p^n})/K` is finite. -/
instance cyclotomicLayer_finiteDimensional (n : ℕ) :
    FiniteDimensional K (cyclotomicLayer (K := K) p n) :=
  inferInstanceAs (FiniteDimensional K (IntermediateField.adjoin K {zeta (K := K) p n}))

/-- The cyclotomic extension `K(ζ_{p^∞}) = ⋃_n K(ζ_{p^n})`. -/
def cyclotomicExtension : IntermediateField K (AlgebraicClosure K) :=
  ⨆ n, cyclotomicLayer p n

/-- `K(ζ_{p^n}) ⊆ K(ζ_{p^∞})`. -/
theorem cyclotomicLayer_le_cyclotomicExtension (n : ℕ) :
    cyclotomicLayer (K := K) p n ≤ cyclotomicExtension p := le_iSup _ n

/-- An element lies in `K(ζ_{p^∞})` if and only if it lies in some `K(ζ_{p^n})`. -/
theorem mem_cyclotomicExtension_iff (x : AlgebraicClosure K) :
    x ∈ cyclotomicExtension p ↔ ∃ n, x ∈ cyclotomicLayer p n :=
  IntermediateField.mem_iSup_of_monotone (cyclotomicLayer_mono p)

/-- The false Tate layer `K(π^{1/p^m}, ζ_{p^n}) = K(π^{1/p^m}) K(ζ_{p^n})`. -/
def falseTateLayer (π : K) (m n : ℕ) : IntermediateField K (AlgebraicClosure K) :=
  radicalLayer p π m ⊔ cyclotomicLayer p n

/-- The layer `K(π^{1/p^0}, ζ_{p^0})` is `K`. -/
@[simp]
theorem falseTateLayer_zero_zero (π : K) : falseTateLayer p π 0 0 = ⊥ := by
  simp [falseTateLayer]

/-- `π^{1/p^m} ∈ K(π^{1/p^m}, ζ_{p^n})`. -/
theorem pPowRoot_mem_falseTateLayer (π : K) (m n : ℕ) :
    pPowRoot p π m ∈ falseTateLayer p π m n :=
  (le_sup_left : radicalLayer p π m ≤ falseTateLayer p π m n)
    (pPowRoot_mem_radicalLayer p π m)

/-- `ζ_{p^n} ∈ K(π^{1/p^m}, ζ_{p^n})`. -/
theorem zeta_mem_falseTateLayer (π : K) (m n : ℕ) :
    zeta p n ∈ falseTateLayer p π m n :=
  (le_sup_right : cyclotomicLayer p n ≤ falseTateLayer p π m n)
    (zeta_mem_cyclotomicLayer p n)

/-- `K(π^{1/p^m}, ζ_{p^n}) ⊆ K(π^{1/p^{m'}}, ζ_{p^{n'}})` when `m ≤ m'` and `n ≤ n'`. -/
theorem falseTateLayer_mono (π : K) {m m' n n' : ℕ} (hm : m ≤ m') (hn : n ≤ n') :
    falseTateLayer p π m n ≤ falseTateLayer p π m' n' :=
  sup_le_sup (radicalLayer_mono p π hm) (cyclotomicLayer_mono p hn)

/-- The family of layers `K(π^{1/p^m}, ζ_{p^n})` is directed. -/
theorem falseTateLayer_directed (π : K) :
    Directed (· ≤ ·) (fun i : ℕ × ℕ ↦ falseTateLayer p π i.1 i.2) := by
  intro i j
  exact ⟨(max i.1 j.1, max i.2 j.2),
    falseTateLayer_mono p π (le_max_left _ _) (le_max_left _ _),
    falseTateLayer_mono p π (le_max_right _ _) (le_max_right _ _)⟩

/-- `K(π^{1/p^m}, ζ_{p^n}) ⊆ K(π^{1/p^N}, ζ_{p^N})` with `N = max m n`. -/
theorem falseTateLayer_le_diagonal (π : K) (m n : ℕ) :
    falseTateLayer p π m n ≤ falseTateLayer p π (max m n) (max m n) :=
  falseTateLayer_mono p π (le_max_left _ _) (le_max_right _ _)

/-- `K(π^{1/p^m}, ζ_{p^n})/K` is finite. -/
instance falseTateLayer_finiteDimensional (π : K) (m n : ℕ) :
    FiniteDimensional K (falseTateLayer p π m n) :=
  inferInstanceAs (FiniteDimensional K (radicalLayer p π m ⊔ cyclotomicLayer p n :
    IntermediateField K (AlgebraicClosure K)))

/-- The false Tate extension `K_FT = K(π^{1/p^∞}, ζ_{p^∞}) = ⋃_{m,n} K(π^{1/p^m}, ζ_{p^n})`. -/
def falseTateExtension (π : K) : IntermediateField K (AlgebraicClosure K) :=
  ⨆ m, ⨆ n, falseTateLayer p π m n

/-- The diagonal layer `K(π^{1/p^n}, ζ_{p^n})`. -/
abbrev falseTateDiagonalLayer (π : K) (n : ℕ) : IntermediateField K (AlgebraicClosure K) :=
  falseTateLayer p π n n

/-- The Galois group `Gal(K_FT/K)` with its Krull topology. -/
abbrev FalseTateGaloisGroup (π : K) : Type _ :=
  falseTateExtension p π ≃ₐ[K] falseTateExtension p π

/-- `K(π^{1/p^m}, ζ_{p^n}) ⊆ K_FT`. -/
theorem falseTateLayer_le_falseTateExtension (π : K) (m n : ℕ) :
    falseTateLayer p π m n ≤ falseTateExtension p π :=
  (le_iSup (fun n ↦ falseTateLayer p π m n) n).trans
    (le_iSup (fun m ↦ ⨆ n, falseTateLayer p π m n) m)

/-- `K_FT = ⋃_n K(π^{1/p^n}, ζ_{p^n})`. -/
theorem falseTateExtension_eq_iSup_diagonal (π : K) :
    falseTateExtension p π = ⨆ n, falseTateLayer p π n n := by
  apply le_antisymm
  · exact iSup_le fun m ↦ iSup_le fun n ↦
      (falseTateLayer_le_diagonal p π m n).trans
        (le_iSup (fun n ↦ falseTateLayer p π n n) (max m n))
  · exact iSup_le fun n ↦ falseTateLayer_le_falseTateExtension p π n n

/-- An element lies in `K_FT` if and only if it lies in some diagonal layer
`K(π^{1/p^n}, ζ_{p^n})`. -/
theorem mem_falseTateExtension_iff_diagonal (π : K) (x : AlgebraicClosure K) :
    x ∈ falseTateExtension p π ↔ ∃ n, x ∈ falseTateLayer p π n n := by
  rw [falseTateExtension_eq_iSup_diagonal]
  exact IntermediateField.mem_iSup_of_monotone (fun _ _ h ↦ falseTateLayer_mono p π h h)

/-- An element lies in `K_FT` if and only if it lies in some layer `K(π^{1/p^m}, ζ_{p^n})`. -/
theorem mem_falseTateExtension_iff (π : K) (x : AlgebraicClosure K) :
    x ∈ falseTateExtension p π ↔ ∃ m n, x ∈ falseTateLayer p π m n := by
  constructor
  · intro hx
    obtain ⟨n, hn⟩ := (mem_falseTateExtension_iff_diagonal p π x).mp hx
    exact ⟨n, n, hn⟩
  · rintro ⟨m, n, hx⟩
    exact falseTateLayer_le_falseTateExtension p π m n hx

/-- `K_FT = K(π^{1/p^∞}) K(ζ_{p^∞})`. -/
theorem falseTateExtension_eq_sup (π : K) :
    falseTateExtension p π = kummerExtension p π ⊔ cyclotomicExtension p := by
  apply le_antisymm
  · exact iSup_le fun m ↦ iSup_le fun n ↦
      sup_le_sup (radicalLayer_le_kummerExtension p π m)
        (cyclotomicLayer_le_cyclotomicExtension p n)
  · apply sup_le
    · exact iSup_le fun m ↦
        (le_sup_left : radicalLayer p π m ≤ falseTateLayer p π m 0).trans
          (falseTateLayer_le_falseTateExtension p π m 0)
    · exact iSup_le fun n ↦
        (le_sup_right : cyclotomicLayer p n ≤ falseTateLayer p π 0 n).trans
          (falseTateLayer_le_falseTateExtension p π 0 n)

end

end FalseTateExtension
