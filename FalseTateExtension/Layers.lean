/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FalseTateExtension.CompatibleRoots
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic

/-!
# Finite layers and infinite false Tate extensions

The compatible systems supplied by `CompatibleRoots` are chosen in the
canonical algebraic closure. Adjoining their terms gives the finite Kummer,
cyclotomic, and false Tate layers. Their directed suprema are the corresponding
infinite extensions; the false Tate extension is the compositum of the other
two extensions.

This implements blueprint `ft:extensions`, following Liu, Section 5.1
(printed page 82). No degree, ramification, or Galois assertion is made here.
-/

@[expose] public section

namespace FalseTateExtension

noncomputable section

variable {K : Type*} [Field K] (p : ℕ) [Fact p.Prime]

/-- A chosen compatible system of radicals in the canonical algebraic closure. -/
def radical (π : K) : ℕ → AlgebraicClosure K :=
  Classical.choose (exists_compatible_radicals p (algebraMap K (AlgebraicClosure K) π))

@[simp]
theorem radical_zero (π : K) : radical p π 0 = algebraMap K (AlgebraicClosure K) π :=
  (Classical.choose_spec
    (exists_compatible_radicals p (algebraMap K (AlgebraicClosure K) π))).1

/-- Successive chosen radicals satisfy the defining pth-power relation. -/
theorem radical_succ_pow (π : K) (n : ℕ) : radical p π (n + 1) ^ p = radical p π n :=
  (Classical.choose_spec
    (exists_compatible_radicals p (algebraMap K (AlgebraicClosure K) π))).2.1 n

/-- The nth chosen radical is a p^n-th root of the original element. -/
theorem radical_pow (π : K) (n : ℕ) :
    radical p π n ^ (p ^ n) = algebraMap K (AlgebraicClosure K) π :=
  (Classical.choose_spec
    (exists_compatible_radicals p (algebraMap K (AlgebraicClosure K) π))).2.2 n

/-- The nth finite Kummer layer, including the base field at index zero. -/
def radicalLayer (π : K) (n : ℕ) : IntermediateField K (AlgebraicClosure K) :=
  IntermediateField.adjoin K {radical p π n}

theorem radical_mem_radicalLayer (π : K) (n : ℕ) : radical p π n ∈ radicalLayer p π n :=
  IntermediateField.subset_adjoin K _ (Set.mem_singleton _)

@[simp]
theorem radicalLayer_zero (π : K) : radicalLayer p π 0 = ⊥ := by
  apply IntermediateField.adjoin_simple_eq_bot_iff.mpr
  rw [radical_zero]
  exact IntermediateField.algebraMap_mem _ π

theorem radicalLayer_le_succ (π : K) (n : ℕ) :
    radicalLayer p π n ≤ radicalLayer p π (n + 1) := by
  apply IntermediateField.adjoin_simple_le_iff.mpr
  rw [← radical_succ_pow p π n]
  exact (radicalLayer p π (n + 1)).toSubalgebra.pow_mem
    (radical_mem_radicalLayer p π (n + 1)) p

/-- The actual finite Kummer layers form an increasing sequence. -/
theorem radicalLayer_mono (π : K) : Monotone (radicalLayer p π) :=
  monotone_nat_of_le_succ (radicalLayer_le_succ p π)

instance radicalLayer_finiteDimensional (π : K) (n : ℕ) :
    FiniteDimensional K (radicalLayer p π n) :=
  inferInstanceAs (FiniteDimensional K (IntermediateField.adjoin K {radical p π n}))

/-- The infinite Kummer extension as an intermediate field of the fixed closure. -/
def kummerExtension (π : K) : IntermediateField K (AlgebraicClosure K) :=
  ⨆ n, radicalLayer p π n

theorem radicalLayer_le_kummerExtension (π : K) (n : ℕ) :
    radicalLayer p π n ≤ kummerExtension p π := le_iSup _ n

/-- Omitting the zeroth Kummer layer leaves the same infinite extension. -/
theorem kummerExtension_eq_iSup_succ (π : K) :
    kummerExtension p π = ⨆ n, radicalLayer p π (n + 1) := by
  apply le_antisymm
  · exact iSup_le fun n ↦ (radicalLayer_le_succ p π n).trans
      (le_iSup (fun n ↦ radicalLayer p π (n + 1)) n)
  · exact iSup_le fun n ↦ radicalLayer_le_kummerExtension p π (n + 1)

/-- The supremum defining the Kummer extension is its ordinary directed union. -/
theorem mem_kummerExtension_iff (π : K) (x : AlgebraicClosure K) :
    x ∈ kummerExtension p π ↔ ∃ n, x ∈ radicalLayer p π n := by
  change x ∈ ((⨆ n, radicalLayer p π n : IntermediateField K (AlgebraicClosure K)) :
    Set (AlgebraicClosure K)) ↔ _
  rw [IntermediateField.coe_iSup_of_directed (radicalLayer_mono p π).directed_le,
    Set.mem_iUnion]
  rfl

variable [CharZero K]

/-- A chosen compatible system of primitive p-power roots of unity in the
canonical algebraic closure. -/
def rootOfUnity : ℕ → AlgebraicClosure K :=
  Classical.choose (exists_compatible_primitive_roots (Ω := AlgebraicClosure K) p)

@[simp]
theorem rootOfUnity_zero : rootOfUnity (K := K) p 0 = 1 :=
  (Classical.choose_spec
    (exists_compatible_primitive_roots (Ω := AlgebraicClosure K) p)).1

theorem rootOfUnity_succ_pow (n : ℕ) :
    rootOfUnity (K := K) p (n + 1) ^ p = rootOfUnity p n :=
  (Classical.choose_spec
    (exists_compatible_primitive_roots (Ω := AlgebraicClosure K) p)).2.1 n

theorem isPrimitiveRoot_rootOfUnity (n : ℕ) :
    IsPrimitiveRoot (rootOfUnity (K := K) p n) (p ^ n) :=
  (Classical.choose_spec
    (exists_compatible_primitive_roots (Ω := AlgebraicClosure K) p)).2.2 n

theorem rootOfUnity_pow (n : ℕ) : rootOfUnity (K := K) p n ^ (p ^ n) = 1 :=
  (isPrimitiveRoot_rootOfUnity (K := K) p n).pow_eq_one

/-- The nth cyclotomic layer generated by the chosen primitive root. -/
def cyclotomicLayer (n : ℕ) : IntermediateField K (AlgebraicClosure K) :=
  IntermediateField.adjoin K {rootOfUnity (K := K) p n}

theorem rootOfUnity_mem_cyclotomicLayer (n : ℕ) :
    rootOfUnity (K := K) p n ∈ cyclotomicLayer p n :=
  IntermediateField.subset_adjoin K _ (Set.mem_singleton _)

@[simp]
theorem cyclotomicLayer_zero : cyclotomicLayer (K := K) p 0 = ⊥ := by
  simp [cyclotomicLayer]

theorem cyclotomicLayer_le_succ (n : ℕ) :
    cyclotomicLayer (K := K) p n ≤ cyclotomicLayer p (n + 1) := by
  apply IntermediateField.adjoin_simple_le_iff.mpr
  rw [← rootOfUnity_succ_pow (K := K) p n]
  exact (cyclotomicLayer (K := K) p (n + 1)).toSubalgebra.pow_mem
    (rootOfUnity_mem_cyclotomicLayer p (n + 1)) p

theorem cyclotomicLayer_mono : Monotone (cyclotomicLayer (K := K) p) :=
  monotone_nat_of_le_succ (cyclotomicLayer_le_succ p)

instance cyclotomicLayer_finiteDimensional (n : ℕ) :
    FiniteDimensional K (cyclotomicLayer (K := K) p n) :=
  inferInstanceAs (FiniteDimensional K (IntermediateField.adjoin K {rootOfUnity (K := K) p n}))

/-- The infinite cyclotomic extension inside the canonical algebraic closure. -/
def cyclotomicExtension : IntermediateField K (AlgebraicClosure K) :=
  ⨆ n, cyclotomicLayer p n

theorem cyclotomicLayer_le_cyclotomicExtension (n : ℕ) :
    cyclotomicLayer (K := K) p n ≤ cyclotomicExtension p := le_iSup _ n

theorem cyclotomicExtension_eq_iSup_succ :
    cyclotomicExtension (K := K) p = ⨆ n, cyclotomicLayer p (n + 1) := by
  apply le_antisymm
  · exact iSup_le fun n ↦ (cyclotomicLayer_le_succ p n).trans
      (le_iSup (fun n ↦ cyclotomicLayer (K := K) p (n + 1)) n)
  · exact iSup_le fun n ↦ cyclotomicLayer_le_cyclotomicExtension p (n + 1)

/-- The cyclotomic extension is the ordinary union of its finite layers. -/
theorem mem_cyclotomicExtension_iff (x : AlgebraicClosure K) :
    x ∈ cyclotomicExtension p ↔ ∃ n, x ∈ cyclotomicLayer p n := by
  change x ∈ ((⨆ n, cyclotomicLayer p n : IntermediateField K (AlgebraicClosure K)) :
    Set (AlgebraicClosure K)) ↔ _
  rw [IntermediateField.coe_iSup_of_directed (cyclotomicLayer_mono p).directed_le,
    Set.mem_iUnion]
  rfl

/-- The finite false Tate layer generated by a radical and a primitive root
of unity, expressed as their actual intermediate-field compositum. -/
def falseTateLayer (π : K) (m n : ℕ) : IntermediateField K (AlgebraicClosure K) :=
  radicalLayer p π m ⊔ cyclotomicLayer p n

@[simp]
theorem falseTateLayer_zero_zero (π : K) : falseTateLayer p π 0 0 = ⊥ := by
  simp [falseTateLayer]

theorem radical_mem_falseTateLayer (π : K) (m n : ℕ) :
    radical p π m ∈ falseTateLayer p π m n :=
  (le_sup_left : radicalLayer p π m ≤ falseTateLayer p π m n)
    (radical_mem_radicalLayer p π m)

theorem rootOfUnity_mem_falseTateLayer (π : K) (m n : ℕ) :
    rootOfUnity p n ∈ falseTateLayer p π m n :=
  (le_sup_right : cyclotomicLayer p n ≤ falseTateLayer p π m n)
    (rootOfUnity_mem_cyclotomicLayer p n)

/-- Finite false Tate layers are monotone in both indices. -/
theorem falseTateLayer_mono (π : K) {m m' n n' : ℕ} (hm : m ≤ m') (hn : n ≤ n') :
    falseTateLayer p π m n ≤ falseTateLayer p π m' n' :=
  sup_le_sup (radicalLayer_mono p π hm) (cyclotomicLayer_mono p hn)

theorem falseTateLayer_directed (π : K) :
    Directed (· ≤ ·) (fun i : ℕ × ℕ ↦ falseTateLayer p π i.1 i.2) := by
  intro i j
  exact ⟨(max i.1 j.1, max i.2 j.2),
    falseTateLayer_mono p π (le_max_left _ _) (le_max_left _ _),
    falseTateLayer_mono p π (le_max_right _ _) (le_max_right _ _)⟩

/-- The diagonal is cofinal in the two-index family of finite layers. -/
theorem falseTateLayer_le_diagonal (π : K) (m n : ℕ) :
    falseTateLayer p π m n ≤ falseTateLayer p π (max m n) (max m n) :=
  falseTateLayer_mono p π (le_max_left _ _) (le_max_right _ _)

instance falseTateLayer_finiteDimensional (π : K) (m n : ℕ) :
    FiniteDimensional K (falseTateLayer p π m n) :=
  inferInstanceAs (FiniteDimensional K (radicalLayer p π m ⊔ cyclotomicLayer p n :
    IntermediateField K (AlgebraicClosure K)))

/-- The infinite false Tate extension as the supremum of its finite layers. -/
def falseTateExtension (π : K) : IntermediateField K (AlgebraicClosure K) :=
  ⨆ m, ⨆ n, falseTateLayer p π m n

/-- The diagonal layer `K(π^{1/p^n}, ζ_{p^n})`. -/
abbrev falseTateDiagonalLayer (π : K) (n : ℕ) : IntermediateField K (AlgebraicClosure K) :=
  falseTateLayer p π n n

/-- The Galois group of `K_FT/K`, with its Krull topology. -/
abbrev FalseTateGaloisGroup (π : K) : Type _ :=
  falseTateExtension p π ≃ₐ[K] falseTateExtension p π

theorem falseTateLayer_le_falseTateExtension (π : K) (m n : ℕ) :
    falseTateLayer p π m n ≤ falseTateExtension p π :=
  (le_iSup (fun n ↦ falseTateLayer p π m n) n).trans
    (le_iSup (fun m ↦ ⨆ n, falseTateLayer p π m n) m)

/-- The infinite extension is already exhausted by diagonal finite layers. -/
theorem falseTateExtension_eq_iSup_diagonal (π : K) :
    falseTateExtension p π = ⨆ n, falseTateLayer p π n n := by
  apply le_antisymm
  · exact iSup_le fun m ↦ iSup_le fun n ↦
      (falseTateLayer_le_diagonal p π m n).trans
        (le_iSup (fun n ↦ falseTateLayer p π n n) (max m n))
  · exact iSup_le fun n ↦ falseTateLayer_le_falseTateExtension p π n n

/-- Every element of the false Tate extension lies in one diagonal finite layer. -/
theorem mem_falseTateExtension_iff_diagonal (π : K) (x : AlgebraicClosure K) :
    x ∈ falseTateExtension p π ↔ ∃ n, x ∈ falseTateLayer p π n n := by
  rw [falseTateExtension_eq_iSup_diagonal]
  change x ∈ ((⨆ n, falseTateLayer p π n n : IntermediateField K (AlgebraicClosure K)) :
    Set (AlgebraicClosure K)) ↔ _
  have hm : Monotone (fun n ↦ falseTateLayer p π n n) :=
    fun _ _ h ↦ falseTateLayer_mono p π h h
  rw [IntermediateField.coe_iSup_of_directed hm.directed_le, Set.mem_iUnion]
  rfl

/-- The two-index finite layers exhaust the actual infinite intermediate field. -/
theorem mem_falseTateExtension_iff (π : K) (x : AlgebraicClosure K) :
    x ∈ falseTateExtension p π ↔ ∃ m n, x ∈ falseTateLayer p π m n := by
  constructor
  · intro hx
    obtain ⟨n, hn⟩ := (mem_falseTateExtension_iff_diagonal p π x).mp hx
    exact ⟨n, n, hn⟩
  · rintro ⟨m, n, hx⟩
    exact falseTateLayer_le_falseTateExtension p π m n hx

/-- Restricting both indices to positive integers leaves the same infinite field. -/
theorem falseTateExtension_eq_iSup_succ (π : K) :
    falseTateExtension p π = ⨆ m, ⨆ n, falseTateLayer p π (m + 1) (n + 1) := by
  apply le_antisymm
  · refine iSup_le fun m ↦ iSup_le fun n ↦ ?_
    exact (falseTateLayer_mono p π (Nat.le_succ m) (Nat.le_succ n)).trans
      ((le_iSup (fun n ↦ falseTateLayer p π (m + 1) (n + 1)) n).trans
        (le_iSup (fun m ↦ ⨆ n, falseTateLayer p π (m + 1) (n + 1)) m))
  · exact iSup_le fun m ↦ iSup_le fun n ↦
      falseTateLayer_le_falseTateExtension p π (m + 1) (n + 1)

/-- The ordinary union can equivalently be taken over strictly positive indices. -/
theorem mem_falseTateExtension_iff_pos (π : K) (x : AlgebraicClosure K) :
    x ∈ falseTateExtension p π ↔
      ∃ m n, 0 < m ∧ 0 < n ∧ x ∈ falseTateLayer p π m n := by
  constructor
  · intro hx
    obtain ⟨m, n, hmn⟩ := (mem_falseTateExtension_iff p π x).mp hx
    exact ⟨m + 1, n + 1, Nat.succ_pos m, Nat.succ_pos n,
      falseTateLayer_mono p π (Nat.le_succ m) (Nat.le_succ n) hmn⟩
  · rintro ⟨m, n, _, _, hx⟩
    exact falseTateLayer_le_falseTateExtension p π m n hx

/-- The false Tate extension is the compositum of the actual infinite Kummer
and cyclotomic intermediate fields. -/
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
