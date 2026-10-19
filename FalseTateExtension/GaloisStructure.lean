/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FalseTateExtension.StrictAPF
public import FalseTateExtension.AffineKernel
public import Mathlib.FieldTheory.Galois.Abelian
public import Mathlib.FieldTheory.LinearDisjoint
public import Mathlib.RingTheory.ZMod.UnitsCyclic
public import FalseTateExtension.Mathlib.FieldTheory.Galois.InfiniteCorrespondence
public import FalseTateExtension.Mathlib.RingTheory.PowerBasis.Eigenvector

/-!
# Odd-prime false Tate Galois structure

At an odd prime the actual finite cyclotomic groups are cyclic and the first
Eisenstein radical is not cyclotomic. These facts force the full translation
kernel. The original fields then give the intersection theorem, the actual
topological semidirect product with the original cyclotomic character image,
and the prescribed topological generator of the relative cyclotomic Galois group.
All relative scalar actions are the original inclusions.
-/

@[expose] public section

noncomputable section

namespace FalseTateExtension

open Polynomial
open FontaineWintenberger

section FiniteCyclotomic

variable {K : Type*} [Field K] [CharZero K] (p : ℕ) [Fact p.Prime]

/-- The actual cyclotomic layer over the original base is abelian Galois. -/
theorem cyclotomicLayer_isAbelianGalois (n : ℕ) :
    IsAbelianGalois K (cyclotomicLayer (K := K) p n) := by
  have : NeZero (p ^ n) := ⟨pow_ne_zero n (Fact.out : p.Prime).ne_zero⟩
  have : IsCyclotomicExtension {p ^ n} K (cyclotomicLayer (K := K) p n) :=
    (isPrimitiveRoot_rootOfUnity (K := K) p n).intermediateField_adjoin_isCyclotomicExtension K
  exact IsCyclotomicExtension.isAbelianGalois {p ^ n} K _

/-- At an odd prime, the actual finite cyclotomic Galois group over any
characteristic-zero base is cyclic, including level zero. -/
theorem cyclotomicLayer_isCyclic [hp₂ : Fact (p ≠ 2)] (n : ℕ) :
    IsCyclic (cyclotomicLayer (K := K) p n ≃ₐ[K] cyclotomicLayer (K := K) p n) := by
  have : NeZero (p ^ n) := ⟨pow_ne_zero n (Fact.out : p.Prime).ne_zero⟩
  have : IsCyclotomicExtension {p ^ n} K (cyclotomicLayer (K := K) p n) :=
    (isPrimitiveRoot_rootOfUnity (K := K) p n).intermediateField_adjoin_isCyclotomicExtension K
  let ζ : cyclotomicLayer (K := K) p n :=
    ⟨rootOfUnity p n, rootOfUnity_mem_cyclotomicLayer p n⟩
  have hζ : IsPrimitiveRoot ζ (p ^ n) :=
    (isPrimitiveRoot_rootOfUnity (K := K) p n).of_map_of_injective
      (f := (cyclotomicLayer (K := K) p n).val) (cyclotomicLayer p n).val.injective
  let := ZMod.isCyclic_units_of_prime_pow p (Fact.out : p.Prime) hp₂.out n
  exact isCyclic_of_injective (hζ.autToPow K) (hζ.autToPow_injective K)

/-- If the preceding cyclotomic layer and the first roots of unity are
already in the base, a genuinely new next root has its literal degree-`p`
binomial minimal polynomial over the original base. -/
theorem cyclotomicLayer_step_minpoly_of_eq_bot (n : ℕ)
    (h₁ : cyclotomicLayer (K := K) p 1 = ⊥)
    (hprev : cyclotomicLayer (K := K) p n = ⊥)
    (hnext : cyclotomicLayer (K := K) p (n + 1) ≠ ⊥) :
    ∃ a : K, algebraMap K (AlgebraicClosure K) a = rootOfUnity p n ∧
      minpoly K (rootOfUnity (K := K) p (n + 1)) = Polynomial.X ^ p - Polynomial.C a := by
  have hprevMem : rootOfUnity (K := K) p n ∈ (⊥ : IntermediateField K (AlgebraicClosure K)) := by
    rw [← hprev]
    exact rootOfUnity_mem_cyclotomicLayer p n
  obtain ⟨a, ha⟩ := hprevMem
  change algebraMap K (AlgebraicClosure K) a = rootOfUnity p n at ha
  have ha₀ : a ≠ 0 := by
    intro h
    have hz := rootOfUnity_pow (K := K) p n
    rw [← ha, h, map_zero, zero_pow (pow_ne_zero n (Fact.out : p.Prime).ne_zero)] at hz
    exact zero_ne_one hz
  have hnot (b : K) : b ^ p ≠ a := by
    intro hb
    have hb₀ : b ≠ 0 := by
      intro h
      apply ha₀
      rw [← hb, h, zero_pow (Fact.out : p.Prime).ne_zero]
    have hquot : (rootOfUnity (K := K) p (n + 1) /
        algebraMap K (AlgebraicClosure K) b) ^ p = 1 := by
      rw [div_pow, rootOfUnity_succ_pow, ← ha, ← map_pow, hb,
        div_self ((map_ne_zero (algebraMap K (AlgebraicClosure K))).mpr ha₀)]
    have hprimitive : IsPrimitiveRoot (rootOfUnity (K := K) p 1) p := by
      simpa only [pow_one] using isPrimitiveRoot_rootOfUnity (K := K) p 1
    obtain ⟨i, _, hi⟩ := hprimitive.eq_pow_of_pow_eq_one hquot
    have hζ₁ : rootOfUnity (K := K) p 1 ∈ (⊥ : IntermediateField K (AlgebraicClosure K)) := by
      rw [← h₁]
      exact rootOfUnity_mem_cyclotomicLayer p 1
    apply hnext
    apply le_antisymm _ bot_le
    apply IntermediateField.adjoin_simple_le_iff.mpr
    have hroot : rootOfUnity (K := K) p (n + 1) =
        rootOfUnity p 1 ^ i * algebraMap K (AlgebraicClosure K) b := by
      rw [hi, div_mul_cancel₀ _ ((map_ne_zero (algebraMap K (AlgebraicClosure K))).mpr hb₀)]
    rw [hroot]
    exact (⊥ : IntermediateField K (AlgebraicClosure K)).mul_mem
      ((⊥ : IntermediateField K (AlgebraicClosure K)).toSubalgebra.pow_mem hζ₁ i)
      ((⊥ : IntermediateField K (AlgebraicClosure K)).algebraMap_mem b)
  have hirr : Irreducible (Polynomial.X ^ p - Polynomial.C a : K[X]) :=
    X_pow_sub_C_irreducible_of_prime (Fact.out : p.Prime) hnot
  refine ⟨a, ha, ?_⟩
  symm
  apply minpoly.eq_of_irreducible_of_monic hirr
  · simp only [map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C,
      rootOfUnity_succ_pow, ha, sub_self]
  · exact Polynomial.monic_X_pow_sub_C a (Fact.out : p.Prime).ne_zero

/-- A genuinely new cyclotomic layer immediately above the base has
degree exactly `p` when the first roots of unity already lie in the base. -/
theorem cyclotomicLayer_step_finrank_of_eq_bot (n : ℕ)
    (h₁ : cyclotomicLayer (K := K) p 1 = ⊥)
    (hprev : cyclotomicLayer (K := K) p n = ⊥)
    (hnext : cyclotomicLayer (K := K) p (n + 1) ≠ ⊥) :
    Module.finrank K (cyclotomicLayer (K := K) p (n + 1)) = p := by
  obtain ⟨a, _, hmin⟩ := cyclotomicLayer_step_minpoly_of_eq_bot p n h₁ hprev hnext
  calc
    _ = (minpoly K (rootOfUnity (K := K) p (n + 1))).natDegree :=
      IntermediateField.adjoin.finrank (Algebra.IsIntegral.isIntegral _)
    _ = p := by rw [hmin, natDegree_X_pow_sub_C]

/-- Every nontrivial finite cyclotomic layer contains an actual first
nontrivial layer immediately above a layer equal to the original base. -/
theorem exists_first_nontrivial_cyclotomicLayer {n : ℕ}
    (hn : cyclotomicLayer (K := K) p n ≠ ⊥) :
    ∃ r : ℕ, r + 1 ≤ n ∧ cyclotomicLayer (K := K) p r = ⊥ ∧
      cyclotomicLayer (K := K) p (r + 1) ≠ ⊥ := by
  classical
  let h : ∃ j : ℕ, cyclotomicLayer (K := K) p j ≠ ⊥ := ⟨n, hn⟩
  have hz : Nat.find h ≠ 0 := by
    intro hz
    have hne := Nat.find_spec h
    rw [hz, cyclotomicLayer_zero] at hne
    exact hne rfl
  obtain ⟨r, hr⟩ := Nat.exists_eq_succ_of_ne_zero hz
  refine ⟨r, ?_, ?_, ?_⟩
  · have hle := Nat.find_min' h hn
    omega
  · exact not_not.mp (Nat.find_min h (by omega : r < Nat.find h))
  · simpa only [hr] using Nat.find_spec h

/-- A degree-`p` subfield of an actual finite odd-prime cyclotomic layer
is exactly the first nontrivial cyclotomic layer, if the first roots of
unity lie in the original base. -/
theorem exists_eq_first_cyclotomicLayer_of_finrank_prime [hp₂ : Fact (p ≠ 2)]
    (F : IntermediateField K (AlgebraicClosure K)) [FiniteDimensional K F]
    {m : ℕ} (hFm : F ≤ cyclotomicLayer (K := K) p m)
    (hd : Module.finrank K F = p) (h₁ : cyclotomicLayer (K := K) p 1 = ⊥) :
    ∃ r : ℕ, r + 1 ≤ m ∧ cyclotomicLayer (K := K) p r = ⊥ ∧
      cyclotomicLayer (K := K) p (r + 1) ≠ ⊥ ∧ F = cyclotomicLayer p (r + 1) := by
  have hm : cyclotomicLayer (K := K) p m ≠ ⊥ := by
    intro hm
    have hF : F = ⊥ := bot_unique (hm ▸ hFm)
    rw [hF, IntermediateField.finrank_bot] at hd
    exact (Fact.out : p.Prime).ne_one hd.symm
  obtain ⟨r, hrm, hprev, hnext⟩ := exists_first_nontrivial_cyclotomicLayer p hm
  refine ⟨r, hrm, hprev, hnext, ?_⟩
  let C := cyclotomicLayer (K := K) p m
  let i := IntermediateField.inclusion hFm
  let j := IntermediateField.inclusion (cyclotomicLayer_mono (K := K) p hrm)
  let := cyclotomicLayer_isCyclic (K := K) p m
  have heq : i.fieldRange = j.fieldRange := by
    apply IntermediateField.eq_of_finrank_eq_of_isCyclic
    calc
      _ = Module.finrank K F := i.equivFieldRange.toLinearEquiv.finrank_eq.symm
      _ = p := hd
      _ = Module.finrank K (cyclotomicLayer (K := K) p (r + 1)) :=
        (cyclotomicLayer_step_finrank_of_eq_bot p r h₁ hprev hnext).symm
      _ = _ := j.equivFieldRange.toLinearEquiv.finrank_eq
  have hmap := congrArg (fun E : IntermediateField K C => E.map C.val) heq
  have hi : C.val.comp i = F.val := rfl
  have hj : C.val.comp j = (cyclotomicLayer (K := K) p (r + 1)).val := rfl
  simpa only [AlgHom.map_fieldRange, hi, hj, IntermediateField.fieldRange_val] using hmap

end FiniteCyclotomic

section RadicalNormality

open Polynomial

variable {K : Type*} [NontriviallyNormedField K] [IsCompleteDiscreteValuedField K] [CharZero K]
variable (p : ℕ) [Fact p.Prime]
variable (π : 𝒪[K])

omit [CharZero K] in
theorem uniformizer_ne_pow_mul_torsion [hπ : Fact (Irreducible π)]
    (a u : K) {N : ℕ} (hN : N ≠ 0) (hu : u ^ N = 1) : (π : K) ≠ a ^ p * u := by
  intro heq
  have hunorm : ‖u‖ = 1 := by
    apply (pow_left_inj₀ (norm_nonneg u) zero_le_one hN).mp
    simp only [← norm_pow, hu, norm_one, one_pow]
  have hπnorm : ‖(π : K)‖ ≤ 1 := by
    have hmem := π.property
    change ‖(π : K)‖₊ ≤ 1 at hmem
    exact_mod_cast hmem
  have hanorm : ‖a‖ ≤ 1 := by
    by_contra! h
    have hpw := one_lt_pow₀ h (Fact.out : p.Prime).ne_zero
    rw [heq, norm_mul, norm_pow, hunorm, mul_one] at hπnorm
    exact (not_lt_of_ge hπnorm) hpw
  let a₀ : 𝒪[K] :=
    ⟨a, by change ‖a‖₊ ≤ 1; exact_mod_cast hanorm⟩
  let u₀ : 𝒪[K] :=
    ⟨u, by change ‖u‖₊ ≤ 1; exact_mod_cast hunorm.le⟩
  have hu₀ : u₀ ^ N = 1 := Subtype.ext hu
  have huunit : IsUnit u₀ := (Units.ofPowEqOne u₀ N hu₀ hN).isUnit
  have heq₀ : π = a₀ ^ p * u₀ := Subtype.ext heq
  have hv : p • IsDiscreteValuationRing.addVal _ a₀ = 1 := by
    calc
      _ = IsDiscreteValuationRing.addVal _ (a₀ ^ p * u₀) := by
        rw [IsDiscreteValuationRing.addVal_mul, IsDiscreteValuationRing.addVal_pow,
          IsDiscreteValuationRing.addVal_eq_zero_iff.mpr huunit, add_zero]
      _ = IsDiscreteValuationRing.addVal _ π :=
        congrArg (IsDiscreteValuationRing.addVal _) heq₀.symm
      _ = 1 := IsDiscreteValuationRing.addVal_uniformizer hπ.out
  have hnat := congrArg (fun v : ℕ∞ => v.toNat) hv
  simp only [nsmul_eq_mul, ENat.toNat_mul, ENat.toNat_natCast, ENat.toNat_one] at hnat
  exact (Fact.out : p.Prime).not_dvd_one ⟨_, hnat.symm⟩

/-- If an actual radical layer is already Galois, its normality contains
all the corresponding roots of unity in that same original field. -/
theorem cyclotomicLayer_le_radicalLayer_of_isGalois [hπ : Fact (Irreducible π)] (n : ℕ)
    [IsGalois K (radicalLayer p (π : K) n)] :
    cyclotomicLayer (K := K) p n ≤ radicalLayer p (π : K) n := by
  let F := radicalLayer p (π : K) n
  let f : K[X] := X ^ (p ^ n) - C (π : K)
  have hsplit : (f.map (algebraMap K F)).Splits := by
    have h := Normal.splits (inferInstance : Normal K F) (radicalLayerRoot p (π : K) n)
    simpa only [minpoly_radicalLayerRoot p π n] using h
  have hle : falseTateLayer p (π : K) n n ≤ F := by
    rw [← adjoin_rootSet_eq_falseTateLayer p (π : K) n]
    apply IntermediateField.adjoin_le_iff.mpr
    rw [← hsplit.image_rootSet F.val]
    rintro _ ⟨x, _, rfl⟩
    exact x.property
  exact (show cyclotomicLayer (K := K) p n ≤ falseTateLayer p (π : K) n n from
    le_sup_right).trans hle

/-- Normality of the first Eisenstein radical layer forces the first
cyclotomic layer to be the original base. -/
theorem cyclotomicLayer_one_eq_bot_of_radicalLayer_one_isGalois [Algebra (ℚ_[p]) K]
    [hπ : Fact (Irreducible π)]
    [IsGalois K (radicalLayer p (π : K) 1)] :
    cyclotomicLayer (K := K) p 1 = ⊥ := by
  have hd : Module.finrank K (cyclotomicLayer (K := K) p 1) ∣ p := by
    simpa only [finrank_radicalLayer p π 1, pow_one] using
      IntermediateField.finrank_dvd_of_le_right
        (cyclotomicLayer_le_radicalLayer_of_isGalois p π 1)
  have hle : Module.finrank K (cyclotomicLayer (K := K) p 1) ≤ p - 1 := by
    simpa only [pow_one, Nat.totient_prime (Fact.out : p.Prime)] using
      finrank_cyclotomicLayer_le_totient (K := K) p 1
  have hd₁ : Module.finrank K (cyclotomicLayer (K := K) p 1) = 1 := by
    rcases (Nat.dvd_prime (Fact.out : p.Prime)).mp hd with h | h
    · exact h
    · have := (Fact.out : p.Prime).pos
      omega
  apply le_antisymm _ bot_le
  exact IntermediateField.adjoin_simple_le_iff.mpr
    (IntermediateField.finrank_adjoin_simple_eq_one_iff.mp hd₁)

/-- The actual first radical cannot belong to the original infinite
cyclotomic extension at an odd prime. The proof uses finite cyclicity and
the literal reverse eigenbasis comparison over the original base. -/
theorem radical_one_not_mem_cyclotomicExtension [Algebra (ℚ_[p]) K]
    [hp₂ : Fact (p ≠ 2)] [hπ : Fact (Irreducible π)] :
    radical p (π : K) 1 ∉ cyclotomicExtension (K := K) p := by
  intro hmem
  obtain ⟨m, hm⟩ := (mem_cyclotomicExtension_iff p _).mp hmem
  have hFm : radicalLayer p (π : K) 1 ≤ cyclotomicLayer p m :=
    IntermediateField.adjoin_simple_le_iff.mpr hm
  have := cyclotomicLayer_isAbelianGalois (K := K) p m
  have : IsAbelianGalois K (radicalLayer p (π : K) 1) :=
    IsAbelianGalois.of_algHom (IntermediateField.inclusion hFm)
  have h₁ := cyclotomicLayer_one_eq_bot_of_radicalLayer_one_isGalois p π
  obtain ⟨r, _, hprev, hnext, hF⟩ :=
    exists_eq_first_cyclotomicLayer_of_finrank_prime p (radicalLayer p (π : K) 1)
      hFm (by simpa only [pow_one] using finrank_radicalLayer p π 1) h₁
  obtain ⟨u, hu, _⟩ := cyclotomicLayer_step_minpoly_of_eq_bot p r h₁ hprev hnext
  let C := cyclotomicLayer (K := K) p (r + 1)
  let B : PowerBasis K C := IntermediateField.adjoin.powerBasis
    (show IsIntegral K (rootOfUnity (K := K) p (r + 1)) from Algebra.IsIntegral.isIntegral _)
  have hdim : B.dim = p := B.finrank.symm.trans
    (cyclotomicLayer_step_finrank_of_eq_bot p r h₁ hprev hnext)
  have hβpow : B.gen ^ p = algebraMap K C u := by
    apply C.val.injective
    exact rootOfUnity_succ_pow (K := K) p r |>.trans hu.symm
  have hβunity : B.gen ^ (p ^ (r + 1)) = 1 :=
    Subtype.ext (rootOfUnity_pow (K := K) p (r + 1))
  have hβ₀ : B.gen ≠ 0 := by
    intro hz
    rw [hz, zero_pow (pow_ne_zero (r + 1) (Fact.out : p.Prime).ne_zero)] at hβunity
    exact zero_ne_one hβunity
  have hαmem : radical p (π : K) 1 ∈ C := by
    change radical p (π : K) 1 ∈ cyclotomicLayer p (r + 1)
    rw [← hF]
    exact radical_mem_radicalLayer p (π : K) 1
  let α : C := ⟨radical p (π : K) 1, hαmem⟩
  have hαpow : α ^ p = algebraMap K C (π : K) := by
    apply C.val.injective
    change radical p (π : K) 1 ^ p = algebraMap K (AlgebraicClosure K) (π : K)
    simpa only [pow_one] using radical_pow p (π : K) 1
  have hα₀ : α ≠ 0 := by
    intro hz
    exact radical_ne_zero p (π : K) 1
      (congrArg Subtype.val hz)
  have hζmem : rootOfUnity (K := K) p 1 ∈ (⊥ : IntermediateField K (AlgebraicClosure K)) := by
    rw [← h₁]
    exact rootOfUnity_mem_cyclotomicLayer p 1
  obtain ⟨z, hz⟩ := hζmem
  change algebraMap K (AlgebraicClosure K) z = rootOfUnity p 1 at hz
  have hzprim : IsPrimitiveRoot z p := by
    have hh : IsPrimitiveRoot (algebraMap K (AlgebraicClosure K) z) p := by
      rw [hz]
      simpa only [pow_one] using isPrimitiveRoot_rootOfUnity (K := K) p 1
    exact hh.of_map_of_injective (f := algebraMap K (AlgebraicClosure K))
      (algebraMap K (AlgebraicClosure K)).injective
  have hzC : IsPrimitiveRoot (algebraMap K C z) p :=
    hzprim.map_of_injective (algebraMap K C).injective
  have hcard : Nat.card (C ≃ₐ[K] C) = p :=
    (IsGalois.card_aut_eq_finrank K C).trans
      (cyclotomicLayer_step_finrank_of_eq_bot p r h₁ hprev hnext)
  have : Nontrivial (C ≃ₐ[K] C) :=
    Finite.one_lt_card_iff_nontrivial.mp (hcard ▸ (Fact.out : p.Prime).one_lt)
  obtain ⟨σ, hσ⟩ := exists_ne (1 : C ≃ₐ[K] C)
  have hσβ : σ B.gen ≠ B.gen := by
    intro hfix
    apply hσ
    have heq : σ.toAlgHom = (1 : C ≃ₐ[K] C).toAlgHom := by
      apply IntermediateField.adjoin_algHom_ext
      intro x hx
      obtain rfl := Set.mem_singleton_iff.mp hx
      exact hfix
    exact AlgEquiv.ext (AlgHom.congr_fun heq)
  have hratio {x : C} (hx₀ : x ≠ 0) {a : K} (hx : x ^ p = algebraMap K C a) :
      (σ x / x) ^ p = 1 := by
    rw [div_pow, ← map_pow, hx, σ.commutes, ← hx, div_self (pow_ne_zero p hx₀)]
  obtain ⟨c, hc, hceq⟩ := hzC.eq_pow_of_pow_eq_one (hratio hβ₀ hβpow)
  have hc₀ : c ≠ 0 := by
    intro hc₀
    apply hσβ
    have hdiv : σ B.gen / B.gen = 1 := by simpa only [hc₀, pow_zero] using hceq.symm
    exact (div_eq_one_iff_eq hβ₀).mp hdiv
  have hcop : c.Coprime p := ((Fact.out : p.Prime).coprime_iff_not_dvd.mpr
    (Nat.not_dvd_of_pos_of_lt (Nat.pos_of_ne_zero hc₀) hc)).symm
  have hprimitive : IsPrimitiveRoot (z ^ c) B.dim := by
    rw [hdim]
    exact hzprim.pow_of_coprime c hcop
  have hgen : σ B.gen = (z ^ c) • B.gen := by
    rw [Algebra.smul_def]
    rw [map_pow, hceq, div_mul_cancel₀ _ hβ₀]
  obtain ⟨b, _, hbeq⟩ := hzC.eq_pow_of_pow_eq_one (hratio hα₀ hαpow)
  have heigen : σ α = (z ^ b) • α := by
    rw [Algebra.smul_def]
    rw [map_pow, hbeq, div_mul_cancel₀ _ hα₀]
  obtain ⟨i, a, ha⟩ := B.eigenvector_eq_smul_pow σ hprimitive hgen hα₀ heigen
  have heq : (π : K) = a ^ p * u ^ (i : ℕ) := by
    apply (algebraMap K C).injective
    rw [map_mul, map_pow, map_pow]
    calc
      _ = α ^ p := hαpow.symm
      _ = (a • B.gen ^ (i : ℕ)) ^ p := congrArg (fun x : C => x ^ p) ha
      _ = algebraMap K C a ^ p * (B.gen ^ p) ^ (i : ℕ) := by
        simp only [Algebra.smul_def, mul_pow]
        congr 1
        rw [← pow_mul, ← pow_mul, Nat.mul_comm (i : ℕ) p]
      _ = _ := by rw [hβpow]
  have hunity : (u ^ (i : ℕ)) ^ (p ^ r) = 1 := by
    apply (algebraMap K (AlgebraicClosure K)).injective
    rw [map_pow, map_pow, hu, ← pow_mul, Nat.mul_comm (i : ℕ) (p ^ r), pow_mul,
      rootOfUnity_pow, one_pow, map_one]
  exact uniformizer_ne_pow_mul_torsion p π a (u ^ (i : ℕ))
    (pow_ne_zero r (Fact.out : p.Prime).ne_zero) hunity heq

end RadicalNormality

section InfiniteCoordinates

variable {K : Type*} [Field K] [CharZero K] (p : ℕ) [Fact p.Prime] (π : K)

/-- The prescribed radical, viewed in the original infinite false Tate field. -/
def extensionRadical (n : ℕ) : falseTateExtension p π :=
  IntermediateField.inclusion (falseTateLayer_le_falseTateExtension p π n n)
    (layerRadical p π n)

@[simp]
theorem coe_extensionRadical (n : ℕ) :
    (extensionRadical p π n : AlgebraicClosure K) = radical p π n := rfl

/-- The infinite Kummer coordinate evaluates on each original chosen radical. -/
theorem padicKummerExponent_spec [hπ : NeZero π]
    (g : falseTateExtension p π ≃ₐ[K] falseTateExtension p π) (n : ℕ) :
    g (extensionRadical p π n) = extensionRootOfUnity p π n ^
      (PadicInt.toZModPow n (padicKummerExponent p π g)).val *
        extensionRadical p π n := by
  rw [padicKummerExponent_toZModPow p π]
  rw [extensionRadical, ← infiniteLayerRestriction_commutes p π]
  rw [finiteKummerExponent_spec p π n, map_mul, map_pow]
  rfl

/-- The original cyclotomic subfield has precisely the actual character kernel
as its fixing subgroup in the original false Tate field. -/
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

/-- Fixing by the actual character kernel places an original radical in the
actual cyclotomic subfield, by infinite Galois correspondence. -/
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

/-- The canonical affine semidirect product with its unit factor restricted
to a specified actual subgroup. -/
abbrev RestrictedPadicAffineGroup :=
  SemidirectProduct (Multiplicative (ℤ_[p])) H ((padicAffineAction p).comp H.subtype)

/-- Ordinary product coordinates for the restricted canonical semidirect product. -/
def restrictedPadicAffineEquivProd : RestrictedPadicAffineGroup p H ≃ ℤ_[p] × H :=
  SemidirectProduct.equivProd.trans
    (Equiv.prodCongr Multiplicative.toAdd (Equiv.refl _))

/-- The usual product topology on the restricted semidirect product. -/
instance restrictedPadicAffineTopologicalSpace :
    TopologicalSpace (RestrictedPadicAffineGroup p H) :=
  (restrictedPadicAffineEquivProd p H).topologicalSpace

/-- The chosen topology is precisely the product topology in affine coordinates. -/
def restrictedPadicAffineHomeomorphProd :
    RestrictedPadicAffineGroup p H ≃ₜ ℤ_[p] × H :=
  (restrictedPadicAffineEquivProd p H).homeomorph

instance restrictedPadicAffineT2Space : T2Space (RestrictedPadicAffineGroup p H) :=
  (restrictedPadicAffineHomeomorphProd p H).symm.t2Space

instance restrictedPadicAffineIsTopologicalGroup :
    IsTopologicalGroup (RestrictedPadicAffineGroup p H) where
  continuous_mul := by
    have hl : Continuous (fun x : RestrictedPadicAffineGroup p H => x.left.toAdd) :=
      continuous_fst.comp (restrictedPadicAffineHomeomorphProd p H).continuous
    have hr : Continuous (fun x : RestrictedPadicAffineGroup p H => x.right) :=
      continuous_snd.comp (restrictedPadicAffineHomeomorphProd p H).continuous
    have hu : Continuous (fun x : RestrictedPadicAffineGroup p H => (x.right.val : ℤ_[p])) :=
      Units.continuous_val.comp (continuous_subtype_val.comp hr)
    apply continuous_induced_rng.mpr
    change Continuous (fun x : RestrictedPadicAffineGroup p H × RestrictedPadicAffineGroup p H =>
      (x.1.left.toAdd + (x.1.right.val : ℤ_[p]) * x.2.left.toAdd, x.1.right * x.2.right))
    exact ((hl.comp continuous_fst).add
      ((hu.comp continuous_fst).mul (hl.comp continuous_snd))).prodMk
      ((hr.comp continuous_fst).mul (hr.comp continuous_snd))
  continuous_inv := by
    have hl : Continuous (fun x : RestrictedPadicAffineGroup p H => x.left.toAdd) :=
      continuous_fst.comp (restrictedPadicAffineHomeomorphProd p H).continuous
    have hr : Continuous (fun x : RestrictedPadicAffineGroup p H => x.right) :=
      continuous_snd.comp (restrictedPadicAffineHomeomorphProd p H).continuous
    apply continuous_induced_rng.mpr
    change Continuous (fun x : RestrictedPadicAffineGroup p H =>
      (((x.right⁻¹).val : ℤ_[p]) * (-x.left.toAdd), x.right⁻¹))
    exact ((Units.continuous_val.comp
      (continuous_subtype_val.comp hr.inv)).mul hl.neg).prodMk hr.inv

end RestrictedAffineGroup

section RestrictedCoordinates

variable {K : Type*} [Field K] [CharZero K] (p : ℕ) [Fact p.Prime] (π : K)

/-- The original affine coordinates, with unit coordinate in the actual
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

/-- Restricting the unit coordinate retains continuity in the ordinary product topology. -/
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

/-- At an odd prime the actual closed translation kernel is the whole p-adic
additive group, with the coordinate normalization fixed by the chosen roots. -/
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

/-- The actual Kummer coordinate is a topological additive isomorphism onto
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

/-- The actual character-kernel automorphism whose chosen Kummer coordinate
is exactly one. -/
def tau [hp₂ : Fact (p ≠ 2)] [hπ : Fact (Irreducible π)] :
    (padicCyclotomicCharacter p (π : K)).ker :=
  ((fullKummerKernelEquiv p π).symm 1).toMul

@[simp]
theorem padicKummerExponent_tau [hp₂ : Fact (p ≠ 2)] [hπ : Fact (Irreducible π)] :
    padicKummerExponent p (π : K)
      (tau p π).val = 1 :=
  (fullKummerKernelEquiv p π).apply_symm_apply 1

/-- The prescribed generator acts on every chosen positive-level radical
by multiplication by the corresponding chosen root of unity. -/
theorem tau_extensionRadical [hp₂ : Fact (p ≠ 2)] [hπ : Fact (Irreducible π)] (n : ℕ) :
    (tau p π).val (extensionRadical p (π : K) (n + 1)) =
      extensionRootOfUnity p (π : K) (n + 1) * extensionRadical p (π : K) (n + 1) := by
  rw [padicKummerExponent_spec p (π : K),
    padicKummerExponent_tau, map_one]
  have hpow : 1 < p ^ (n + 1) := one_lt_pow₀ (Fact.out : p.Prime).one_lt (Nat.succ_ne_zero n)
  simp only [ZMod.val_one'' (ne_of_gt hpow), pow_one]

/-- Integral powers of the prescribed automorphism are dense in the original
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

/-- Every translation coordinate and every actual cyclotomic unit coordinate
occur together in the original Galois group. -/
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

/-- The actual cyclotomic fixer and actual radical fixer generate the whole
original false Tate Galois group. -/
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

/-- The original infinite radical and cyclotomic subfields meet exactly in
the original base field, for every odd prime and every actual uniformizer. -/
theorem kummerExtension_inf_cyclotomicExtension [hp₂ : Fact (p ≠ 2)] [hπ : Fact (Irreducible π)] :
    kummerExtension p (π : K) ⊓ cyclotomicExtension (K := K) p = ⊥ := by
  have := falseTateExtension_isGalois p (π : K)
  apply IntermediateField.inf_eq_bot_of_inclusion_fixingSubgroup_sup_eq_top
    (kummerExtension_le_falseTateExtension p (π : K))
    (cyclotomicExtension_le_falseTateExtension p (π : K))
  rw [cyclotomicInclusion_fixingSubgroup, sup_comm]
  exact cyclotomicKernel_sup_kummerFixing p π

/-- The original Krull Galois group is the canonical affine semidirect product
of all translations by the actual cyclotomic character image. -/
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

/-- The semidirect isomorphism retains the original actual Kummer coordinate. -/
theorem falseTateGaloisEquiv_left [hp₂ : Fact (p ≠ 2)] [hπ : Fact (Irreducible π)]
    (g : falseTateExtension p (π : K) ≃ₐ[K] falseTateExtension p (π : K)) :
    (falseTateGaloisEquiv p π g).left.toAdd =
      padicKummerExponent p (π : K) g := rfl

/-- The semidirect isomorphism retains the original actual cyclotomic character. -/
theorem falseTateGaloisEquiv_right [hp₂ : Fact (p ≠ 2)] [hπ : Fact (Irreducible π)]
    (g : falseTateExtension p (π : K) ≃ₐ[K] falseTateExtension p (π : K)) :
    (falseTateGaloisEquiv p π g).right.val = padicCyclotomicCharacter p (π : K) g := rfl

/-- The original cyclotomic fixer is exactly the translation factor under
the actual topological semidirect isomorphism. -/
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

/-- The original radical fixer is exactly the pure cyclotomic-unit factor. -/
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

/-- Restriction of the actual cyclotomic character identifies the original
radical fixer with the actual cyclotomic character image. -/
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

/-- On the original radical fixer the factor isomorphism is the usual
cyclotomic character, with its actual image as codomain. -/
theorem kummerFixingEquivCyclotomicImage_apply [hp₂ : Fact (p ≠ 2)] [hπ : Fact (Irreducible π)]
    (g : falseTateKummerFixing p (π : K)) :
    (kummerFixingEquivCyclotomicImage p π g).val =
      padicCyclotomicCharacter p (π : K) g.val := rfl

/-- The prescribed generator fixes the original embedded cyclotomic field. -/
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

/-- Fixing the cyclotomic field and the displayed actions on all compatible
positive-level radicals uniquely specify the original automorphism. -/
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
on the original character kernel. -/
def fullKummerKernelMulEquiv [hp₂ : Fact (p ≠ 2)] [hπ : Fact (Irreducible π)] :
    (padicCyclotomicCharacter p (π : K)).ker ≃ₜ* Multiplicative (ℤ_[p]) := by
  let e := fullKummerKernelEquiv p π
  exact
    { AddEquiv.toMultiplicativeRight e.toAddEquiv with
      continuous_toFun := continuous_ofAdd.comp (e.continuous.comp continuous_ofMul)
      continuous_invFun := continuous_toMul.comp (e.symm.continuous.comp continuous_toAdd) }

end FullTranslation

section RelativeCyclotomic

variable {K : Type*} [NontriviallyNormedField K] [IsCompleteDiscreteValuedField K] [CharZero K]
variable (p : ℕ) [Fact p.Prime] [Algebra (ℚ_[p]) K]
variable (π : 𝒪[K])

/-- The original inclusion defines the relative cyclotomic scalar action. -/
local instance cyclotomicRelativeAlgebra :
    Algebra (cyclotomicExtension (K := K) p) (falseTateExtension p (π : K)) :=
  IntermediateField.algebraOfLE (cyclotomicExtension_le_falseTateExtension p (π : K))

local instance cyclotomicRelativeScalarTower :
    IsScalarTower K (cyclotomicExtension (K := K) p) (falseTateExtension p (π : K)) :=
  IntermediateField.isScalarTower_of_le (cyclotomicExtension_le_falseTateExtension p (π : K))

omit [Algebra (ℚ_[p]) K] in
/-- The relative scalar homomorphism is exactly the original cyclotomic inclusion. -/
theorem cyclotomicRelative_scalarHom_eq :
    IsScalarTower.toAlgHom K (cyclotomicExtension (K := K) p) (falseTateExtension p (π : K)) =
      IntermediateField.inclusion (cyclotomicExtension_le_falseTateExtension p (π : K)) := by
  apply AlgHom.ext
  intro x
  rfl

/-- The original character kernel is the original relative cyclotomic Galois
group, with its own Krull topology and original inclusion of scalars. -/
def cyclotomicKernelRelativeEquiv [hπ : Fact (Irreducible π)] :
    (padicCyclotomicCharacter p (π : K)).ker ≃ₜ*
      (falseTateExtension p (π : K) ≃ₐ[cyclotomicExtension (K := K) p]
        falseTateExtension p (π : K)) := by
  have := falseTateExtension_isGalois p (π : K)
  let i := IntermediateField.inclusion (cyclotomicExtension_le_falseTateExtension p (π : K))
  let e : (padicCyclotomicCharacter p (π : K)).ker ≃ₜ* i.fieldRange.fixingSubgroup :=
    { MulEquiv.subgroupCongr (cyclotomicInclusion_fixingSubgroup p (π : K)).symm with
      continuous_toFun := continuous_subtype_val.subtype_mk _
      continuous_invFun := continuous_subtype_val.subtype_mk _ }
  exact e.trans (AlgEquiv.fixingSubgroupContinuousMulEquiv K (cyclotomicExtension (K := K) p)
    (falseTateExtension p (π : K)) i (AlgHom.congr_fun (cyclotomicRelative_scalarHom_eq p π)))

/-- The original relative cyclotomic Galois group is the full p-adic
translation factor, normalized by the prescribed roots. -/
def cyclotomicRelativeGaloisEquiv [hp₂ : Fact (p ≠ 2)] [hπ : Fact (Irreducible π)] :
    (falseTateExtension p (π : K) ≃ₐ[cyclotomicExtension (K := K) p]
      falseTateExtension p (π : K)) ≃ₜ* Multiplicative (ℤ_[p]) :=
  (cyclotomicKernelRelativeEquiv p π).symm.trans (fullKummerKernelMulEquiv p π)

/-- The prescribed generator as an actual automorphism over the original
cyclotomic field, rather than only as an element of its fixing subgroup. -/
def relativeTau [hp₂ : Fact (p ≠ 2)] [hπ : Fact (Irreducible π)] :
    falseTateExtension p (π : K) ≃ₐ[cyclotomicExtension (K := K) p]
      falseTateExtension p (π : K) :=
  cyclotomicKernelRelativeEquiv p π (tau p π)

/-- The original relative generator has precisely the prescribed radical actions. -/
theorem relativeTau_extensionRadical [hp₂ : Fact (p ≠ 2)] [hπ : Fact (Irreducible π)] (n : ℕ) :
    relativeTau p π (extensionRadical p (π : K) (n + 1)) =
      extensionRootOfUnity p (π : K) (n + 1) * extensionRadical p (π : K) (n + 1) :=
  tau_extensionRadical p π n

/-- Integral powers are dense in the original relative cyclotomic Galois group. -/
theorem denseRange_relativeTau_zpow [hp₂ : Fact (p ≠ 2)] [hπ : Fact (Irreducible π)] :
    DenseRange (fun n : ℤ => relativeTau p π ^ n) := by
  have hd := (cyclotomicKernelRelativeEquiv p π).surjective.denseRange.comp
    (denseRange_tau_zpow p π) (cyclotomicKernelRelativeEquiv p π).continuous
  simpa only [Function.comp_def, map_zpow, relativeTau] using hd

/-- The original relative generator corresponds to exactly one under the
isomorphism normalized by the prescribed compatible roots. -/
theorem cyclotomicRelativeGaloisEquiv_relativeTau [hp₂ : Fact (p ≠ 2)] [hπ : Fact (Irreducible π)] :
    cyclotomicRelativeGaloisEquiv p π (relativeTau p π) =
      Multiplicative.ofAdd (1 : ℤ_[p]) := by
  change fullKummerKernelMulEquiv p π
    ((cyclotomicKernelRelativeEquiv p π).symm
      (cyclotomicKernelRelativeEquiv p π (tau p π))) = _
  rw [(cyclotomicKernelRelativeEquiv p π).symm_apply_apply]
  exact congrArg Multiplicative.ofAdd (padicKummerExponent_tau p π)

/-- The displayed actions uniquely determine the generator in the original
relative cyclotomic Galois group. -/
theorem relativeTau_unique [hp₂ : Fact (p ≠ 2)] [hπ : Fact (Irreducible π)]
    (g : falseTateExtension p (π : K) ≃ₐ[cyclotomicExtension (K := K) p]
      falseTateExtension p (π : K))
    (hg : ∀ n : ℕ, g (extensionRadical p (π : K) (n + 1)) =
      extensionRootOfUnity p (π : K) (n + 1) * extensionRadical p (π : K) (n + 1)) :
    g = relativeTau p π := by
  apply (cyclotomicKernelRelativeEquiv p π).symm.injective
  change (cyclotomicKernelRelativeEquiv p π).symm g =
    (cyclotomicKernelRelativeEquiv p π).symm
      (cyclotomicKernelRelativeEquiv p π (tau p π))
  rw [(cyclotomicKernelRelativeEquiv p π).symm_apply_apply]
  apply tau_unique p π
  exact hg

end RelativeCyclotomic

section RelativeKummer

variable {K : Type*} [NontriviallyNormedField K] [IsCompleteDiscreteValuedField K] [CharZero K]
variable (p : ℕ) [Fact p.Prime] [Algebra (ℚ_[p]) K]
variable (π : 𝒪[K])

/-- The original inclusion defines the relative radical scalar action. -/
local instance kummerRelativeAlgebra :
    Algebra (kummerExtension p (π : K)) (falseTateExtension p (π : K)) :=
  IntermediateField.algebraOfLE (kummerExtension_le_falseTateExtension p (π : K))

local instance kummerRelativeScalarTower :
    IsScalarTower K (kummerExtension p (π : K)) (falseTateExtension p (π : K)) :=
  IntermediateField.isScalarTower_of_le (kummerExtension_le_falseTateExtension p (π : K))

omit [Algebra (ℚ_[p]) K] in
/-- The relative scalar homomorphism is exactly the original radical inclusion. -/
theorem kummerRelative_scalarHom_eq :
    IsScalarTower.toAlgHom K (kummerExtension p (π : K)) (falseTateExtension p (π : K)) =
      falseTateKummerInclusion p (π : K) := by
  apply AlgHom.ext
  intro x
  rfl

/-- The actual Galois group over the original radical field is the actual
cyclotomic character image, with both of their original topologies. -/
def kummerRelativeGaloisEquiv [hp₂ : Fact (p ≠ 2)] [hπ : Fact (Irreducible π)] :
    (falseTateExtension p (π : K) ≃ₐ[kummerExtension p (π : K)]
      falseTateExtension p (π : K)) ≃ₜ* (cyclotomicExtensionCharacter (K := K) p).range := by
  have := falseTateExtension_isGalois p (π : K)
  exact (AlgEquiv.fixingSubgroupContinuousMulEquiv K (kummerExtension p (π : K))
    (falseTateExtension p (π : K)) (falseTateKummerInclusion p (π : K))
    (AlgHom.congr_fun (kummerRelative_scalarHom_eq p π))).symm.trans
      (kummerFixingEquivCyclotomicImage p π)

end RelativeKummer

end FalseTateExtension
