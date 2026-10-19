/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FalseTateExtension.Padic.FiniteCharacter
public import FontaineWintenberger.Ramification.Lower.Generator
public import FontaineWintenberger.Ramification.Lower.Basic
public import FontaineWintenberger.Ramification.Upper.Basic
public import Mathlib.Data.ZMod.Units

/-!
# The actual rational cyclotomic ramification filtration

The chosen cyclotomic uniformizer and its conjugates determine the integer
and real lower groups, supplying the finite input for the Herbrand integrals.
-/

@[expose] public section

noncomputable section

namespace FalseTateExtension

open Polynomial IsDiscreteValuationRing

variable (p : ℕ) [Fact p.Prime]

local notation "Qp" => Padic p
local notation "L(" n ")" => cyclotomicLayer (K := Padic p) p (n + 1)
local notation "O(" n ")" => FontaineWintenberger.spectralIntegerRing (Padic p) L(n)

local instance (n : ℕ) : IsDiscreteValuationRing O(n) :=
  cyclotomicValuationSubring_isDiscreteValuationRing p (n + 1)
    (FontaineWintenberger.spectralValuation Qp L(n))

local notation "v(" n ")" =>
  IsDedekindDomain.HeightOneSpectrum.valuation L(n) (maximalIdeal O(n))

/-- Every primitive root in the actual layer has the signed cyclotomic
norm; the sign is retained at the first dyadic level. -/
theorem norm_primitive_cyclotomic_sub_one (n : ℕ) {ζ : L(n)}
    (hζ : IsPrimitiveRoot ζ (p ^ (n + 1))) :
    Algebra.norm Qp (ζ - 1) = (-1 : Qp) ^ (p ^ (n + 1)).totient * p := by
  have : NeZero (p ^ (n + 1)) := ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
  let pb := hζ.subOnePowerBasis Qp
  have hdim : pb.dim = (p ^ (n + 1)).totient := by
    rw [← pb.finrank, finrank_cyclotomicLayer_padic]
  have hn := Algebra.PowerBasis.norm_gen_eq_coeff_zero_minpoly pb
  rw [IsPrimitiveRoot.subOnePowerBasis_gen, hdim,
    hζ.minpoly_sub_one_eq_cyclotomic_comp (Padic.irreducible_cyclotomic_prime_pow p (n + 1))] at hn
  simpa only [coeff_zero_eq_eval_zero, eval_comp, eval_add, eval_X, eval_one,
    zero_add, eval_one_cyclotomic_prime_pow] using hn

/-- The original normalized spectral valuation of any primitive root minus
one is the uniformizer value, at every positive layer and every prime. -/
theorem normalizedValuation_primitive_cyclotomic_sub_one (n : ℕ) {ζ : L(n)}
    (hζ : IsPrimitiveRoot ζ (p ^ (n + 1))) :
    v(n) (ζ - 1) = WithZero.exp (-1 : ℤ) := by
  have hn := FontaineWintenberger.extensionValuationSubring_normalizedValuation_norm
    Qp L(n) (FontaineWintenberger.spectralValuation Qp L(n)) (ζ - 1)
  rw [norm_primitive_cyclotomic_sub_one p n hζ, cyclotomicLayer_spectral_residueDegree,
    pow_one] at hn
  simpa only [map_mul, map_pow, Valuation.map_neg, map_one, one_pow, one_mul,
    padicUnitBall_normalizedValuation_p] using hn.symm

/-- Prime-power powers of a primitive root have their exact normalized
displacement valuation in the original layer, including the first dyadic layer. -/
theorem normalizedValuation_primitive_cyclotomic_pow_sub_one
    (n s : ℕ) (hs : s ≤ n) {ζ : L(n)}
    (hζ : IsPrimitiveRoot ζ (p ^ (n + 1))) :
    v(n) (ζ ^ (p ^ s) - 1) = WithZero.exp (-(p ^ s : ℕ) : ℤ) := by
  by_cases hn : n = 0
  · subst n
    have : s = 0 := by omega
    subst s
    simpa only [pow_zero, pow_one, Nat.cast_one] using
      normalizedValuation_primitive_cyclotomic_sub_one p 0 hζ
  · have hv := FontaineWintenberger.extensionValuationSubring_normalizedValuation_norm
      Qp L(n) (FontaineWintenberger.spectralValuation Qp L(n)) (ζ ^ (p ^ s) - 1)
    rw [hζ.norm_pow_sub_one_eq_prime_pow_of_ne_zero
      (Padic.irreducible_cyclotomic_prime_pow p (n + 1)) hs hn,
      cyclotomicLayer_spectral_residueDegree, pow_one, map_pow,
      padicUnitBall_normalizedValuation_p] at hv
    simpa using hv.symm

/-- A nonidentity unit exponent has a prime-power displacement with a
coprime remaining factor, strictly below the cyclotomic level. -/
theorem cyclotomic_exponent_decomposition (n : ℕ)
    (a : (ZMod (p ^ (n + 1)))ˣ) (ha : a ≠ 1) :
    ∃ b : ℕ, padicValNat p ((a : ZMod (p ^ (n + 1))).val - 1) ≤ n ∧ ¬ p ∣ b ∧
      (a : ZMod (p ^ (n + 1))).val =
        1 + p ^ padicValNat p ((a : ZMod (p ^ (n + 1))).val - 1) * b := by
  have hN : 1 < p ^ (n + 1) := one_lt_pow₀ (Fact.out : p.Prime).one_lt (by omega)
  have : Fact (1 < p ^ (n + 1)) := ⟨hN⟩
  have : NeZero (p ^ (n + 1)) := ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
  have ht : 0 < (a : ZMod (p ^ (n + 1))).val :=
    ZMod.val_pos.mpr (Units.ne_zero a)
  have hta : (a : ZMod (p ^ (n + 1))).val ≠ 1 := by
    intro h
    exact ha (Units.ext ((ZMod.val_eq_one hN _).mp h))
  let d := (a : ZMod (p ^ (n + 1))).val - 1
  have hd : 0 < d := by dsimp [d]; omega
  let s := padicValNat p d
  let b := d.divMaxPow p
  have hfactor : p ^ s * b = d := Nat.pow_padicValNat_mul_divMaxPow p d
  have hp_le : p ^ s ≤ d := Nat.le_of_dvd hd pow_padicValNat_dvd
  have hd_lt : d < p ^ (n + 1) :=
    (Nat.sub_le _ _).trans_lt (ZMod.val_lt _)
  have hs : s < n + 1 :=
    (pow_lt_pow_iff_right₀ (Fact.out : p.Prime).one_lt).mp (hp_le.trans_lt hd_lt)
  refine ⟨b, by change s ≤ n; omega,
    Nat.not_dvd_divMaxPow (Fact.out : p.Prime).one_lt hd.ne', ?_⟩
  change (a : ZMod (p ^ (n + 1))).val = 1 + p ^ s * b
  rw [hfactor]
  dsimp [d]
  omega

/-- A root of unity has unit value for the original normalized spectral
valuation. -/
theorem normalizedValuation_primitive_cyclotomic_root (n : ℕ) {ζ : L(n)}
    (hζ : IsPrimitiveRoot ζ (p ^ (n + 1))) : v(n) ζ = 1 := by
  apply (pow_eq_one_iff_of_nonneg (show 0 ≤ v(n) ζ from zero_le)
    (pow_ne_zero (n + 1) (Fact.out : p.Prime).ne_zero)).mp
  rw [← map_pow, hζ.pow_eq_one, map_one]

/-- The actual finite character computes the exact normalized displacement
of the chosen cyclotomic root in its original field. -/
theorem normalizedValuation_cyclotomic_displacement_of_exponent
    (n s b : ℕ) (hs : s ≤ n) (hb : ¬ p ∣ b)
    (g : L(n) ≃ₐ[Qp] L(n))
    (ha : (cyclotomicLayerCharacter p (n + 1) g : ZMod (p ^ (n + 1))).val =
      1 + p ^ s * b) :
    v(n) (g (cyclotomicLayerRoot p (n + 1)) - cyclotomicLayerRoot p (n + 1)) =
      WithZero.exp (-(p ^ s : ℕ) : ℤ) := by
  let ζ := cyclotomicLayerRoot p (n + 1)
  have hζ := isPrimitiveRoot_cyclotomicLayerRoot p (n + 1)
  have hpower : IsPrimitiveRoot (ζ ^ b) (p ^ (n + 1)) :=
    hζ.pow_of_coprime b ((Fact.out : p.Prime).coprime_pow_of_not_dvd hb)
  have hv := normalizedValuation_primitive_cyclotomic_pow_sub_one p n s hs hpower
  have heq : ζ ^ (1 + p ^ s * b) - ζ = ζ * ((ζ ^ b) ^ (p ^ s) - 1) := by
    rw [pow_add, pow_one, ← pow_mul, Nat.mul_comm b]
    ring
  rw [cyclotomicLayerCharacter_spec, ha]
  change v(n) (ζ ^ (1 + p ^ s * b) - ζ) = _
  rw [heq, map_mul, normalizedValuation_primitive_cyclotomic_root p n hζ, one_mul]
  exact hv

/-- Every nonidentity automorphism has an actual cyclotomic displacement
with a prime-power order below the level. -/
theorem normalizedValuation_cyclotomic_displacement
    (n : ℕ) (g : L(n) ≃ₐ[Qp] L(n)) (hg : g ≠ 1) :
    ∃ s : ℕ, s ≤ n ∧
      v(n) (g (cyclotomicLayerRoot p (n + 1)) - cyclotomicLayerRoot p (n + 1)) =
        WithZero.exp (-(p ^ s : ℕ) : ℤ) := by
  have ha : cyclotomicLayerCharacter p (n + 1) g ≠ 1 := by
    intro h
    exact hg (cyclotomicLayerCharacter_injective p (n + 1)
      (h.trans (map_one _).symm))
  obtain ⟨b, hs, hb, ha⟩ := cyclotomic_exponent_decomposition p n _ ha
  exact ⟨_, hs, normalizedValuation_cyclotomic_displacement_of_exponent p n _ b hs hb g ha⟩

/-- The chosen cyclotomic uniformizer generates the original spectral
integer ring over the actual p-adic base integers. -/
theorem cyclotomicUniformizer_adjoin_spectral (n : ℕ) :
    Algebra.adjoin (NormedField.valuation (K := Qp)).valuationSubring
      {cyclotomicUniformizer p n (FontaineWintenberger.spectralValuation Qp L(n))} = ⊤ :=
  FontaineWintenberger.extensionValuationSubring_adjoin_uniformizer_eq_top
    Qp L(n) (FontaineWintenberger.spectralValuation Qp L(n))
    (cyclotomicLayer_ramificationIdx p n _)
    (irreducible_cyclotomicUniformizer_spectral p n)

/-- The actual ramification order is exactly the prime-power displacement
read from the original finite character. -/
theorem ramificationOrder_cyclotomic_of_exponent
    (n s b : ℕ) (hs : s ≤ n) (hb : ¬ p ∣ b)
    (g : L(n) ≃ₐ[Qp] L(n))
    (ha : (cyclotomicLayerCharacter p (n + 1) g : ZMod (p ^ (n + 1))).val =
      1 + p ^ s * b) :
    FontaineWintenberger.ramificationOrder (R := O(n)) (L(n) ≃ₐ[Qp] L(n)) g =
      (p ^ s : ℕ) := by
  let π := cyclotomicUniformizer p n (FontaineWintenberger.spectralValuation Qp L(n))
  rw [FontaineWintenberger.ramificationOrder_eq_generator _
    (cyclotomicUniformizer_adjoin_spectral p n)]
  have hv : v(n) ((g • π - π : O(n)) : L(n)) = WithZero.exp (-(p ^ s : ℕ) : ℤ) := by
    have hcoe : ((g • π - π : O(n)) : L(n)) =
        g (cyclotomicLayerRoot p (n + 1)) - cyclotomicLayerRoot p (n + 1) := by
      change ((g • π : O(n)) : L(n)) - (π : L(n)) = _
      rw [FontaineWintenberger.coe_spectralIntegerRing_galois_smul]
      change g (cyclotomicLayerRoot p (n + 1) - 1) -
        (cyclotomicLayerRoot p (n + 1) - 1) = _
      rw [map_sub, map_one]
      ring
    rw [hcoe]
    exact normalizedValuation_cyclotomic_displacement_of_exponent p n s b hs hb g ha
  apply ENat.eq_of_forall_natCast_le_iff
  intro k
  change (k : ℕ∞) ≤ addVal O(n) (g • π - π) ↔ (k : ℕ∞) ≤ (p ^ s : ℕ)
  rw [← FontaineWintenberger.mem_maximalIdeal_pow_iff_addVal,
    FontaineWintenberger.mem_maximalIdeal_pow_iff_valuation (E := L(n)),
    ValuationSubring.algebraMap_apply, hv]
  simp
  norm_cast

/-- The intrinsic ramification order of a nonidentity automorphism is the
prime power specified by the p-adic order of its actual character minus one. -/
theorem ramificationOrder_cyclotomic (n : ℕ) (g : L(n) ≃ₐ[Qp] L(n)) (hg : g ≠ 1) :
    FontaineWintenberger.ramificationOrder (R := O(n)) (L(n) ≃ₐ[Qp] L(n)) g =
      (p ^ padicValNat p
        ((cyclotomicLayerCharacter p (n + 1) g : ZMod (p ^ (n + 1))).val - 1) : ℕ) := by
  have ha : cyclotomicLayerCharacter p (n + 1) g ≠ 1 := by
    intro h
    exact hg (cyclotomicLayerCharacter_injective p (n + 1)
      (h.trans (map_one _).symm))
  obtain ⟨b, hs, hb, ha⟩ := cyclotomic_exponent_decomposition p n _ ha
  exact ramificationOrder_cyclotomic_of_exponent p n _ b hs hb g ha

/-- The actual integer lower groups, expressed by the original finite
cyclotomic character, with the identity handled separately. -/
theorem mem_lowerRamificationGroup_cyclotomic_iff
    (n : ℕ) (m : ℤ) (g : L(n) ≃ₐ[Qp] L(n)) :
    g ∈ FontaineWintenberger.lowerRamificationGroup
        (L(n) ≃ₐ[Qp] L(n)) (IsLocalRing.maximalIdeal O(n)) m ↔
      g = 1 ∨ (m + 1).toNat ≤
        p ^ padicValNat p
          ((cyclotomicLayerCharacter p (n + 1) g : ZMod (p ^ (n + 1))).val - 1) := by
  by_cases hg : g = 1
  · subst g
    simp
  · rw [FontaineWintenberger.mem_lowerRamificationGroup_iff_le_order,
      ramificationOrder_cyclotomic p n g hg]
    simp only [hg, false_or, ENat.natCast_le_natCast]

/-- The actual real lower groups, with their closed break endpoints, are
computed by the original finite cyclotomic character. -/
theorem mem_lowerRamificationGroupReal_cyclotomic_iff
    (n : ℕ) (t : ℝ) (g : L(n) ≃ₐ[Qp] L(n)) :
    g ∈ FontaineWintenberger.lowerRamificationGroupReal
        (L(n) ≃ₐ[Qp] L(n)) (IsLocalRing.maximalIdeal O(n)) t ↔
      g = 1 ∨ t + 1 ≤
        ((p ^ padicValNat p
          ((cyclotomicLayerCharacter p (n + 1) g : ZMod (p ^ (n + 1))).val - 1) : ℕ) : ℝ) := by
  by_cases hg : g = 1
  · subst g
    simp
  · rw [FontaineWintenberger.mem_lowerRamificationGroupReal_iff_le_order,
      ramificationOrder_cyclotomic p n g hg]
    simp only [hg, false_or, ENat.toENNReal_coe, ENNReal.ofReal_le_natCast]

/-- Reduction of the actual finite character unit group has the expected
kernel index, including reduction to the trivial zeroth level. -/
theorem cyclotomicUnitReduction_ker_index (n r : ℕ) (hr : r ≤ n + 1) :
    (ZMod.unitsMap (pow_dvd_pow p hr)).ker.index = (p ^ r).totient := by
  have : NeZero (p ^ (n + 1)) := ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
  have : NeZero (p ^ r) := ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
  rw [Subgroup.index_ker,
    MonoidHom.range_eq_top.mpr (ZMod.unitsMap_surjective (pow_dvd_pow p hr)),
    Subgroup.card_top, Nat.card_eq_fintype_card, ZMod.card_units_eq_totient]

/-- Every positive-level principal-unit kernel has its exact cardinality
inside the original finite character unit group. -/
theorem cyclotomicUnitReduction_ker_card (n r : ℕ)
    (hr0 : 0 < r) (hr : r ≤ n + 1) :
    Nat.card (ZMod.unitsMap (pow_dvd_pow p hr)).ker = p ^ (n + 1 - r) := by
  have : NeZero (p ^ (n + 1)) := ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
  have : NeZero (p ^ r) := ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
  have hmul := Subgroup.card_ker_mul_card_of_surjective
    (ZMod.unitsMap_surjective (pow_dvd_pow p hr))
  simp only [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient] at hmul
  have hφ : (p ^ r).totient ≠ 0 := by
    rw [Nat.totient_prime_pow (Fact.out : p.Prime) hr0]
    exact mul_ne_zero (pow_ne_zero _ (Fact.out : p.Prime).ne_zero)
      (Nat.sub_ne_zero_of_lt (Fact.out : p.Prime).one_lt)
  apply mul_right_cancel₀ hφ
  rw [Nat.card_eq_fintype_card, hmul,
    Nat.totient_prime_pow (Fact.out : p.Prime) (by omega : 0 < n + 1),
    Nat.totient_prime_pow (Fact.out : p.Prime) hr0, ← mul_assoc, ← pow_add]
  congr 2
  omega

/-- The actual finite-unit reduction kernel is ordinary divisibility of
the canonical representative minus one; this also covers the identity. -/
theorem mem_cyclotomicUnitReduction_ker_iff (n r : ℕ) (hr : r ≤ n + 1)
    (a : (ZMod (p ^ (n + 1)))ˣ) :
    a ∈ (ZMod.unitsMap (pow_dvd_pow p hr)).ker ↔
      p ^ r ∣ (a : ZMod (p ^ (n + 1))).val - 1 := by
  have : NeZero (p ^ (n + 1)) := ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
  have : Fact (1 < p ^ (n + 1)) :=
    ⟨one_lt_pow₀ (Fact.out : p.Prime).one_lt (by omega)⟩
  have ht : 1 ≤ (a : ZMod (p ^ (n + 1))).val :=
    ZMod.val_pos.mpr (Units.ne_zero a)
  have hcast : ZMod.castHom (pow_dvd_pow p hr) (ZMod (p ^ r))
      (a : ZMod (p ^ (n + 1))) =
        ((a : ZMod (p ^ (n + 1))).val : ZMod (p ^ r)) := by
    calc
      _ = ZMod.castHom (pow_dvd_pow p hr) (ZMod (p ^ r))
          (((a : ZMod (p ^ (n + 1))).val : ℕ) : ZMod (p ^ (n + 1))) :=
        congrArg _ (ZMod.natCast_zmod_val _).symm
      _ = _ := map_natCast _ _
  have hsub : (((a : ZMod (p ^ (n + 1))).val - 1 : ℕ) : ZMod (p ^ r)) =
      ((a : ZMod (p ^ (n + 1))).val : ZMod (p ^ r)) - 1 := by
    rw [Nat.cast_sub ht, Nat.cast_one]
  rw [MonoidHom.mem_ker, Units.ext_iff]
  change ZMod.castHom (pow_dvd_pow p hr) (ZMod (p ^ r))
    (a : ZMod (p ^ (n + 1))) = 1 ↔ _
  rw [hcast, ← sub_eq_zero, ← hsub, ZMod.natCast_eq_zero_iff]

/-- At every integral cyclotomic threshold, the actual lower group is
the preimage of the canonical finite-unit reduction kernel. -/
theorem lowerRamificationGroup_cyclotomic_eq_comap_unitReduction
    (n r : ℕ) (hr : r ≤ n + 1) :
    FontaineWintenberger.lowerRamificationGroup
        (L(n) ≃ₐ[Qp] L(n)) (IsLocalRing.maximalIdeal O(n)) (((p ^ r : ℕ) : ℤ) - 1) =
      (ZMod.unitsMap (pow_dvd_pow p hr)).ker.comap
        (cyclotomicLayerCharacter p (n + 1)) := by
  have hN : 1 < p ^ (n + 1) := one_lt_pow₀ (Fact.out : p.Prime).one_lt (by omega)
  have : Fact (1 < p ^ (n + 1)) := ⟨hN⟩
  ext g
  rw [mem_lowerRamificationGroup_cyclotomic_iff, Subgroup.mem_comap,
    mem_cyclotomicUnitReduction_ker_iff p n r hr]
  simp only [sub_add_cancel, Int.toNat_natCast]
  by_cases hg : g = 1
  · subst g
    simp [ZMod.val_one]
  · have ha : cyclotomicLayerCharacter p (n + 1) g ≠ 1 := by
      intro h
      exact hg (cyclotomicLayerCharacter_injective p (n + 1)
        (h.trans (map_one _).symm))
    have hval : (cyclotomicLayerCharacter p (n + 1) g : ZMod (p ^ (n + 1))).val ≠ 1 := by
      intro h
      exact ha (Units.ext ((ZMod.val_eq_one hN _).mp h))
    have hpos : 0 < (cyclotomicLayerCharacter p (n + 1) g : ZMod (p ^ (n + 1))).val :=
      ZMod.val_pos.mpr (Units.ne_zero _)
    have hd : (cyclotomicLayerCharacter p (n + 1) g : ZMod (p ^ (n + 1))).val - 1 ≠ 0 := by
      omega
    simp only [hg, false_or]
    rw [pow_le_pow_iff_right₀ (Fact.out : p.Prime).one_lt,
      Nat.pow_dvd_iff_le_padicValNat (Fact.out : p.Prime).ne_one hd]

/-- The exact full index of an actual cyclotomic lower group at a
prime-power threshold. -/
theorem lowerRamificationGroup_cyclotomic_index (n r : ℕ) (hr : r ≤ n + 1) :
    (FontaineWintenberger.lowerRamificationGroup
      (L(n) ≃ₐ[Qp] L(n)) (IsLocalRing.maximalIdeal O(n)) (((p ^ r : ℕ) : ℤ) - 1)).index =
        (p ^ r).totient := by
  rw [lowerRamificationGroup_cyclotomic_eq_comap_unitReduction p n r hr,
    Subgroup.index_comap_of_surjective _ (cyclotomicLayerCharacter_surjective p (n + 1)),
    cyclotomicUnitReduction_ker_index p n r hr]

/-- The actual inertia subgroup of every positive rational cyclotomic
layer is the whole original Galois group. -/
theorem lowerRamificationGroup_cyclotomic_zero (n : ℕ) :
    FontaineWintenberger.lowerRamificationGroup
      (L(n) ≃ₐ[Qp] L(n)) (IsLocalRing.maximalIdeal O(n)) 0 = ⊤ := by
  apply Subgroup.index_eq_one.mp
  simpa only [pow_zero, Nat.cast_one, sub_self, Nat.totient_one] using
    lowerRamificationGroup_cyclotomic_index p n 0 (by omega)

/-- The actual finite character maps a lower threshold group onto the
canonical finite-unit reduction kernel. -/
theorem lowerRamificationGroup_cyclotomic_map_character (n r : ℕ) (hr : r ≤ n + 1) :
    (FontaineWintenberger.lowerRamificationGroup
      (L(n) ≃ₐ[Qp] L(n)) (IsLocalRing.maximalIdeal O(n)) (((p ^ r : ℕ) : ℤ) - 1)).map
        (cyclotomicLayerCharacter p (n + 1)) =
      (ZMod.unitsMap (pow_dvd_pow p hr)).ker := by
  rw [lowerRamificationGroup_cyclotomic_eq_comap_unitReduction p n r hr,
    Subgroup.map_comap_eq,
    MonoidHom.range_eq_top.mpr (cyclotomicLayerCharacter_surjective p (n + 1)), top_inf_eq]

/-- Exact cardinalities of the original lower threshold groups. -/
theorem lowerRamificationGroup_cyclotomic_card (n r : ℕ)
    (hr0 : 0 < r) (hr : r ≤ n + 1) :
    Nat.card (FontaineWintenberger.lowerRamificationGroup
      (L(n) ≃ₐ[Qp] L(n)) (IsLocalRing.maximalIdeal O(n)) (((p ^ r : ℕ) : ℤ) - 1)) =
        p ^ (n + 1 - r) := by
  calc
    _ = Nat.card ((FontaineWintenberger.lowerRamificationGroup
        (L(n) ≃ₐ[Qp] L(n)) (IsLocalRing.maximalIdeal O(n))
          (((p ^ r : ℕ) : ℤ) - 1)).map (cyclotomicLayerCharacter p (n + 1))) :=
      (Subgroup.card_map_of_injective (cyclotomicLayerCharacter_injective p (n + 1))).symm
    _ = _ := by
      rw [lowerRamificationGroup_cyclotomic_map_character p n r hr,
        cyclotomicUnitReduction_ker_card p n r hr0 hr]

/-- Real and integer numbering agree at every cyclotomic lower threshold. -/
theorem lowerRamificationGroupReal_cyclotomic_threshold (n r : ℕ) :
    FontaineWintenberger.lowerRamificationGroupReal
        (L(n) ≃ₐ[Qp] L(n)) (IsLocalRing.maximalIdeal O(n)) (((p ^ r : ℕ) : ℝ) - 1) =
      FontaineWintenberger.lowerRamificationGroup
        (L(n) ≃ₐ[Qp] L(n)) (IsLocalRing.maximalIdeal O(n)) (((p ^ r : ℕ) : ℤ) - 1) := by
  ext g
  rw [mem_lowerRamificationGroupReal_cyclotomic_iff, mem_lowerRamificationGroup_cyclotomic_iff]
  simp only [sub_add_cancel, Int.toNat_natCast, Nat.cast_le]

/-- The actual real lower group is constant between consecutive
prime-power thresholds, open on the left and closed on the right. -/
theorem lowerRamificationGroupReal_cyclotomic_constant (n r : ℕ) {t : ℝ}
    (ht0 : ((p ^ r : ℕ) : ℝ) - 1 < t)
    (ht1 : t ≤ ((p ^ (r + 1) : ℕ) : ℝ) - 1) :
    FontaineWintenberger.lowerRamificationGroupReal
        (L(n) ≃ₐ[Qp] L(n)) (IsLocalRing.maximalIdeal O(n)) t =
      FontaineWintenberger.lowerRamificationGroupReal
        (L(n) ≃ₐ[Qp] L(n)) (IsLocalRing.maximalIdeal O(n))
          (((p ^ (r + 1) : ℕ) : ℝ) - 1) := by
  ext g
  rw [mem_lowerRamificationGroupReal_cyclotomic_iff,
    mem_lowerRamificationGroupReal_cyclotomic_iff]
  simp only [sub_add_cancel]
  by_cases hg : g = 1
  · simp only [hg, true_or]
  · simp only [hg, false_or]
    constructor
    · intro h
      have hpow : p ^ r < p ^ padicValNat p
          ((cyclotomicLayerCharacter p (n + 1) g : ZMod (p ^ (n + 1))).val - 1) := by
        exact_mod_cast (show ((p ^ r : ℕ) : ℝ) <
          ((p ^ padicValNat p
            ((cyclotomicLayerCharacter p (n + 1) g : ZMod (p ^ (n + 1))).val - 1) : ℕ) : ℝ) by
              linarith)
      have hj := (pow_lt_pow_iff_right₀ (Fact.out : p.Prime).one_lt).mp hpow
      exact_mod_cast ((pow_le_pow_iff_right₀ (Fact.out : p.Prime).one_lt).mpr
        (show r + 1 ≤ _ by omega))
    · intro h
      linarith

/-- Exact actual lower-group cardinality on each cyclotomic interval. -/
theorem lowerRamificationGroupReal_cyclotomic_card_on (n r : ℕ) (hr : r ≤ n) {t : ℝ}
    (ht0 : ((p ^ r : ℕ) : ℝ) - 1 < t)
    (ht1 : t ≤ ((p ^ (r + 1) : ℕ) : ℝ) - 1) :
    Nat.card (FontaineWintenberger.lowerRamificationGroupReal
      (L(n) ≃ₐ[Qp] L(n)) (IsLocalRing.maximalIdeal O(n)) t) = p ^ (n - r) := by
  rw [lowerRamificationGroupReal_cyclotomic_constant p n r ht0 ht1,
    lowerRamificationGroupReal_cyclotomic_threshold,
    lowerRamificationGroup_cyclotomic_card p n (r + 1) (by omega) (by omega)]
  congr 1
  omega

set_option maxHeartbeats 1000000 in
-- The explicit ramification intervals require substantial integral and cardinality simplification.
/-- Each consecutive cyclotomic lower interval has actual Herbrand
length one, at every prime and including the first interval. -/
theorem integral_cyclotomic_lower_slope (n r : ℕ) (hr : r ≤ n) :
    (∫ t in (((p ^ r : ℕ) : ℝ) - 1)..(((p ^ (r + 1) : ℕ) : ℝ) - 1),
      (Nat.card (FontaineWintenberger.lowerRamificationGroupReal
        (L(n) ≃ₐ[Qp] L(n)) (IsLocalRing.maximalIdeal O(n)) t) : ℝ) /
        Nat.card (FontaineWintenberger.lowerRamificationGroup
          (L(n) ≃ₐ[Qp] L(n)) (IsLocalRing.maximalIdeal O(n)) 0)) = 1 := by
  have hab : ((p ^ r : ℕ) : ℝ) - 1 ≤ ((p ^ (r + 1) : ℕ) : ℝ) - 1 := by
    have hpow : p ^ r ≤ p ^ (r + 1) :=
      (pow_le_pow_iff_right₀ (Fact.out : p.Prime).one_lt).mpr (by omega)
    exact sub_le_sub_right (by exact_mod_cast hpow) 1
  have heq :
      (∫ t in (((p ^ r : ℕ) : ℝ) - 1)..(((p ^ (r + 1) : ℕ) : ℝ) - 1),
        (Nat.card (FontaineWintenberger.lowerRamificationGroupReal
          (L(n) ≃ₐ[Qp] L(n)) (IsLocalRing.maximalIdeal O(n)) t) : ℝ) /
            Nat.card (FontaineWintenberger.lowerRamificationGroup
              (L(n) ≃ₐ[Qp] L(n)) (IsLocalRing.maximalIdeal O(n)) 0)) =
      ∫ _t in (((p ^ r : ℕ) : ℝ) - 1)..(((p ^ (r + 1) : ℕ) : ℝ) - 1),
        (p ^ (n - r) : ℕ) /
          (Nat.card (FontaineWintenberger.lowerRamificationGroup
            (L(n) ≃ₐ[Qp] L(n)) (IsLocalRing.maximalIdeal O(n)) 0) : ℝ) := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [] with t
    intro ht
    rw [Set.uIoc_of_le hab] at ht
    rw [lowerRamificationGroupReal_cyclotomic_card_on p n r hr ht.1 ht.2]
  rw [heq, intervalIntegral.integral_const, smul_eq_mul,
    lowerRamificationGroup_cyclotomic_zero, Subgroup.card_top,
    card_cyclotomicLayer_galois, Nat.totient_prime_pow (Fact.out : p.Prime) (by omega)]
  rw [show n + 1 - 1 = n by omega]
  simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_sub (Fact.out : p.Prime).one_le,
    Nat.cast_one]
  have hp : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hden : (p : ℝ) ^ n * ((p : ℝ) - 1) ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ (by linarith)) (by linarith)
  rw [← mul_div_assoc, div_eq_one_iff_eq hden]
  have hpower : (p : ℝ) ^ r * (p : ℝ) ^ (n - r) = (p : ℝ) ^ n := by
    rw [← pow_add, Nat.add_sub_of_le hr]
  calc
    _ = ((p : ℝ) ^ r * (p : ℝ) ^ (n - r)) * ((p : ℝ) - 1) := by
      rw [pow_succ]
      ring
    _ = _ := by rw [hpower]

set_option maxHeartbeats 1000000 in
-- The explicit ramification intervals require substantial integral and cardinality simplification.
/-- The actual integral-defined Herbrand function sends every
prime-power lower threshold to its integer upper threshold. -/
theorem herbrandFunction_cyclotomic_threshold (n r : ℕ) (hr : r ≤ n + 1) :
    FontaineWintenberger.herbrandFunction (R := O(n)) (L(n) ≃ₐ[Qp] L(n))
      (((p ^ r : ℕ) : ℝ) - 1) = r := by
  induction r with
  | zero =>
    simp only [pow_zero, Nat.cast_one, sub_self, Nat.cast_zero]
    exact FontaineWintenberger.herbrandFunction_of_nonpos _ le_rfl
  | succ r ih =>
    have hrn : r ≤ n := by omega
    have ha : 0 ≤ ((p ^ r : ℕ) : ℝ) - 1 := by
      have hpow : 1 ≤ p ^ r := Nat.one_le_iff_ne_zero.mpr
        (pow_ne_zero r (Fact.out : p.Prime).ne_zero)
      exact sub_nonneg.mpr (by exact_mod_cast hpow)
    have hb : 0 < ((p ^ (r + 1) : ℕ) : ℝ) - 1 := by
      have hpow : 1 < p ^ (r + 1) :=
        one_lt_pow₀ (Fact.out : p.Prime).one_lt (by omega)
      exact sub_pos.mpr (by exact_mod_cast hpow)
    let f : ℝ → ℝ := fun t =>
      (Nat.card (FontaineWintenberger.lowerRamificationGroupReal
        (L(n) ≃ₐ[Qp] L(n)) (IsLocalRing.maximalIdeal O(n)) t) : ℝ) /
          Nat.card (FontaineWintenberger.lowerRamificationGroup
            (L(n) ≃ₐ[Qp] L(n)) (IsLocalRing.maximalIdeal O(n)) 0)
    have hfa : FontaineWintenberger.herbrandFunction (R := O(n))
        (L(n) ≃ₐ[Qp] L(n)) (((p ^ r : ℕ) : ℝ) - 1) =
          ∫ t in (0 : ℝ)..(((p ^ r : ℕ) : ℝ) - 1), f t := by
      by_cases ha0 : ((p ^ r : ℕ) : ℝ) - 1 ≤ 0
      · have hzero : ((p ^ r : ℕ) : ℝ) - 1 = 0 := le_antisymm ha0 ha
        rw [hzero]
        simp [FontaineWintenberger.herbrandFunction]
      · rw [FontaineWintenberger.herbrandFunction, ite_eq_right ha0]
    have hfb : FontaineWintenberger.herbrandFunction (R := O(n))
        (L(n) ≃ₐ[Qp] L(n)) (((p ^ (r + 1) : ℕ) : ℝ) - 1) =
          ∫ t in (0 : ℝ)..(((p ^ (r + 1) : ℕ) : ℝ) - 1), f t := by
      rw [FontaineWintenberger.herbrandFunction, ite_eq_right (not_le.mpr hb)]
    have hadd := intervalIntegral.integral_add_adjacent_intervals
      ((FontaineWintenberger.intervalIntegrable_card_lowerRamificationGroupReal
        (R := O(n)) (L(n) ≃ₐ[Qp] L(n)) 0 (((p ^ r : ℕ) : ℝ) - 1)).div_const
          (Nat.card (FontaineWintenberger.lowerRamificationGroup
            (L(n) ≃ₐ[Qp] L(n)) (IsLocalRing.maximalIdeal O(n)) 0) : ℝ))
      ((FontaineWintenberger.intervalIntegrable_card_lowerRamificationGroupReal
        (R := O(n)) (L(n) ≃ₐ[Qp] L(n)) (((p ^ r : ℕ) : ℝ) - 1)
          (((p ^ (r + 1) : ℕ) : ℝ) - 1)).div_const
          (Nat.card (FontaineWintenberger.lowerRamificationGroup
            (L(n) ≃ₐ[Qp] L(n)) (IsLocalRing.maximalIdeal O(n)) 0) : ℝ))
    change (∫ t in (0 : ℝ)..(((p ^ r : ℕ) : ℝ) - 1), f t) +
      (∫ t in (((p ^ r : ℕ) : ℝ) - 1)..(((p ^ (r + 1) : ℕ) : ℝ) - 1), f t) =
        (∫ t in (0 : ℝ)..(((p ^ (r + 1) : ℕ) : ℝ) - 1), f t) at hadd
    rw [← hfa, ← hfb, ih (by omega)] at hadd
    have hstep := integral_cyclotomic_lower_slope p n r hrn
    change (∫ t in (((p ^ r : ℕ) : ℝ) - 1)..(((p ^ (r + 1) : ℕ) : ℝ) - 1), f t) = 1 at hstep
    rw [hstep] at hadd
    simpa only [Nat.cast_add, Nat.cast_one] using hadd.symm

set_option maxHeartbeats 1000000 in
-- The explicit ramification intervals require substantial integral and cardinality simplification.
/-- The actual upper group on each unit upper interval is the preimage
of the canonical finite-character principal-unit kernel. -/
theorem upperRamificationGroup_cyclotomic_eq_comap_unitReduction
    (n r : ℕ) (hr : r ≤ n) {u : ℝ} (hu0 : (r : ℝ) < u) (hu1 : u ≤ (r : ℝ) + 1) :
    FontaineWintenberger.upperRamificationGroup (R := O(n)) (L(n) ≃ₐ[Qp] L(n)) u =
      (ZMod.unitsMap (pow_dvd_pow p (by omega : r + 1 ≤ n + 1))).ker.comap
        (cyclotomicLayerCharacter p (n + 1)) := by
  have hφ0 := herbrandFunction_cyclotomic_threshold p n r (by omega)
  have hφ1 := herbrandFunction_cyclotomic_threshold p n (r + 1) (by omega)
  have ht0 : -1 ≤ ((p ^ r : ℕ) : ℝ) - 1 := by
    linarith [Nat.cast_nonneg (α := ℝ) (p ^ r)]
  have ht1 : -1 ≤ ((p ^ (r + 1) : ℕ) : ℝ) - 1 := by
    linarith [Nat.cast_nonneg (α := ℝ) (p ^ (r + 1))]
  have hψ := FontaineWintenberger.inverseHerbrandFunction_mem_Ici (R := O(n))
    (L(n) ≃ₐ[Qp] L(n)) u
  have hinv := FontaineWintenberger.herbrandFunction_inverseHerbrandFunction (R := O(n))
    (L(n) ≃ₐ[Qp] L(n)) (by linarith [Nat.cast_nonneg (α := ℝ) r] : -1 ≤ u)
  have hψ0 : ((p ^ r : ℕ) : ℝ) - 1 <
      FontaineWintenberger.inverseHerbrandFunction (R := O(n)) (L(n) ≃ₐ[Qp] L(n)) u := by
    apply ((FontaineWintenberger.strictMonoOn_herbrandFunction (R := O(n))
      (L(n) ≃ₐ[Qp] L(n))).lt_iff_lt ht0 hψ).mp
    rw [hφ0, hinv]
    exact hu0
  have hψ1 : FontaineWintenberger.inverseHerbrandFunction (R := O(n))
      (L(n) ≃ₐ[Qp] L(n)) u ≤ ((p ^ (r + 1) : ℕ) : ℝ) - 1 := by
    apply ((FontaineWintenberger.strictMonoOn_herbrandFunction (R := O(n))
      (L(n) ≃ₐ[Qp] L(n))).le_iff_le hψ ht1).mp
    rw [hinv, hφ1]
    simpa only [Nat.cast_add, Nat.cast_one] using hu1
  rw [FontaineWintenberger.upperRamificationGroup,
    lowerRamificationGroupReal_cyclotomic_constant p n r hψ0 hψ1,
    lowerRamificationGroupReal_cyclotomic_threshold,
    lowerRamificationGroup_cyclotomic_eq_comap_unitReduction p n (r + 1) (by omega)]

/-- The actual finite upper index is the expected prime-power totient
on every closed upper interval. -/
theorem upperRamificationGroup_cyclotomic_index
    (n r : ℕ) (hr : r ≤ n) {u : ℝ} (hu0 : (r : ℝ) < u) (hu1 : u ≤ (r : ℝ) + 1) :
    (FontaineWintenberger.upperRamificationGroup (R := O(n)) (L(n) ≃ₐ[Qp] L(n)) u).index =
      (p ^ (r + 1)).totient := by
  rw [upperRamificationGroup_cyclotomic_eq_comap_unitReduction p n r hr hu0 hu1,
    Subgroup.index_comap_of_surjective _ (cyclotomicLayerCharacter_surjective p (n + 1)),
    cyclotomicUnitReduction_ker_index p n (r + 1) (by omega)]

/-- The exact cardinality of each original finite cyclotomic upper group. -/
theorem upperRamificationGroup_cyclotomic_card
    (n r : ℕ) (hr : r ≤ n) {u : ℝ} (hu0 : (r : ℝ) < u) (hu1 : u ≤ (r : ℝ) + 1) :
    Nat.card (FontaineWintenberger.upperRamificationGroup
      (R := O(n)) (L(n) ≃ₐ[Qp] L(n)) u) = p ^ (n - r) := by
  rw [upperRamificationGroup_cyclotomic_eq_comap_unitReduction p n r hr hu0 hu1,
    ← lowerRamificationGroup_cyclotomic_eq_comap_unitReduction p n (r + 1) (by omega),
    lowerRamificationGroup_cyclotomic_card p n (r + 1) (by omega) (by omega)]
  congr 1
  omega

/-- The actual upper inertia group is full, including the trivial first
dyadic layer. -/
theorem upperRamificationGroup_cyclotomic_zero (n : ℕ) :
    FontaineWintenberger.upperRamificationGroup (R := O(n)) (L(n) ≃ₐ[Qp] L(n)) 0 = ⊤ := by
  simpa only [FontaineWintenberger.upperRamificationGroup_zero,
    FontaineWintenberger.lowerRamificationGroup_zero] using
      lowerRamificationGroup_cyclotomic_zero p n

/-- The actual finite upper group is trivial after the final upper break. -/
theorem upperRamificationGroup_cyclotomic_eq_bot (n : ℕ) {u : ℝ} (hu : (n : ℝ) < u) :
    FontaineWintenberger.upperRamificationGroup (R := O(n)) (L(n) ≃ₐ[Qp] L(n)) u = ⊥ := by
  by_cases hu1 : u ≤ (n : ℝ) + 1
  · apply Subgroup.card_eq_one.mp
    simpa only [Nat.sub_self, pow_zero] using
      upperRamificationGroup_cyclotomic_card p n n le_rfl hu hu1
  · have ht : FontaineWintenberger.upperRamificationGroup (R := O(n))
        (L(n) ≃ₐ[Qp] L(n)) ((n : ℝ) + 1) = ⊥ := by
      apply Subgroup.card_eq_one.mp
      simpa only [Nat.sub_self, pow_zero] using
        upperRamificationGroup_cyclotomic_card p n n le_rfl
          (by linarith : (n : ℝ) < (n : ℝ) + 1) le_rfl
    apply le_bot_iff.mp
    rw [← ht]
    exact FontaineWintenberger.upperRamificationGroup_antitoneOn (R := O(n))
      (L(n) ≃ₐ[Qp] L(n))
      (by linarith [Nat.cast_nonneg (α := ℝ) n] : -1 ≤ (n : ℝ) + 1)
      (by linarith [Nat.cast_nonneg (α := ℝ) n] : -1 ≤ u) (le_of_not_ge hu1)

end FalseTateExtension

end
