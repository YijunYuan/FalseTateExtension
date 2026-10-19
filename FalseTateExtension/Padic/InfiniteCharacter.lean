/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FalseTateExtension.Padic.FiniteCharacter
public import FalseTateExtension.CyclotomicImage

/-!
# The actual infinite rational cyclotomic character

Finite cyclotomic characters and ordinary restriction make the closed fibers
of every finite residue coordinate nonempty. Compactness of the actual Krull
Galois group yields surjectivity of its canonical p-adic character and hence
a topological group isomorphism with the p-adic units. The unbounded degrees
of the actual finite layers also prove that the extension has infinite degree.

This proves blueprint `ft:infinite-cyclotomic-character`.
-/

@[expose] public section

noncomputable section

namespace FalseTateExtension

variable (p : ℕ) [Fact p.Prime]

/-- Ordinary restriction from the actual infinite cyclotomic field to one
of its original finite layers. -/
def cyclotomicLayerRestriction (m : ℕ) :
    (cyclotomicExtension (K := Padic p) p ≃ₐ[Padic p] cyclotomicExtension (K := Padic p) p) →*
      (cyclotomicLayer (K := Padic p) p m ≃ₐ[Padic p] cyclotomicLayer (K := Padic p) p m) := by
  let : Algebra (cyclotomicLayer (K := Padic p) p m) (cyclotomicExtension (K := Padic p) p) :=
    RingHom.toAlgebra (Subsemiring.inclusion (cyclotomicLayer_le_cyclotomicExtension p m))
  let : IsScalarTower (Padic p) (cyclotomicLayer (K := Padic p) p m)
      (cyclotomicExtension (K := Padic p) p) :=
    IsScalarTower.of_algebraMap_eq (congrFun rfl)
  exact AlgEquiv.restrictNormalHom (cyclotomicLayer (K := Padic p) p m)

/-- Restriction uses the original inclusion into the infinite field. -/
theorem cyclotomicLayerRestriction_commutes (m : ℕ)
    (g : cyclotomicExtension (K := Padic p) p ≃ₐ[Padic p] cyclotomicExtension (K := Padic p) p)
    (x : cyclotomicLayer (K := Padic p) p m) :
    IntermediateField.inclusion (cyclotomicLayer_le_cyclotomicExtension p m)
        (cyclotomicLayerRestriction p m g x) =
      g (IntermediateField.inclusion (cyclotomicLayer_le_cyclotomicExtension p m) x) := by
  let : Algebra (cyclotomicLayer (K := Padic p) p m) (cyclotomicExtension (K := Padic p) p) :=
    RingHom.toAlgebra (Subsemiring.inclusion (cyclotomicLayer_le_cyclotomicExtension p m))
  let : IsScalarTower (Padic p) (cyclotomicLayer (K := Padic p) p m)
      (cyclotomicExtension (K := Padic p) p) :=
    IsScalarTower.of_algebraMap_eq (congrFun rfl)
  exact AlgEquiv.restrictNormal_commutes g (cyclotomicLayer (K := Padic p) p m) x

/-- Every actual finite cyclotomic automorphism extends to the infinite
cyclotomic extension. -/
theorem cyclotomicLayerRestriction_surjective (m : ℕ) :
    Function.Surjective (cyclotomicLayerRestriction p m) := by
  let : Algebra (cyclotomicLayer (K := Padic p) p m) (cyclotomicExtension (K := Padic p) p) :=
    RingHom.toAlgebra (Subsemiring.inclusion (cyclotomicLayer_le_cyclotomicExtension p m))
  let : IsScalarTower (Padic p) (cyclotomicLayer (K := Padic p) p m)
      (cyclotomicExtension (K := Padic p) p) :=
    IsScalarTower.of_algebraMap_eq (congrFun rfl)
  exact AlgEquiv.restrictNormalHom_surjective (cyclotomicExtension (K := Padic p) p)

/-- Ordinary finite-layer restriction is continuous for the actual Krull
topologies. The intermediate field in the infinite field is the original
inclusion's field range. -/
theorem continuous_cyclotomicLayerRestriction (m : ℕ) :
    Continuous (cyclotomicLayerRestriction p m) := by
  let i := IntermediateField.inclusion (cyclotomicLayer_le_cyclotomicExtension (K := Padic p) p m)
  let e := i.equivFieldRange
  have : Module.Finite (Padic p) i.fieldRange := Module.Finite.equiv e.toLinearEquiv
  have : IsGalois (Padic p) i.fieldRange := IsGalois.of_algEquiv e
  have hc : Continuous (fun g : cyclotomicExtension (K := Padic p) p ≃ₐ[Padic p]
      cyclotomicExtension (K := Padic p) p ↦
      e.symm.autCongr (AlgEquiv.restrictNormalHom i.fieldRange g)) :=
    continuous_of_discreteTopology.comp (InfiniteGalois.restrictNormalHom_continuous i.fieldRange)
  convert hc using 1
  funext g
  apply AlgEquiv.ext
  intro x
  apply (show Function.Injective i from i.injective)
  rw [cyclotomicLayerRestriction_commutes]
  change g (i x) = i (e.symm ((g.restrictNormal i.fieldRange) (e x)))
  have he (y : i.fieldRange) : i (e.symm y) = y := by
    change (e (e.symm y) : cyclotomicExtension (K := Padic p) p) = _
    rw [e.apply_symm_apply]
  rw [he]
  exact (AlgEquiv.restrictNormal_commutes g i.fieldRange (e x)).symm

/-- The finite character is exactly the corresponding residue coordinate
of the existing canonical infinite character. -/
theorem cyclotomicLayerCharacter_restrict (m : ℕ)
    (g : cyclotomicExtension (K := Padic p) p ≃ₐ[Padic p] cyclotomicExtension (K := Padic p) p) :
    cyclotomicLayerCharacter p m (cyclotomicLayerRestriction p m g) =
      Units.map (PadicInt.toZModPow m).toMonoidHom (cyclotomicExtensionCharacter p g) := by
  apply cyclotomicLayerCharacter_unique p m
  let i := IntermediateField.inclusion (cyclotomicLayer_le_cyclotomicExtension (K := Padic p) p m)
  apply i.injective
  rw [map_pow]
  change i (cyclotomicLayerRestriction p m g (cyclotomicLayerRoot p m)) =
    cyclotomicRootOfUnity p m ^
      (PadicInt.toZModPow m (cyclotomicExtensionCharacter p g : PadicInt p)).val
  rw [cyclotomicLayerRestriction_commutes]
  exact cyclotomicExtensionCharacter_spec p m g

/-- The actual residue-coordinate fiber of the existing infinite character. -/
def cyclotomicCharacterFiber (u : (PadicInt p)ˣ) (m : ℕ) :
    Set (cyclotomicExtension (K := Padic p) p ≃ₐ[Padic p] cyclotomicExtension (K := Padic p) p) :=
  {g | PadicInt.toZModPow m (cyclotomicExtensionCharacter p g : PadicInt p) =
    PadicInt.toZModPow m (u : PadicInt p)}

/-- The finite coordinate fibers are closed in the actual Krull topology. -/
theorem isClosed_cyclotomicCharacterFiber (u : (PadicInt p)ˣ) (m : ℕ) :
    IsClosed (cyclotomicCharacterFiber p u m) := by
  have hc : Continuous (fun g ↦
      (cyclotomicLayerCharacter p m (cyclotomicLayerRestriction p m g) : ZMod (p ^ m))) :=
    (Units.continuous_val.comp (continuous_of_discreteTopology :
      Continuous (cyclotomicLayerCharacter p m))).comp (continuous_cyclotomicLayerRestriction p m)
  have he : (fun g ↦ (cyclotomicLayerCharacter p m (cyclotomicLayerRestriction p m g) :
      ZMod (p ^ m))) =
      (fun g ↦ PadicInt.toZModPow m (cyclotomicExtensionCharacter p g : PadicInt p)) := by
    funext g
    exact congrArg Units.val (cyclotomicLayerCharacter_restrict p m g)
  rw [he] at hc
  exact isClosed_eq hc continuous_const

/-- Finite-character surjectivity and actual normal restriction make each
residue fiber nonempty. -/
theorem cyclotomicCharacterFiber_nonempty (u : (PadicInt p)ˣ) (m : ℕ) :
    (cyclotomicCharacterFiber p u m).Nonempty := by
  obtain ⟨h, hh⟩ := cyclotomicLayerCharacter_surjective p m
    (Units.map (PadicInt.toZModPow m).toMonoidHom u)
  obtain ⟨g, rfl⟩ := cyclotomicLayerRestriction_surjective p m h
  refine ⟨g, ?_⟩
  change PadicInt.toZModPow m (cyclotomicExtensionCharacter p g : PadicInt p) = _
  rw [cyclotomicLayerCharacter_restrict p m g] at hh
  exact congrArg Units.val hh

/-- The residue fibers are nested, by the canonical reduction compatibility. -/
theorem cyclotomicCharacterFiber_succ_subset (u : (PadicInt p)ˣ) (m : ℕ) :
    cyclotomicCharacterFiber p u (m + 1) ⊆ cyclotomicCharacterFiber p u m := by
  intro g hg
  let f := ZMod.castHom (pow_dvd_pow p (Nat.le_succ m)) (ZMod (p ^ m))
  have hf (x : PadicInt p) : f (PadicInt.toZModPow (m + 1) x) = PadicInt.toZModPow m x :=
    congrArg (fun h : PadicInt p →+* ZMod (p ^ m) ↦ h x)
      (PadicInt.zmod_cast_comp_toZModPow m (m + 1) (Nat.le_succ m))
  change PadicInt.toZModPow m (cyclotomicExtensionCharacter p g : PadicInt p) = _
  exact (hf _).symm.trans ((congrArg f hg).trans (hf _))

/-- Compactness of the actual Krull Galois group produces an automorphism
realizing every p-adic unit under the existing canonical character. -/
theorem cyclotomicExtensionCharacter_surjective_padic :
    Function.Surjective (cyclotomicExtensionCharacter (K := Padic p) p) := by
  intro u
  obtain ⟨g, hg⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
    (cyclotomicCharacterFiber p u) (cyclotomicCharacterFiber_succ_subset p u)
    (cyclotomicCharacterFiber_nonempty p u)
    ((isClosed_cyclotomicCharacterFiber p u 0).isCompact)
    (isClosed_cyclotomicCharacterFiber p u)
  refine ⟨g, ?_⟩
  apply Units.ext
  apply PadicInt.ext_of_toZModPow.mp
  intro m
  exact Set.mem_iInter.mp hg m

/-- The canonical infinite rational cyclotomic character is an isomorphism
of the actual Krull Galois group with the p-adic units, with continuous inverse. -/
def cyclotomicExtensionGaloisEquivUnits :
    (cyclotomicExtension (K := Padic p) p ≃ₐ[Padic p] cyclotomicExtension (K := Padic p) p) ≃ₜ*
      (PadicInt p)ˣ := by
  let e := MulEquiv.ofBijective (cyclotomicExtensionCharacter (K := Padic p) p)
    ⟨cyclotomicExtensionCharacter_injective p, cyclotomicExtensionCharacter_surjective_padic p⟩
  have hc : Continuous e := continuous_cyclotomicExtensionCharacter p
  have hi : Continuous e.symm :=
    (isClosedEmbedding_cyclotomicExtensionCharacter (K := Padic p) p).isEmbedding.continuous_iff.mpr
      (by
        change Continuous (fun u ↦ cyclotomicExtensionCharacter p (e.symm u))
        have he : (fun u ↦ cyclotomicExtensionCharacter p (e.symm u)) = id :=
          funext e.apply_symm_apply
        rw [he]
        exact continuous_id)
  exact
    { e with
      continuous_toFun := hc
      continuous_invFun := hi }

/-- The topological isomorphism evaluates as the original canonical character. -/
@[simp]
theorem cyclotomicExtensionGaloisEquivUnits_apply
    (g : cyclotomicExtension (K := Padic p) p ≃ₐ[Padic p] cyclotomicExtension (K := Padic p) p) :
    cyclotomicExtensionGaloisEquivUnits p g = cyclotomicExtensionCharacter p g := rfl

/-- The degrees of the actual rational cyclotomic layers are unbounded. -/
theorem cyclotomicLayer_padic_degrees_unbounded (N : ℕ) :
    ∃ m, N < Module.finrank (Padic p) (cyclotomicLayer (K := Padic p) p m) := by
  refine ⟨N + 1, ?_⟩
  rw [finrank_cyclotomicLayer_padic, Nat.totient_prime_pow_succ (Fact.out : p.Prime)]
  exact (show N < p ^ N from Nat.lt_pow_self (Fact.out : p.Prime).one_lt).trans_le
    (Nat.le_mul_of_pos_right _ (by have := (Fact.out : p.Prime).two_le; omega))

/-- The actual infinite rational cyclotomic extension is not finite dimensional. -/
theorem not_finiteDimensional_cyclotomicExtension_padic :
    ¬FiniteDimensional (Padic p) (cyclotomicExtension (K := Padic p) p) := by
  intro h
  let := h
  obtain ⟨m, hm⟩ := cyclotomicLayer_padic_degrees_unbounded p
    (Module.finrank (Padic p) (cyclotomicExtension (K := Padic p) p))
  exact (not_lt_of_ge (IntermediateField.finrank_le_of_le_right
    (cyclotomicLayer_le_cyclotomicExtension p m))) hm

end FalseTateExtension

end
