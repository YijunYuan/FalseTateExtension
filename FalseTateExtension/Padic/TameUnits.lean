module

public import Mathlib.NumberTheory.Padics.Hensel
public import Mathlib.NumberTheory.Padics.RingHoms
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import Mathlib.FieldTheory.Finite.Basic

/-!
# Canonical tame units of the p-adic integers

Simple-root Hensel lifting constructs the multiplicative residue section
and the actual cyclic subgroup of order p-1.
-/

@[expose] public section

noncomputable section

namespace PadicInt

variable {p : ℕ} [Fact p.Prime]

/-- Reduction vanishes exactly on the original open maximal-ideal ball. -/
theorem toZMod_eq_zero_iff_norm_lt_one (x : PadicInt p) :
    toZMod x = 0 ↔ ‖x‖ < 1 := by
  rw [← RingHom.mem_ker, ker_toZMod, maximalIdeal_eq_span_p,
    Ideal.mem_span_singleton, ← norm_lt_one_iff_dvd]

/-- Nonzero residue is exactly unit norm in the original p-adic ring. -/
theorem norm_eq_one_iff_toZMod_ne_zero (x : PadicInt p) :
    ‖x‖ = 1 ↔ toZMod x ≠ 0 := by
  constructor
  · intro hx hz
    have hlt := (toZMod_eq_zero_iff_norm_lt_one x).mp hz
    rw [hx] at hlt
    exact (lt_irrefl _ hlt)
  · intro hx
    exact le_antisymm (norm_le_one x) (le_of_not_gt
      (fun hlt => hx ((toZMod_eq_zero_iff_norm_lt_one x).mpr hlt)))

/-- Every residue has its unique actual Frobenius-fixed Hensel lift. -/
theorem existsUnique_teichmullerLift (a : ZMod p) :
    ∃! z : PadicInt p, toZMod z = a ∧ z ^ p = z := by
  obtain ⟨b, hb⟩ := ZMod.ringHom_surjective (toZMod : PadicInt p →+* ZMod p) a
  let f : Polynomial (PadicInt p) := Polynomial.X ^ p - Polynomial.X
  have hf : ‖f.aeval b‖ < 1 := by
    apply (toZMod_eq_zero_iff_norm_lt_one _).mp
    simp [f, hb, ZMod.pow_card]
  have hd : ‖f.derivative.aeval b‖ = 1 := by
    apply (norm_eq_one_iff_toZMod_ne_zero _).mpr
    simp [f, Polynomial.derivative_pow]
  obtain ⟨z, hz, hzb, _, huniq⟩ := hensels_lemma (F := f) (a := b)
    (by simpa only [hd, one_pow] using hf)
  have hzres : toZMod z = a := by
    have h := (toZMod_eq_zero_iff_norm_lt_one (z - b)).mpr (by simpa only [hd] using hzb)
    simpa only [map_sub, sub_eq_zero, hb] using h
  refine ⟨z, ⟨hzres, ?_⟩, fun y hy => ?_⟩
  · exact sub_eq_zero.mp (by simpa [f] using hz)
  · apply huniq y
    · simpa [f] using sub_eq_zero.mpr hy.2
    · rw [hd]
      apply (toZMod_eq_zero_iff_norm_lt_one _).mp
      simp only [map_sub, hy.1, hb, sub_self]

/-- The canonical multiplicative residue section is constructed by the
unique actual Hensel lifts, without an assumed lifting section. -/
def teichmuller : ZMod p →*₀ PadicInt p where
  toFun a := (existsUnique_teichmullerLift a).choose
  map_zero' := by
    symm
    exact (existsUnique_teichmullerLift (0 : ZMod p)).choose_spec.2 0
      ⟨by simp, by simp [(Fact.out : p.Prime).ne_zero]⟩
  map_one' := by
    symm
    exact (existsUnique_teichmullerLift (1 : ZMod p)).choose_spec.2 1
      ⟨by simp, one_pow p⟩
  map_mul' a b := by
    symm
    have ha := (existsUnique_teichmullerLift a).choose_spec.1
    have hb := (existsUnique_teichmullerLift b).choose_spec.1
    apply (existsUnique_teichmullerLift (a * b)).choose_spec.2
    exact ⟨by rw [map_mul, ha.1, hb.1], by rw [mul_pow, ha.2, hb.2]⟩

/-- The canonical multiplicative lift is a section of actual reduction. -/
@[simp]
theorem toZMod_teichmuller (a : ZMod p) : toZMod (teichmuller a) = a :=
  (existsUnique_teichmullerLift a).choose_spec.1.1

/-- The actual lifts are fixed by the pth power map. -/
@[simp]
theorem teichmuller_pow (a : ZMod p) : teichmuller a ^ p = teichmuller a :=
  (existsUnique_teichmullerLift a).choose_spec.1.2

theorem teichmuller_injective : Function.Injective (teichmuller : ZMod p → PadicInt p) := by
  intro a b h
  simpa only [toZMod_teichmuller] using congrArg toZMod h

/-- The induced canonical homomorphism on the actual unit groups. -/
def teichmullerUnits : (ZMod p)ˣ →* (PadicInt p)ˣ :=
  Units.map (teichmuller : ZMod p →*₀ PadicInt p).toMonoidHom

theorem teichmullerUnits_injective : Function.Injective (teichmullerUnits (p := p)) := by
  intro a b h
  apply Units.ext
  apply teichmuller_injective
  exact congrArg (fun u : (PadicInt p)ˣ => (u : PadicInt p)) h

/-- Reduction of the lifted unit is its original residue unit. -/
@[simp]
theorem toZMod_teichmullerUnits (a : (ZMod p)ˣ) :
    toZMod (teichmullerUnits a : PadicInt p) = (a : ZMod p) :=
  toZMod_teichmuller _

/-- The actual tame unit image is canonically the finite residue unit group. -/
def teichmullerUnitsEquivRange :
    (ZMod p)ˣ ≃* (teichmullerUnits (p := p)).range :=
  MonoidHom.ofInjective teichmullerUnits_injective

theorem natCard_teichmullerUnits_range :
    Nat.card (teichmullerUnits (p := p)).range = p - 1 := by
  rw [← Nat.card_congr teichmullerUnitsEquivRange.toEquiv,
    Nat.card_eq_fintype_card, ZMod.card_units]

theorem isCyclic_teichmullerUnits_range : IsCyclic (teichmullerUnits (p := p)).range :=
  isCyclic_of_surjective teichmullerUnitsEquivRange
    teichmullerUnitsEquivRange.surjective

/-- There is an actual p-adic unit of exact order p-1, with primitive residue. -/
theorem exists_teichmullerUnit_orderOf :
    ∃ u : (PadicInt p)ˣ, orderOf u = p - 1 ∧
      orderOf (Units.map (toZMod : PadicInt p →+* ZMod p).toMonoidHom u) = p - 1 := by
  obtain ⟨a, ha⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := (ZMod p)ˣ)
  rw [Nat.card_eq_fintype_card, ZMod.card_units] at ha
  refine ⟨teichmullerUnits a, ?_, ?_⟩
  · rw [orderOf_injective teichmullerUnits teichmullerUnits_injective, ha]
  · have heq : Units.map (toZMod : PadicInt p →+* ZMod p).toMonoidHom
        (teichmullerUnits a) = a := Units.ext (toZMod_teichmullerUnits a)
    rw [heq, ha]

end PadicInt
