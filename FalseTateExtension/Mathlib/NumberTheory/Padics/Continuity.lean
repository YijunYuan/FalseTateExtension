/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import Mathlib.NumberTheory.Padics.RingHoms
public import Mathlib.Topology.Instances.ZMod

/-!
# Continuity into `ℤ_[p]` through the residue projections

A map into `ℤ_[p]` is continuous as soon as all its compositions with the projections
`ℤ_[p] → ZMod (p ^ n)` are.

Upstream candidate: `Mathlib.NumberTheory.Padics.RingHoms`.
-/

@[expose] public section

/-- A map into `ℤ_[p]` is continuous if its reductions modulo every `p ^ n` are. -/
theorem PadicInt.continuous_of_toZModPow {p : ℕ} [Fact p.Prime] {X : Type*} [TopologicalSpace X]
    (f : X → ℤ_[p])
    (hf : ∀ n, Continuous (fun x ↦ PadicInt.toZModPow n (f x))) : Continuous f := by
  rw [continuous_iff_continuousAt]
  intro x
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨n, hn⟩ := PadicInt.exists_pow_neg_lt p hε
  have he : ∀ᶠ y in nhds x,
      PadicInt.toZModPow n (f y) = PadicInt.toZModPow n (f x) :=
    ((hf n).continuousAt (x := x)).eventually
      (p := fun t ↦ t = PadicInt.toZModPow n (f x)) (by simp)
  filter_upwards [he] with y hy
  apply lt_of_le_of_lt _ hn
  rw [dist_eq_norm, PadicInt.norm_le_pow_iff_mem_span_pow,
    ← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub, hy, sub_self]

