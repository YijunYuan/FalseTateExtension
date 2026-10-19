/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FalseTateExtension.Affine.Group
public import FalseTateExtension.Padic.Basic

/-!
# The `p`-adic affine group `ℤ_[p] ⋊ ℤ_[p]ˣ`

`PadicAffineGroup p` is the affine group `ℤ_[p] ⋊ ℤ_[p]ˣ` of the ring `ℤ_[p]`: the group of the
maps `x ↦ u x + a` with `a ∈ ℤ_[p]` and `u ∈ ℤ_[p]ˣ`, written `(a, u)`. With the product topology
it is a compact Hausdorff topological group. The Galois group of the false Tate extension
`K_FT/K` embeds into it as a closed subgroup (`Coordinates/AffineEmbedding`).

## Main results

* `PadicAffineGroup`: the group `ℤ_[p] ⋊ ℤ_[p]ˣ`.
* `padicAffineHomeomorphProd`: the homeomorphism `ℤ_[p] ⋊ ℤ_[p]ˣ ≃ₜ ℤ_[p] × ℤ_[p]ˣ`.
* `continuous_padicAffine_left`, `continuous_padicAffine_right`: the coordinates `(a, u) ↦ a`
  and `(a, u) ↦ u` are continuous.

## References

* Liu, *On lattices in semi-stable representations: a proof of a conjecture of Breuil*, §5.1.
-/

@[expose] public section

namespace FalseTateExtension

noncomputable section

variable (p : ℕ) [Fact p.Prime]

/-- The action of `ℤ_[p]ˣ` on the additive group of `ℤ_[p]` by multiplication. -/
abbrev padicAffineAction : ℤ_[p]ˣ →* MulAut (Multiplicative ℤ_[p]) :=
  affineAction ℤ_[p] (MonoidHom.id ℤ_[p]ˣ)

/-- The affine group `ℤ_[p] ⋊ ℤ_[p]ˣ` of the maps `x ↦ u x + a`, `a ∈ ℤ_[p]`, `u ∈ ℤ_[p]ˣ`. -/
abbrev PadicAffineGroup : Type := AffineGroup ℤ_[p] (MonoidHom.id ℤ_[p]ˣ)

/-- The homeomorphism `ℤ_[p] ⋊ ℤ_[p]ˣ ≃ₜ ℤ_[p] × ℤ_[p]ˣ`, `(a, u) ↦ (a, u)`. -/
abbrev padicAffineHomeomorphProd : PadicAffineGroup p ≃ₜ ℤ_[p] × ℤ_[p]ˣ :=
  AffineGroup.homeomorphProd _

/-- The translation coordinate `(a, u) ↦ a` of `ℤ_[p] ⋊ ℤ_[p]ˣ` is continuous. -/
theorem continuous_padicAffine_left :
    Continuous (fun x : PadicAffineGroup p ↦ x.left.toAdd) :=
  AffineGroup.continuous_left _

/-- The unit coordinate `(a, u) ↦ u` of `ℤ_[p] ⋊ ℤ_[p]ˣ` is continuous. -/
theorem continuous_padicAffine_right :
    Continuous (fun x : PadicAffineGroup p ↦ x.right) :=
  AffineGroup.continuous_right _

end

end FalseTateExtension
