/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FalseTateExtension.Affine.Group
public import FalseTateExtension.Padic.Basic

/-!
# The p-adic affine group `ℤ_[p] ⋊ ℤ_[p]ˣ`

The affine group of `ℤ_[p]`, a compact Hausdorff topological group; the Galois group of the
false Tate extension embeds into it as a closed subgroup (`Coordinates/AffineEmbedding`).
-/

@[expose] public section

namespace FalseTateExtension

noncomputable section

variable (p : ℕ) [Fact p.Prime]

/-- `ℤ_[p]ˣ` acting on `ℤ_[p]` by multiplication. -/
abbrev padicAffineAction : ℤ_[p]ˣ →* MulAut (Multiplicative ℤ_[p]) :=
  affineAction ℤ_[p] (MonoidHom.id ℤ_[p]ˣ)

/-- The affine group `ℤ_[p] ⋊ ℤ_[p]ˣ`. -/
abbrev PadicAffineGroup : Type := AffineGroup ℤ_[p] (MonoidHom.id ℤ_[p]ˣ)

/-- The coordinates `ℤ_[p] ⋊ ℤ_[p]ˣ ≃ₜ ℤ_[p] × ℤ_[p]ˣ`. -/
abbrev padicAffineHomeomorphProd : PadicAffineGroup p ≃ₜ ℤ_[p] × ℤ_[p]ˣ :=
  AffineGroup.homeomorphProd _

theorem continuous_padicAffine_left :
    Continuous (fun x : PadicAffineGroup p ↦ x.left.toAdd) :=
  AffineGroup.continuous_left _

theorem continuous_padicAffine_right :
    Continuous (fun x : PadicAffineGroup p ↦ x.right) :=
  AffineGroup.continuous_right _

end

end FalseTateExtension
