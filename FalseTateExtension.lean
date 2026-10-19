/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FalseTateExtension.Mathlib
public import FalseTateExtension.Padic
public import FalseTateExtension.Affine
public import FalseTateExtension.Layers
public import FalseTateExtension.Coordinates
public import FalseTateExtension.Cyclotomic
public import FalseTateExtension.Kummer
public import FalseTateExtension.FalseTate

/-!
# The false Tate curve extension

Root module: it imports one aggregate per layer. The six targets of the project and the
declarations proving them are listed in `README.md`:

1. the layers `K(π^{1/p^m}, ζ_{p^n})`, `K_FT`, `K_Kum`, `K_cyc` (`Layers/Basic`);
2. `K_FT`, `K_Kum`, `K_cyc` are strictly APF (`FalseTate/StrictAPF`, `Kummer/APF`,
   `Cyclotomic/APF`);
3. Liu's Lemma 5.1.2 (`FalseTate/TranslationKernel`, `FalseTate/LiuLemma`);
4. the generator `τ = kummerGenerator` of `Gal(K_FT/K_cyc)` (`FalseTate/TranslationKernel`);
5. total ramification of `K_FT/ℚ_p` (`FalseTate/TotalRamification`);
6. Viviani's Corollary 6.10 (`FalseTate/Viviani/Filtration`, `FalseTate/Viviani/Corollary`).
-/
