/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FalseTateExtension.GaloisStructure
public import FalseTateExtension.Padic.FiniteGaloisStructure
public import FontaineWintenberger

public import FalseTateExtension.Layers.CompatibleRoots
public import FalseTateExtension.Layers.Basic
public import FalseTateExtension.Layers.Galois
public import FalseTateExtension.Coordinates.Finite
public import FalseTateExtension.Coordinates.Transitions
public import FalseTateExtension.Coordinates.Padic

public import FalseTateExtension.AffineEmbedding
public import FalseTateExtension.Mathlib.FieldTheory.RestrictNormal
public import FalseTateExtension.Mathlib.FieldTheory.Galois.InfiniteCorrespondence
public import FalseTateExtension.Mathlib.FieldTheory.Galois.RestrictScalars
public import FalseTateExtension.Mathlib.FieldTheory.IntermediateField.Supremum
public import FalseTateExtension.Mathlib.NumberTheory.Cyclotomic.CharacterNaturality
public import FalseTateExtension.Mathlib.NumberTheory.Padics.ClosedAddSubgroup
public import FalseTateExtension.Mathlib.NumberTheory.Padics.Cyclotomic
public import FalseTateExtension.Mathlib.RingTheory.Polynomial.EisensteinUniformizer
public import FalseTateExtension.Mathlib.RingTheory.PowerBasis.Eigenvector
public import FalseTateExtension.Mathlib.Data.ZMod.UnitsMap

public import FalseTateExtension.CyclotomicImage

public import FalseTateExtension.AffineKernel

public import FalseTateExtension.Padic.Basic
public import FalseTateExtension.Padic.ClosedAddSubgroup
public import FalseTateExtension.AffineCommutator
public import FalseTateExtension.AffineIndex
public import FalseTateExtension.Cyclotomic.Basic
public import FalseTateExtension.Cyclotomic.Ramification
public import FalseTateExtension.Cyclotomic.Filtration
public import FalseTateExtension.Cyclotomic.FiniteCharacter
public import FalseTateExtension.Cyclotomic.Restriction
public import FalseTateExtension.Cyclotomic.InfiniteCharacter
public import FalseTateExtension.Cyclotomic.CharacterNaturality
public import FalseTateExtension.Cyclotomic.ResidueBound
public import FalseTateExtension.Cyclotomic.Inertia
public import FalseTateExtension.Cyclotomic.InertiaImage

public import FalseTateExtension.Cyclotomic.APF
public import FalseTateExtension.Kummer.Eisenstein
public import FalseTateExtension.Kummer.StepProfile
public import FalseTateExtension.Kummer.Breaks
public import FalseTateExtension.Kummer.FiniteProfile
public import FalseTateExtension.Kummer.APF
public import FalseTateExtension.StrictAPF
public import FalseTateExtension.Padic.Viviani
public import FalseTateExtension.FalseTate.Viviani.TauRamification

/-!
# False Tate, Kummer, and cyclotomic extensions

This is the project public import interface. No mathematical theorem is asserted here.
See blueprint/src/content.tex for the source-facing mathematical specification.
-/
