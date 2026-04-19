/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina, Michael R. Douglas

# Euclidean Plane Backgrounds

**(Mathlib-facing):** `EuclideanSpace ℝ (Fin d)`, `SchwartzMap`, `Configuration` (Gaussian-field
tempered distributions), `LinearIsometryEquiv`, and the composition theorems used below. No
`InteractionPolynomial`, lattice measure, or OS axioms appear here.

**(this repository):** `EuclideanPlaneBackground` is only a **1-field** carrier `dim : ℕ`.
Everything else is either an **`abbrev`** to a Mathlib type or a **`def` proved equivalent**
to standard operations (`translate_apply`, `action` via `SchwartzMap.compCLMOfAntilipschitz`).
See `docs/mathlib_prerequisite_layering.md`.

## Content

We package the ambient Euclidean background and derive motions and translation on Schwartz
space once, instead of duplicating `ℝ^d` APIs across the continuum limit and OS layers.

The first instance is the plane background for `P(Φ)₂` (`planeBackground 2`). Torus/cylinder
backgrounds can extend the same pattern beside route-local code.
-/

import GaussianField.Construction
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv

noncomputable section

open GaussianField

namespace Pphi2

/-- A Euclidean continuum background determined by its dimension.

This is intentionally small: the point space, real/complex Schwartz test
spaces, tempered distributions, and Euclidean motions are all derived from
the ambient Euclidean space `ℝ^d`. -/
structure EuclideanPlaneBackground where
  dim : ℕ

namespace EuclideanPlaneBackground

/-- The underlying Euclidean spacetime `ℝ^d`. -/
abbrev SpaceTime (B : EuclideanPlaneBackground) :=
  EuclideanSpace ℝ (Fin B.dim)

/-- Real Schwartz test functions on the background. -/
abbrev RealTestFunction (B : EuclideanPlaneBackground) :=
  SchwartzMap (SpaceTime B) ℝ

/-- Complex Schwartz test functions on the background. -/
abbrev ComplexTestFunction (B : EuclideanPlaneBackground) :=
  SchwartzMap (SpaceTime B) ℂ

/-- Tempered distributions on the background. -/
abbrev Distribution (B : EuclideanPlaneBackground) :=
  Configuration (RealTestFunction B)

/-- Orthogonal linear isometry equivalences of the background. -/
abbrev OrthogonalGroup (B : EuclideanPlaneBackground) :=
  SpaceTime B ≃ₗᵢ[ℝ] SpaceTime B

/-- A Euclidean motion: orthogonal part plus translation. -/
structure Motion (B : EuclideanPlaneBackground) where
  R : OrthogonalGroup B
  t : SpaceTime B

/-- The inverse affine action of a Euclidean motion on spacetime points. -/
def inversePointAction {B : EuclideanPlaneBackground}
    (g : Motion B) (x : SpaceTime B) : SpaceTime B :=
  g.R.symm (x - g.t)

private lemma inversePointAction_hasTemperateGrowth
    {B : EuclideanPlaneBackground} (g : Motion B) :
    (inversePointAction g).HasTemperateGrowth := by
  have hR := g.R.symm.toContinuousLinearEquiv.hasTemperateGrowth
  have hSub : (fun x : SpaceTime B => x - g.t).HasTemperateGrowth :=
    ((ContinuousLinearMap.id ℝ (SpaceTime B)).hasTemperateGrowth).sub
      (Function.HasTemperateGrowth.const g.t)
  convert hR.comp hSub

private lemma inversePointAction_antilipschitz
    {B : EuclideanPlaneBackground} (g : Motion B) :
    AntilipschitzWith 1 (inversePointAction g) :=
  fun x y => by
    simp only [inversePointAction, ENNReal.coe_one, one_mul]
    calc edist x y
        = edist (x - g.t) (y - g.t) := by rw [edist_sub_right]
      _ = edist (g.R.symm (x - g.t)) (g.R.symm (y - g.t)) :=
          (g.R.symm.isometry.edist_eq _ _).symm
      _ ≤ edist (g.R.symm (x - g.t)) (g.R.symm (y - g.t)) := le_refl _

/-- Pull back a real Schwartz function along a Euclidean motion. -/
noncomputable def action {B : EuclideanPlaneBackground}
    (g : Motion B) : RealTestFunction B →L[ℝ] RealTestFunction B :=
  SchwartzMap.compCLMOfAntilipschitz ℝ
    (inversePointAction_hasTemperateGrowth g)
    (inversePointAction_antilipschitz g)

/-- Pull back a complex Schwartz function along a Euclidean motion. -/
noncomputable def actionComplex {B : EuclideanPlaneBackground}
    (g : Motion B) : ComplexTestFunction B →L[ℝ] ComplexTestFunction B :=
  SchwartzMap.compCLMOfAntilipschitz ℝ
    (inversePointAction_hasTemperateGrowth g)
    (inversePointAction_antilipschitz g)

/-- `action` is pullback along the inverse affine point action `x ↦ g.R.symm (x - g.t)`. -/
theorem action_apply {B : EuclideanPlaneBackground} (g : Motion B)
    (f : RealTestFunction B) (x : SpaceTime B) :
    action g f x = f (inversePointAction g x) := by
  simp only [action, SchwartzMap.compCLMOfAntilipschitz_apply, Function.comp_apply]

/-- `actionComplex` is pullback along the inverse affine point action
`x ↦ g.R.symm (x - g.t)`. -/
theorem actionComplex_apply {B : EuclideanPlaneBackground} (g : Motion B)
    (f : ComplexTestFunction B) (x : SpaceTime B) :
    actionComplex g f x = f (inversePointAction g x) := by
  simp only [actionComplex, SchwartzMap.compCLMOfAntilipschitz_apply, Function.comp_apply]

/-- The pure translation motion with identity orthogonal part. -/
def translationMotion (B : EuclideanPlaneBackground) (t : SpaceTime B) : Motion B where
  R := LinearIsometryEquiv.refl ℝ (SpaceTime B)
  t := t

/-- For a pure translation motion, the inverse point action is `x ↦ x - t`. -/
@[simp] theorem inversePointAction_translationMotion
    (B : EuclideanPlaneBackground) (t x : SpaceTime B) :
    inversePointAction (translationMotion B t) x = x - t := by
  change (LinearIsometryEquiv.refl ℝ (SpaceTime B)).symm (x - t) = x - t
  rfl

/-- Translation of a real Schwartz function by a spacetime vector. -/
noncomputable def translate (B : EuclideanPlaneBackground) (v : SpaceTime B) :
    RealTestFunction B →L[ℝ] RealTestFunction B :=
  action (translationMotion B v)

/-- Translation of a complex Schwartz function by a spacetime vector. -/
noncomputable def translateComplex (B : EuclideanPlaneBackground) (v : SpaceTime B) :
    ComplexTestFunction B →L[ℝ] ComplexTestFunction B :=
  actionComplex (translationMotion B v)

/-- `translate` acts by precomposition with `x ↦ x - v`. -/
theorem translate_apply (B : EuclideanPlaneBackground) (v : SpaceTime B)
    (f : RealTestFunction B) (x : SpaceTime B) :
    translate B v f x = f (x - v) := by
  simp [translate, action_apply]

/-- `translateComplex` acts by precomposition with `x ↦ x - v`. -/
theorem translateComplex_apply (B : EuclideanPlaneBackground) (v : SpaceTime B)
    (f : ComplexTestFunction B) (x : SpaceTime B) :
    translateComplex B v f x = f (x - v) := by
  simp [translateComplex, actionComplex_apply]

end EuclideanPlaneBackground

/-- The canonical Euclidean plane background of dimension `d`. -/
abbrev planeBackground (d : ℕ) : EuclideanPlaneBackground where
  dim := d

@[simp] lemma planeBackground_dim (d : ℕ) : (planeBackground d).dim = d :=
  rfl

/-- Euclidean spacetime `ℝ^d` used by continuum test functions. -/
abbrev ContinuumSpaceTime (d : ℕ) :=
  EuclideanPlaneBackground.SpaceTime (planeBackground d)

/-- Continuum real Schwartz test functions on `ℝ^d`. -/
abbrev ContinuumTestFunction (d : ℕ) :=
  EuclideanPlaneBackground.RealTestFunction (planeBackground d)

/-- Continuum complex Schwartz test functions on `ℝ^d`. -/
abbrev ContinuumComplexTestFunction (d : ℕ) :=
  EuclideanPlaneBackground.ComplexTestFunction (planeBackground d)

/-- Tempered distributions on `ℝ^d`. -/
abbrev ContinuumFieldConfig (d : ℕ) :=
  EuclideanPlaneBackground.Distribution (planeBackground d)

/-- Orthogonal group of `ℝ^d`. -/
abbrev ContinuumOrthogonalGroup (d : ℕ) :=
  EuclideanPlaneBackground.OrthogonalGroup (planeBackground d)

/-- Euclidean motions of `ℝ^d`. -/
abbrev ContinuumMotion (d : ℕ) :=
  EuclideanPlaneBackground.Motion (planeBackground d)

/-! ### P-characterization of continuum abbreviations

These are definitional equalities to standard Mathlib types (`rfl`). Use them in `rw`/`simp`
to discharge “notational” distance between `Continuum*` names and `EuclideanSpace`/`SchwartzMap`. -/

@[simp] theorem ContinuumSpaceTime_eq (d : ℕ) :
    ContinuumSpaceTime d = EuclideanSpace ℝ (Fin d) :=
  rfl

@[simp] theorem ContinuumTestFunction_eq (d : ℕ) :
    ContinuumTestFunction d = SchwartzMap (EuclideanSpace ℝ (Fin d)) ℝ :=
  rfl

@[simp] theorem ContinuumComplexTestFunction_eq (d : ℕ) :
    ContinuumComplexTestFunction d = SchwartzMap (EuclideanSpace ℝ (Fin d)) ℂ :=
  rfl

@[simp] theorem ContinuumFieldConfig_eq (d : ℕ) :
    ContinuumFieldConfig d = Configuration (SchwartzMap (EuclideanSpace ℝ (Fin d)) ℝ) :=
  rfl

@[simp] theorem ContinuumOrthogonalGroup_eq (d : ℕ) :
    ContinuumOrthogonalGroup d =
      (EuclideanSpace ℝ (Fin d) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d)) :=
  rfl

/-- Pull back a real Schwartz function on `ℝ^d` along a Euclidean motion. -/
noncomputable def continuumEuclideanAction {d : ℕ}
    (g : ContinuumMotion d) :
    ContinuumTestFunction d →L[ℝ] ContinuumTestFunction d :=
  EuclideanPlaneBackground.action g

/-- `continuumEuclideanAction` is pullback along `x ↦ g.R.symm (x - g.t)`. -/
theorem continuumEuclideanAction_apply {d : ℕ} (g : ContinuumMotion d)
    (f : ContinuumTestFunction d) (x : ContinuumSpaceTime d) :
    continuumEuclideanAction g f x =
      f (EuclideanPlaneBackground.inversePointAction g x) :=
  EuclideanPlaneBackground.action_apply g f x

/-- Pull back a complex Schwartz function on `ℝ^d` along a Euclidean motion. -/
noncomputable def continuumEuclideanActionComplex {d : ℕ}
    (g : ContinuumMotion d) :
    ContinuumComplexTestFunction d →L[ℝ] ContinuumComplexTestFunction d :=
  EuclideanPlaneBackground.actionComplex g

/-- `continuumEuclideanActionComplex` is pullback along `x ↦ g.R.symm (x - g.t)`. -/
theorem continuumEuclideanActionComplex_apply {d : ℕ} (g : ContinuumMotion d)
    (f : ContinuumComplexTestFunction d) (x : ContinuumSpaceTime d) :
    continuumEuclideanActionComplex g f x =
      f (EuclideanPlaneBackground.inversePointAction g x) :=
  EuclideanPlaneBackground.actionComplex_apply g f x

/-- Translation of a real Schwartz function by `v ∈ ℝ^d`. -/
noncomputable def schwartzTranslate (d : ℕ) (v : ContinuumSpaceTime d) :
    ContinuumTestFunction d →L[ℝ] ContinuumTestFunction d :=
  EuclideanPlaneBackground.translate (planeBackground d) v

/-- `schwartzTranslate` acts by precomposition with `x ↦ x - v`. -/
theorem schwartzTranslate_apply {d : ℕ} (v : ContinuumSpaceTime d)
    (f : ContinuumTestFunction d) (x : ContinuumSpaceTime d) :
    schwartzTranslate d v f x = f (x - v) :=
  EuclideanPlaneBackground.translate_apply (planeBackground d) v f x

end Pphi2
