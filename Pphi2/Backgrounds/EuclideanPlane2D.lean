/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Canonical 2D Euclidean Background

This file instantiates the generic Euclidean background and Euclidean time
structure layers for the canonical `P(Φ)₂` spacetime `ℝ²`, with coordinate
`0` singled out as time.
-/

import Pphi2.Backgrounds.EuclideanTime
import Pphi2.OSforGFF.TimeTranslation

noncomputable section

namespace Pphi2

/-- The canonical Euclidean plane background used by `P(Φ)₂`. -/
abbrev plane2Background : EuclideanPlaneBackground := planeBackground 2

/-- Spacetime for `P(Φ)₂`: Euclidean `ℝ²`. -/
abbrev SpaceTime2 := ContinuumSpaceTime 2

/-- Real Schwartz test functions on `ℝ²`. -/
abbrev TestFunction2 := ContinuumTestFunction 2

/-- Complex Schwartz test functions on `ℝ²`. -/
abbrev TestFunction2ℂ := ContinuumComplexTestFunction 2

/-- Tempered distributions on `ℝ²`. -/
abbrev FieldConfig2 := ContinuumFieldConfig 2

/-- Orthogonal linear isometries of `ℝ²`. -/
abbrev O2 := ContinuumOrthogonalGroup 2

/-- Euclidean motions of `ℝ²`. -/
abbrev E2 := ContinuumMotion 2

/-- Action of a Euclidean motion on spacetime points. -/
def E2.act (g : E2) (x : SpaceTime2) : SpaceTime2 := g.R x + g.t

/-- Pull back real Schwartz functions along Euclidean motions. -/
abbrev euclideanAction2 (g : E2) : TestFunction2 →L[ℝ] TestFunction2 :=
  continuumEuclideanAction g

/-- Pull back complex Schwartz functions along Euclidean motions. -/
abbrev euclideanAction2ℂ (g : E2) : TestFunction2ℂ →L[ℝ] TestFunction2ℂ :=
  continuumEuclideanActionComplex g

/-- Time reflection on `ℝ²`: `(t, x) ↦ (-t, x)`. -/
def timeReflection2 (p : SpaceTime2) : SpaceTime2 :=
  WithLp.toLp 2 (fun i => if i = 0 then -p.ofLp i else p.ofLp i)

/-- Time reflection is an involution. -/
theorem timeReflection2_involution (p : SpaceTime2) :
    timeReflection2 (timeReflection2 p) = p := by
  ext i
  by_cases hi : i = 0
  · simp [timeReflection2, hi]
  · simp [timeReflection2, hi]

/-- Time reflection as a linear map on spacetime. -/
def timeReflectionLinear : SpaceTime2 →ₗ[ℝ] SpaceTime2 where
  toFun := timeReflection2
  map_add' p q := by
    ext i
    by_cases hi : i = 0
    · simp [timeReflection2, hi, PiLp.add_apply]
      ring
    · simp [timeReflection2, hi, PiLp.add_apply]
  map_smul' c p := by
    ext i
    by_cases hi : i = 0
    · simp [timeReflection2, hi, PiLp.smul_apply, smul_eq_mul]
    · simp [timeReflection2, hi, PiLp.smul_apply, smul_eq_mul]

/-- The distinguished time axis `t ↦ (t, 0)` in `ℝ²`. -/
def timeAxis2 : ℝ →ₗ[ℝ] SpaceTime2 where
  toFun := fun t => (WithLp.equiv 2 (Fin 2 → ℝ)).symm ![t, 0]
  map_add' s t := by
    ext i
    fin_cases i <;> simp [WithLp.equiv_symm_apply, WithLp.ofLp_toLp,
      Matrix.cons_val_zero, Matrix.cons_val_one]
  map_smul' c t := by
    ext i
    fin_cases i <;> simp [WithLp.equiv_symm_apply, WithLp.ofLp_toLp,
      Matrix.cons_val_zero, Matrix.cons_val_one, smul_eq_mul]

/-- The canonical time structure on `ℝ²`. -/
def plane2TimeStructure : EuclideanTimeStructure plane2Background where
  reflect := timeReflectionLinear
  reflect_involutive := timeReflection2_involution
  timeAxis := timeAxis2
  positiveTimeSet := {p | p.ofLp (0 : Fin 2) > 0}

/-- A spacetime point has positive time if its first coordinate is positive. -/
def hasPositiveTime2 (p : SpaceTime2) : Prop :=
  p ∈ plane2TimeStructure.positiveTimeSet

/-- Time reflection as a continuous linear equivalence. -/
abbrev timeReflectionCLE : SpaceTime2 ≃L[ℝ] SpaceTime2 :=
  plane2TimeStructure.reflectCLE

/-- Pull back real test functions along time reflection. -/
abbrev compTimeReflection2 : TestFunction2 →L[ℝ] TestFunction2 :=
  plane2TimeStructure.reflectOnRealTestFunctions

/-- Pull back complex test functions along time reflection. -/
abbrev compTimeReflection2ℂ : TestFunction2ℂ →L[ℝ] TestFunction2ℂ :=
  plane2TimeStructure.reflectOnComplexTestFunctions

/-- `compTimeReflection2` agrees with pointwise composition by `timeReflection2`. -/
theorem compTimeReflection2_apply (f : TestFunction2) (p : SpaceTime2) :
    compTimeReflection2 f p = f (timeReflection2 p) := rfl

/-- The submodule of real test functions supported at positive time. -/
abbrev positiveTimeSubmodule2 : Submodule ℝ TestFunction2 :=
  plane2TimeStructure.positiveTimeSubmodule

/-- Type of real test functions supported in the positive-time region. -/
abbrev PositiveTimeTestFunction2 := positiveTimeSubmodule2

/-- The pure time-translation vector `(t, 0) ∈ ℝ²`. -/
def timeTranslationVector2 (t : ℝ) : SpaceTime2 :=
  plane2TimeStructure.timeTranslation t

@[simp] theorem timeTranslationVector2_ofLp_zero (t : ℝ) :
    (timeTranslationVector2 t).ofLp (0 : Fin 2) = t := by
  simp [timeTranslationVector2, EuclideanTimeStructure.timeTranslation, plane2TimeStructure,
    timeAxis2, WithLp.equiv_symm_apply, WithLp.ofLp_toLp, Matrix.cons_val_zero]

@[simp] theorem timeTranslationVector2_ofLp_one (t : ℝ) :
    (timeTranslationVector2 t).ofLp (1 : Fin 2) = 0 := by
  simp [timeTranslationVector2, EuclideanTimeStructure.timeTranslation, plane2TimeStructure,
    timeAxis2, WithLp.equiv_symm_apply, WithLp.ofLp_toLp, Matrix.cons_val_one]

/-- Translation of a real Schwartz function by a spacetime vector. -/
abbrev SchwartzMap.translate (a : SpaceTime2) : TestFunction2 →L[ℝ] TestFunction2 :=
  EuclideanPlaneBackground.translate plane2Background a

@[simp] theorem SchwartzMap.translate_apply (a : SpaceTime2)
    (f : TestFunction2) (x : SpaceTime2) :
    SchwartzMap.translate a f x = f (x - a) :=
  EuclideanPlaneBackground.translate_apply plane2Background a f x

theorem sub_timeTranslationVector2_eq_timeShift_neg [Fact (0 < 2)]
    (t : ℝ) (x : SpaceTime2) :
    x - timeTranslationVector2 t = TimeTranslation.timeShift (-t) x := by
  ext i
  fin_cases i
  · simp [TimeTranslation.timeShift, sub_eq_add_neg]
  · simp [TimeTranslation.timeShift, sub_eq_add_neg]

@[simp] theorem translate_timeTranslationVector2_eq_timeTranslationSchwartz_neg
    [Fact (0 < 2)] (t : ℝ) (f : TestFunction2) :
    SchwartzMap.translate (timeTranslationVector2 t) f =
      TimeTranslation.timeTranslationSchwartz (-t) f := by
  ext x
  rw [SchwartzMap.translate_apply, TimeTranslation.timeTranslationSchwartz_apply,
    sub_timeTranslationVector2_eq_timeShift_neg]

end Pphi2
