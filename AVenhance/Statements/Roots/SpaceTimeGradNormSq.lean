-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

module

public import AVenhance.Statements.Roots.TimeCube
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis

/-! Statement file: `spaceTimeGradNormSq` (Roots).
This file contains exactly one declaration of the formalization's public statement surface. -/

@[expose] public section

open MeasureTheory Filter Topology Homogenization

namespace AVenhance

/-- The squared space-time norm `‖∇θ‖²_{L²((0,1)×𝕋²)}` of a weak gradient `Dθ`. -/
noncomputable def spaceTimeGradNormSq (Dθ : ℝ → Vec 2 → Vec 2) : ℝ :=
  ∫ p in timeCube, vecNormSq (Dθ p.1 p.2)

end AVenhance
