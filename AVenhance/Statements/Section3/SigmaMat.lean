-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

module

public import AVenhance.Statements.Ingredients.HatXiML
public import AVenhance.Statements.Roots.SpaceGrad

/-! Statement file: `sigmaMat` (Section3).
This file contains exactly one declaration of the formalization's public statement surface. -/

@[expose] public section

open MeasureTheory Homogenization

noncomputable section

namespace AVenhance

/-- `e.sigma` (label 919): `σ = (0 -1; 1 0)`. -/
def sigmaMat : Matrix (Fin 2) (Fin 2) ℝ := !![0, -1; 1, 0]

end AVenhance
