-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

module

public import AVenhance.Statements.Section3.SpaceAvgMat

/-! Statement file: `timeAvgMat` (Section3).
This file contains exactly one declaration of the formalization's public statement surface. -/

@[expose] public section

open MeasureTheory Homogenization

noncomputable section

namespace AVenhance

/-- Entrywise `⟨⟨F⟩⟩ = ∫_0^1 F dt` (line 922; `e.Kbarm.def`, label 2983: `∫_0^1 J dt = ⟨⟨·⟩⟩`). -/
def timeAvgMat (F : ℝ → Matrix (Fin 2) (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  Matrix.of fun i j => ∫ t in (0 : ℝ)..1, F t i j

end AVenhance
