-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

module

public import AVenhance.Statements.Construction.IsStreamSeq
public import AVenhance.Statements.Construction.StreamVelContinuous
public import AVenhance.Statements.Construction.StreamVelLipschitz
public import AVenhance.Statements.FlowDefs.FlowInv
public import AVenhance.Statements.Section3.KappaAt
public import AVenhance.Statements.Section3.PermittedInterval
public import AVenhance.Statements.Section3.PermissibleSet
public import AVenhance.Statements.Section3.ChiM
public import AVenhance.Statements.Section3.Flux
public import AVenhance.Statements.Section3.TimeAvgMat
public import AVenhance.Statements.Section3.GradMatrix
public import AVenhance.Statements.Section3.SpaceLap
public import AVenhance.Statements.Roots.SpaceTimeGradNormSq
public import AVenhance.Statements.Roots.IsWeakSolutionGrad
public import AVenhance.Statements.Ingredients.Ingredients
public import AVenhance.Statements.Ingredients.HatXiML
public import AVenhance.Statements.Ingredients.HatZetaML
public import AVenhance.Statements.Ingredients.XiMK
public import AVenhance.Statements.Ingredients.ZetaMK
public import AVenhance.Infra.Ingredients.EpsilonConsequences
public import AVenhance.Infra.Ingredients.LIdxConsequences
public import AVenhance.Infra.Cutoff.TimeScaleFacts
public import AVenhance.Statements.Section4.IsClassicalSol

/-! Public statement. -/

@[expose] public section

open MeasureTheory Homogenization Filter Topology

noncomputable section

namespace AVenhance

/-- `‖h‖_{Ḣ⁻¹(𝕋²)} = sup { ∫_{(0,1)²} h φ : φ ∈ C^∞ periodic, ‖∇φ‖_{L²} ≤ 1 }` (the source
uses the norm in `e.bigbound` (7017-7021) and 7047-7078 without a formula).  `ℝ≥0∞`-valued: `⊤` if `h` has nonzero
mean (constants are admissible `φ`), so no junk value. -/
def hMinusOneNorm (h : Vec 2 → ℝ) : ENNReal :=
  ⨆ φ : {φ : Vec 2 → ℝ // ContDiff ℝ (⊤ : ℕ∞) φ ∧ IsZ2Periodic φ ∧ gradNormSq (spaceGrad φ) ≤ 1},
    ENNReal.ofReal |∫ x in unitCube, h x * φ.1 x|

end AVenhance
