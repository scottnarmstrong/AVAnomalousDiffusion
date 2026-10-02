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
public import AVenhance.Statements.Section4.Ansatz
public import AVenhance.Proofs.Section4.ClassicalWellposed

/-! Public statement. -/

@[expose] public section

open MeasureTheory Homogenization Filter Topology

noncomputable section

namespace AVenhance

/-- Smooth periodic solvability for smooth forcing (external input of PLAN §0: "parabolic smoothness
of `θ_m` for smooth `b_m`"): existence, and uniqueness on `t ≥ 0` (the class does not constrain
`t < 0`).  Makes the hypotheses `IsClassicalSol` of FILES 34, 35 non-vacuous. -/
theorem classical_wellposed (φ : ℝ → Vec 2 → ℝ) (hφ : IsAdmissibleStream φ) (κ : ℝ) (hκ : 0 < κ)
    (F : ℝ → Vec 2 → ℝ)
    (hF : ContDiffOn ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 => F p.1 p.2) (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (hFper : ∀ t : ℝ, 0 ≤ t → IsZ2Periodic (F t))
    (θ₀ : Vec 2 → ℝ) (hθ₀ : ContDiff ℝ (⊤ : ℕ∞) θ₀) (hper : IsZ2Periodic θ₀) :
    ∃ θ : ℝ → Vec 2 → ℝ, IsClassicalSol (streamVel φ) κ F θ₀ θ ∧
      ∀ θ' : ℝ → Vec 2 → ℝ, IsClassicalSol (streamVel φ) κ F θ₀ θ' →
        ∀ t : ℝ, 0 ≤ t → ∀ x, θ' t x = θ t x := by
  exact AVenhance.Proofs.classical_wellposed φ hφ κ hκ F hF hFper θ₀ hθ₀ hper

end AVenhance
