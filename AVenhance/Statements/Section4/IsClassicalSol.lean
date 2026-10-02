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
public import AVenhance.Statements.Section4.AdvDiffOp

/-! Public statement. -/

@[expose] public section

open MeasureTheory Homogenization Filter Topology

noncomputable section

namespace AVenhance

/-- Classical `ℤ²`-periodic solution of `∂_t θ - κ Δθ + b·∇θ = F` in `(0,∞) × ℝ²`, `θ(0) = θ₀`
(`e.theta.m` 3842-3853, `e.Tm-1.i` 4036-4046, `e.Vm-1.i`; source: "`θ_m ∈ C^∞`", "`T ∈ C^∞([0,∞)×ℝ²)`",
"zero mean and `ℤ²`-periodic for each time").  Smooth up to `t = 0`, periodic in `x` for `t ≥ 0`. -/
def IsClassicalSol (b : ℝ → Vec 2 → Vec 2) (κ : ℝ) (F : ℝ → Vec 2 → ℝ) (θ₀ : Vec 2 → ℝ)
    (θ : ℝ → Vec 2 → ℝ) : Prop :=
  ContDiffOn ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 => θ p.1 p.2) (Set.Ici (0 : ℝ) ×ˢ Set.univ) ∧
  (∀ t : ℝ, 0 ≤ t → IsZ2Periodic (θ t)) ∧
  (∀ x, θ 0 x = θ₀ x) ∧
  ∀ t : ℝ, 0 < t → ∀ x, advDiffOp b κ θ t x = F t x

end AVenhance
