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
public import AVenhance.Statements.Section4.HMinusOneNorm

/-! Public statement. -/

@[expose] public section

open MeasureTheory Homogenization Filter Topology

noncomputable section

namespace AVenhance

/-- `e.theta0.anal` (3835-3838) = `e.theta0.anal.encore` (8030-8035): with `‖∇ⁿ f‖_X := max_{|α|=n}
‖∂^α f‖_X` (`e.nabla.n`, 944) the two displays coincide.  The maximum over multi-indices is
expressed as a bound for every ordered coordinate tuple `i : Fin n → Fin 2` (as in `barNorm`; equal
for `C^n` functions by symmetry of the derivative), for every `n ∈ ℕ = {1,2,…}`. -/
def IsThetaAnalytic (R : ℝ) (θ₀ : Vec 2 → ℝ) : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ i : Fin n → Fin 2,
    Real.sqrt (∫ x in unitCube, (iteratedFDeriv ℝ n θ₀ x (fun j => basisVec (i j))) ^ 2) ≤
      Real.sqrt (l2NormSq θ₀) * ((n.factorial : ℝ) / R ^ n)

end AVenhance
