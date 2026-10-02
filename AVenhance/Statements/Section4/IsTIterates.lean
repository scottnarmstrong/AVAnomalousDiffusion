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
public import AVenhance.Statements.Section4.TForcing

/-! Public statement. -/

@[expose] public section

open MeasureTheory Homogenization Filter Topology

noncomputable section

namespace AVenhance

namespace Ingredients
variable {β : ℝ} (I : Ingredients β) {Φ : ℕ → ℝ → Vec 2 → ℝ}

/-- The iteration `T^{(0)} = θ_{m-1}`, `T^{(i)}` the (classical) solution of `e.Tm-1.i` for
`1 ≤ i ≤ N_*` (`e.T.m-1.0`, `e.Tm-1.i`, 4031-4054).  `T_{m-1} = T^{(N_*)} = T (Nstar β)`
(`e.T.m-1.Nstar`); `κm = κ_m`, `κprev = κ_{m-1}`, `θprev = θ_{m-1}`. -/
def IsTIterates (hΦ : IsStreamSeq I Φ) (m : ℕ) (κm κprev : ℝ) (θ₀ : Vec 2 → ℝ)
    (θprev : ℝ → Vec 2 → ℝ) (T : ℕ → ℝ → Vec 2 → ℝ) : Prop :=
  T 0 = θprev ∧
  ∀ i : ℕ, 1 ≤ i → i ≤ Nstar β →
    IsClassicalSol (streamVel (Φ (m - 1))) κprev (I.TForcing hΦ m κm κprev (T (i - 1))) θ₀ (T i)

end Ingredients
end AVenhance
