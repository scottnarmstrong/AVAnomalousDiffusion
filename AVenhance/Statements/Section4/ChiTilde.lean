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
public import AVenhance.Statements.Section4.Hm

/-! Public statement. -/

@[expose] public section

open MeasureTheory Homogenization Filter Topology

noncomputable section

namespace AVenhance

namespace Ingredients
variable {β : ℝ} (I : Ingredients β) {Φ : ℕ → ℝ → Vec 2 → ℝ}

/-- The twisted corrector `Χ̃_{m,k} := Χ_{m,k} ∘ X⁻¹_{m-1,l_k}`, `e.Chim.def` (4386).  The source
writes `X⁻¹_{m-1,k}`; this is a slip in the source (`l_k` is meant: `e.tbm1.one` 6373 and the proof of `p.indystepdown` use `l_k`; same slip in `ψ̃_{m,k}`, 6327). -/
def chiTilde (hΦ : IsStreamSeq I Φ) (m : ℕ) (κm : ℝ) (k : ℤ) (t : ℝ) (x : Vec 2) : Vec 2 :=
  I.chiMK κm m k t (I.xFlowInv hΦ m (lIdx β I.Λ m k) t x)

end Ingredients
end AVenhance
