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
public import AVenhance.Statements.Section3.JHat

/-! Public statement. -/

@[expose] public section

open MeasureTheory Homogenization Filter Topology

noncomputable section

namespace AVenhance

namespace Ingredients
variable {β : ℝ} (I : Ingredients β)

/-- `𝐪^κ_{m,n,r}`, `e.q.mnr.def` (3239-3250), by the explicit recursion that solves the
characterization: `q_{n,0} = 𝐣_n - ⟨⟨𝐣_n⟩⟩`, `q_{n,r+1}(t) = -∫_0^t q_{n,r} + ⟨⟨∫_0^· q_{n,r}⟩⟩`
(so `∂_t q_{r+1} = -q_r` and `⟨⟨q_{r+1}⟩⟩ = 0`, `⟨⟨·⟩⟩ = ∫_0^1`).  The index `r` ranges over `ℕ₀` and `q` is
`4τ_m`-periodic (not `τ_m`-periodic); see `qMNR_char`. -/
def qMNR (κ : ℝ) (m n : ℕ) : ℕ → ℝ → Matrix (Fin 2) (Fin 2) ℝ
  | 0 => fun t => I.jMN κ m n t - timeAvgMat (I.jMN κ m n)
  | r + 1 => fun t =>
      -(Matrix.of fun i j => ∫ s in (0 : ℝ)..t, qMNR κ m n r s i j) +
        timeAvgMat (fun u => Matrix.of fun i j => ∫ s in (0 : ℝ)..u, qMNR κ m n r s i j)

end Ingredients
end AVenhance
