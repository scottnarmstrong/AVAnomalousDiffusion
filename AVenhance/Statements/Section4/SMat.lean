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
public import AVenhance.Statements.Section4.FlowGrad

/-! Public statement. -/

@[expose] public section

open MeasureTheory Homogenization Filter Topology

noncomputable section

namespace AVenhance

namespace Ingredients
variable {β : ℝ} (I : Ingredients β) {Φ : ℕ → ℝ → Vec 2 → ℝ}

/-- `𝐬⁺_{m-1} := 𝐊_m ∑_l ξ̂_{m,l}(F_l − I) + ∑_l ξ̂_{m,l}(F_lᵀ − I)(𝐊_m − κ_m I)F_l`, with
`F_l = ∇X_{m-1,l}∘X⁻¹_{m-1,l}`: `e.sm` (3974) corrected by the left Jacobian. `𝐊_m = 𝐊^{κ_m}_m`. -/
def sMat (hΦ : IsStreamSeq I Φ) (m : ℕ) (κm : ℝ) (t : ℝ) (x : Vec 2) :
    Matrix (Fin 2) (Fin 2) ℝ :=
  I.Kmat κm m t * ∑' l : ℤ, I.hatXiML m l t • (I.flowGrad hΦ m l t x - 1) +
    ∑' l : ℤ, I.hatXiML m l t •
      (((I.flowGrad hΦ m l t x).transpose - 1) *
        (I.Kmat κm m t - κm • (1 : Matrix (Fin 2) (Fin 2) ℝ)) * I.flowGrad hΦ m l t x)

end Ingredients
end AVenhance
