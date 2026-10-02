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
public import AVenhance.Infra.Section4.LocalFinite

/-! Public statement. -/

@[expose] public section

open MeasureTheory Homogenization Filter Topology

noncomputable section

namespace AVenhance

namespace Ingredients
variable {β : ℝ} (I : Ingredients β)

/-- `𝐣^κ_{m,n}(t)`, `e.jkmn` (3065-3069): `(2π²a_m²ε_m²/n!)(ε_m²/(4π²κ))ⁿ ∑_{k∈2ℤ+1} ζ_{m,k}(t)
∂_tⁿζ_{m,k}(t) (1_{k∈4ℤ+1} e₂⊗e₂ + 1_{k∈4ℤ+3} e₁⊗e₁)`; the sum is locally finite
(`zetaMK_support_finite`); `4τ_m`-periodic. -/
def jMN (κ : ℝ) (m n : ℕ) (t : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  (2 * Real.pi ^ 2 * a β I.Λ m ^ 2 * epsilon β I.Λ m ^ 2 / (n.factorial : ℝ) *
      (epsilon β I.Λ m ^ 2 / (4 * Real.pi ^ 2 * κ)) ^ n) •
    ∑' k : {k : ℤ // Odd k},
      (I.zetaMK m k t * iteratedDeriv n (I.zetaMK m k) t) •
        ((if (k : ℤ) % 4 = 1 then !![0, 0; 0, 1] else 0) +
          (if (k : ℤ) % 4 = 3 then !![1, 0; 0, 0] else 0) : Matrix (Fin 2) (Fin 2) ℝ)

end Ingredients
end AVenhance
