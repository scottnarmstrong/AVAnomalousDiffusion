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
public import AVenhance.Statements.Section4.ChiTilde

/-! Public statement. -/

@[expose] public section

open MeasureTheory Homogenization Filter Topology

noncomputable section

namespace AVenhance

namespace Ingredients
variable {β : ℝ} (I : Ingredients β) {Φ : ℕ → ℝ → Vec 2 → ℝ}

/-- The multiscale ansatz `θ̃_m`, `e.ansatz` (4355), SECOND line — the object the source's
proof actually uses (e.tbm1.one, e.timecomp.0, §5.3); the ansatz is line 2,
with the large-scale flow index `l_k` throughout (and `Χ̃_{m,k}` built from `X⁻¹_{m-1,l_k}`):
`θ̃_m = T_{m-1} + ∑_{k∈ℤ} ξ_{m,k} Χ̃_{m,k} · (∇(T_{m-1}∘X_{m-1,l_k})∘X⁻¹_{m-1,l_k}) + H̃_m`.
The `tsum` is finitely supported for each `(t,x)` (FILE 11), no junk. -/
def ansatz (hΦ : IsStreamSeq I Φ) (m : ℕ) (κm : ℝ) (Tm1 : ℝ → Vec 2 → ℝ) (t : ℝ) (x : Vec 2) : ℝ :=
  Tm1 t x +
    (∑' k : ℤ, I.xiMK m k t *
      vecDot (I.chiTilde hΦ m κm k t x)
        (spaceGrad (fun y => Tm1 t (I.xFlow hΦ m (lIdx β I.Λ m k) t y))
          (I.xFlowInv hΦ m (lIdx β I.Λ m k) t x))) +
    I.Hm hΦ m κm Tm1 t x

end Ingredients
end AVenhance
