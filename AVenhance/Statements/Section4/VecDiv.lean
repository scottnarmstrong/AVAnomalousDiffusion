-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

module

public import AVenhance.Statements.Roots.SpaceGrad

/-! Public statement. -/

@[expose] public section

open MeasureTheory Homogenization Filter Topology

noncomputable section

namespace AVenhance

/-- Classical divergence `∇ · V = ∑ᵢ ∂ᵢ Vᵢ` of a vector field on `ℝ²` (`∇·` in `e.Tm`, `e.Gm`,
`e.H.mr.def`, `e.dm`).  `spaceGrad` is the classical gradient. -/
def vecDiv (V : Vec 2 → Vec 2) (x : Vec 2) : ℝ :=
  ∑ i : Fin 2, spaceGrad (fun y => V y i) x i

end AVenhance
