-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

module

public import AVenhance.Statements.Section3.TimeAvgMat
public import AVenhance.Statements.Section3.LMN
public import AVenhance.Statements.Section3.JMN

/-! Public statement. -/

@[expose] public section

open MeasureTheory Filter Topology

noncomputable section

namespace AVenhance

namespace Ingredients
variable {β : ℝ} (I : Ingredients β)

/-- `𝐊^κ_m(t) := κ I + ∑_{n=0}^{N_*-1} ⟨⟨𝐣^κ_{m,n}⟩⟩ L^κ_{m,n}(t)`, `e.K` (3180-3184). -/
def Kmat (κ : ℝ) (m : ℕ) (t : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  κ • (1 : Matrix (Fin 2) (Fin 2) ℝ) +
    ∑ n ∈ Finset.range (Nstar β), I.LMN κ m n t • timeAvgMat (I.jMN κ m n)

end Ingredients
end AVenhance
