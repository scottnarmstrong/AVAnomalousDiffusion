-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

module

public import AVenhance.Statements.Section3.JMN
public import AVenhance.Statements.Section3.LMN

/-! Public statement. -/

@[expose] public section

open MeasureTheory Filter Topology

noncomputable section

namespace AVenhance

namespace Ingredients
variable {β : ℝ} (I : Ingredients β)

/-- `Ĵ^κ_m(t) := κ I + ∑_{n=0}^{N_*-1} L^κ_{m,n}(t) 𝐣^κ_{m,n}(t)`, `e.Jhat` (3056-3060). -/
def Jhat (κ : ℝ) (m : ℕ) (t : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  κ • (1 : Matrix (Fin 2) (Fin 2) ℝ) +
    ∑ n ∈ Finset.range (Nstar β), I.LMN κ m n t • I.jMN κ m n t

end Ingredients
end AVenhance
