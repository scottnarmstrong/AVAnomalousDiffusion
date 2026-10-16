-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

module

public import AVenhance.Statements.Construction.IsStreamSeqAdmPred

/-! Public statement. -/

@[expose] public section

open MeasureTheory Homogenization Filter Topology

noncomputable section

namespace AVenhance

namespace Ingredients
variable {β : ℝ} (I : Ingredients β) {Φ : ℕ → ℝ → Vec 2 → ℝ}

/-- `X_{m-1,l}(t,x) = X_{m-1}(t,x,l τ''_m)` (`e.flowabbrev`). -/
def xFlow (hΦ : IsStreamSeq I Φ) (m : ℕ) (l : ℤ) (t : ℝ) (x : Vec 2) : Vec 2 :=
  flow (streamVel (Φ (m - 1))) (hΦ.adm_pred m).vel_continuous (hΦ.adm_pred m).vel_lipschitz t x
    ((l : ℝ) * tauPP β I.Λ m)

end Ingredients
end AVenhance
