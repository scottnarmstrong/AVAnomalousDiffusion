-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

module

import AVenhance.Proofs.Construction.ExistsIsStreamSeq
public import AVenhance.Statements.Construction.IsStreamSeq

/-! Public statement. -/

@[expose] public section

open MeasureTheory Homogenization Filter Topology

noncomputable section

namespace AVenhance

/-- Well-definedness (existence) of the construction: the recursion can be carried out at
every step. Together with `IsStreamSeq.unique` this makes `φ_m` a well-defined sequence.
Provable from the closure theorem FILE 9 by recursion (same Paper proof lemma). -/
theorem exists_isStreamSeq {β : ℝ} (I : Ingredients β) :
    ∃ Φ : ℕ → ℝ → Vec 2 → ℝ, IsStreamSeq I Φ := by
  exact AVenhance.Proofs.exists_isStreamSeq I

end AVenhance
