-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

module

public import AVenhance.Statements.Section4.KappaSeq

/-! Public statement. -/

@[expose] public section

open MeasureTheory Homogenization Filter Topology

noncomputable section

namespace AVenhance

namespace Ingredients
variable {β : ℝ} (I : Ingredients β)

/-- `K̄_m^{κ_m} = κ_{m-1}` (source 3897-3898: "Recall `Khom_m^{κ_m} = κ_{m-1}` by
`e.kappa.sequence`"). -/
theorem kappaSeq_pred (κ : ℝ) {M m : ℕ} (hm : 1 ≤ m) (hmM : m ≤ M) :
    I.kappaSeq κ M (m - 1) = I.KhomScalar (I.kappaSeq κ M m) m := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  have h : M - n = (M - (n + 1)) + 1 := by omega
  simp only [kappaSeq, Nat.add_sub_cancel]
  rw [h]
  rfl

end Ingredients
end AVenhance
