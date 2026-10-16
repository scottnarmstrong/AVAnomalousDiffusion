-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

module

public import AVenhance.Statements.Construction.IsStreamSeq

/-! Public statement. -/

@[expose] public section

open MeasureTheory Homogenization Filter Topology

noncomputable section

namespace AVenhance

/-- Admissibility of `φ_{m-1}` for every `m` (so the flow `X_{m-1}` of `b_{m-1}` exists), read off
`IsStreamSeq`: for `m ≥ 1` it is the `∃ h` of the definition, for `m = 0` (`Φ (0-1) = Φ 0 = 0`) it
is trivial.  No closure theorem is used and no premise `∀ m, IsAdmissibleStream (Φ m)`. -/
theorem IsStreamSeq.adm_pred {β : ℝ} {I : Ingredients β} {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (h : IsStreamSeq I Φ) (m : ℕ) : IsAdmissibleStream (Φ (m - 1)) := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · have h0 : Φ (0 - 1) = fun _ _ => (0 : ℝ) := h.1
    rw [h0]
    exact ⟨contDiff_const, fun _ _ _ _ => rfl⟩
  · obtain ⟨hφ, _⟩ := h.2 m hm
    exact hφ

end AVenhance
