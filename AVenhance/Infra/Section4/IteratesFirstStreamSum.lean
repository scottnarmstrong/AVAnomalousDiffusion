-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

module

public import Mathlib.Basic.Real.Basic

/-! The full first-coefficient-order stream contribution. -/

@[expose] public section

noncomputable section
namespace AVenhance.Infra.Section4
open AVenhance

theorem IteratesFirstStreamSum.first_stream_abs_sum {α : Type*} (P : List α) (f : α → ℝ) :
    |(P.map f).sum| ≤ (P.map (fun p => |f p|)).sum := by
  induction P with
  | nil => simp
  | cons p P ih =>
    simp only [List.map_cons, List.sum_cons]
    exact (abs_add_le _ _).trans (add_le_add le_rfl ih)

end AVenhance.Infra.Section4
