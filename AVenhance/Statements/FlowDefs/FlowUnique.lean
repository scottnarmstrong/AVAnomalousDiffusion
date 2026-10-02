-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

module

public import AVenhance.Statements.FlowDefs.FlowIsFlow

/-! Statement file: `flow_unique` (FlowDefs).
This file contains exactly one declaration of the formalization's public statement surface. -/

@[expose] public section

open Homogenization

namespace AVenhance

/-- Characterization: `flow` is the only flow of `b`. -/
theorem flow_unique (b : ℝ → Vec 2 → Vec 2)
    (hb : Continuous (fun p : ℝ × Vec 2 => b p.1 p.2))
    (hL : ∃ L : ℝ, ∀ t x y, ‖b t x - b t y‖ ≤ L * ‖x - y‖)
    {X : ℝ → Vec 2 → ℝ → Vec 2} (hX : IsFlow b X) :
    X = flow b hb hL :=
  (existsUnique_flow b hb hL).unique hX (flow_isFlow b hb hL)

end AVenhance
