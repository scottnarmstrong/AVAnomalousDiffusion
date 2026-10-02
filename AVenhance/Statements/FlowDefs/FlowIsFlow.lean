-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

module

public import AVenhance.Statements.FlowDefs.Flow

/-! Statement file: `flow_isFlow` (FlowDefs).
This file contains exactly one declaration of the formalization's public statement surface. -/

@[expose] public section

open Homogenization

namespace AVenhance

/-- Characterization: `flow` satisfies the flow equation and initial condition. -/
theorem flow_isFlow (b : ℝ → Vec 2 → Vec 2)
    (hb : Continuous (fun p : ℝ × Vec 2 => b p.1 p.2))
    (hL : ∃ L : ℝ, ∀ t x y, ‖b t x - b t y‖ ≤ L * ‖x - y‖) :
    IsFlow b (flow b hb hL) :=
  Classical.choose_spec (existsUnique_flow b hb hL).exists

end AVenhance
