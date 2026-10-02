-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

module

public import AVenhance.Statements.Flow.ExistsUniqueFlow
public import AVenhance.Infra.Flow.Laws

/-! Statement file: `flow` (FlowDefs).
This file contains exactly one declaration of the formalization's public statement surface. -/

@[expose] public section

open Homogenization

namespace AVenhance

/-- The flow `X(t,x,s)` of `e.flow.m.def` (source 1397–1410): the unique `X` with
`IsFlow b X`, chosen from the proved `existsUnique_flow`. -/
noncomputable def flow (b : ℝ → Vec 2 → Vec 2)
    (hb : Continuous (fun p : ℝ × Vec 2 => b p.1 p.2))
    (hL : ∃ L : ℝ, ∀ t x y, ‖b t x - b t y‖ ≤ L * ‖x - y‖) :
    ℝ → Vec 2 → ℝ → Vec 2 :=
  Classical.choose (existsUnique_flow b hb hL).exists

end AVenhance
