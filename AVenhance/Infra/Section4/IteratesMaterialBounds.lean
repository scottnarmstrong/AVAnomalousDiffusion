-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

module

public import AVenhance.Infra.Section4.IteratesCurrent

/-! Quantitative reductions of the material oscillatory errors in l.V.
Previous energy inputs are induction inputs on actual fields. These lemmas do
not assert the induction hypothesis for the preceding increment. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory
open scoped Matrix.Norms.Elementwise
namespace AVenhance.Infra.Section4
open IterateCalculus
open AVenhance

end AVenhance.Infra.Section4
