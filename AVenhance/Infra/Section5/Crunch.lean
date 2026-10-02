-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

module

public import AVenhance.Infra.Ingredients.EpsilonConsequences
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Analysis.ODE.Gronwall
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! Scalar bookkeeping for §5.4. All estimates are independent of PDE solution carriers. -/

@[expose] public section

noncomputable section
open scoped BigOperators
open Finset
namespace AVenhance.Infra.Section5

end AVenhance.Infra.Section5
