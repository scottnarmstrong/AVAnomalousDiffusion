-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

module

public import AVenhance.Infra.Section4.IteratesCancellationRegularity
public import AVenhance.Infra.Section4.IteratesWeightedIntegrability

/-! Transported half-square for the actual K primitive and scalar Hessian. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory
open scoped Matrix.Norms.Elementwise
namespace AVenhance.Infra.Section4
open IterateCalculus
open AVenhance

end AVenhance.Infra.Section4
