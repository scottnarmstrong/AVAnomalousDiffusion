-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

module

public import AVenhance.Infra.Section4.CoarseCoeff.Bounds
public import AVenhance.Infra.Section3.ExplicitBounds
public import AVenhance.Infra.Section4.IteratesEnergy

/-! Forcing coefficient estimates for the actual iterate equations. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory
open scoped Matrix.Norms.Elementwise
namespace AVenhance.Infra.Section4
open AVenhance

end AVenhance.Infra.Section4
