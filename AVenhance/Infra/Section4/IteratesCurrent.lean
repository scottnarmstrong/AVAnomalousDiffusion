-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

module

public import AVenhance.Infra.Section4.IteratesDiffusion

/-! The current material oscillatory term is reduced using its actual PDE.
The remainder contains only the preceding scalar field and actual forcing. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory
open scoped Matrix.Norms.Elementwise
namespace AVenhance.Infra.Section4
open IterateCalculus
open AVenhance

end AVenhance.Infra.Section4
