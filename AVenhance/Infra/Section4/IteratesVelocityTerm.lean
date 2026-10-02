-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

module

public import AVenhance.Infra.Section4.IteratesVelocityRegularity
public import AVenhance.Infra.Section4.IteratesComponentEnergy
public import AVenhance.Infra.Section4.IteratesLinearPairing

/-! Linear integrated control of each actual material velocity term. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory
namespace AVenhance.Infra.Section4
open IterateCalculus
open AVenhance

end AVenhance.Infra.Section4
