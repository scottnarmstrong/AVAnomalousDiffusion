-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

module

public import AVenhance.Infra.Parabolic.FourierGalerkin.GalerkinSequence
public import AVenhance.Infra.Parabolic.FourierGalerkin.EquationModulus

/-!
# positive-cutoff Galerkin solutions

The drift hypotheses instantiate the real Fourier weak-form ODE at every cutoff. This
module packages the concrete data, selected coefficient path, and cutoff-independent scalar and
gradient estimates in one reusable existence statement.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open Homogenization
open scoped Topology

namespace AVenhance.Infra.Parabolic.FourierGalerkin

end AVenhance.Infra.Parabolic.FourierGalerkin

end
