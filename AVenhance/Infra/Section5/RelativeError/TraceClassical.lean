-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

module

public import AVenhance.Infra.Section5.RelativeError.TraceConcreteAverage
public import AVenhance.Infra.Section5.RelativeError.TransportTraceGradient
public import AVenhance.Infra.Section5.RelativeError.TransportPairingIntegral
public import AVenhance.Infra.Section5.RelativeError.TransportTestSmooth
public import AVenhance.Infra.Section5.RelativeError.ClassicalEnergy
public import AVenhance.Infra.Section5.LeftToShow.BreakUp.Slicing

/-! # RelativeError: the classical low-mode trace bridge

This module connects the transported-test estimate to a classical solution.
The Fourier projection supplies the three explicit spectral facts in the
theorem: its initial pairing, gradient energy, and differentiated Laplacian
bound. -/

@[expose] public section

noncomputable section

open MeasureTheory Set intervalIntegral
open Homogenization
open scoped ContDiff

namespace AVenhance.Infra.Section5.RelativeError

open AVenhance
open AVenhance.Infra.Classical
open AVenhance.Infra.Torus

end AVenhance.Infra.Section5.RelativeError

end
