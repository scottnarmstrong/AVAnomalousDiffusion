-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

module

public import AVenhance.Infra.Section5.RelativeError.AssemblyReal
public import AVenhance.Infra.Section5.RelativeError.AssemblyScales
public import AVenhance.Infra.Section5.RelativeError.AssemblyGradient
public import AVenhance.Infra.Section5.RelativeError.AssemblyTelescope
public import AVenhance.Infra.Section5.RelativeError.AssemblyDissipation
public import AVenhance.Infra.Section5.RelativeError.AssemblyClosure

/-! Facade for the RelativeError item 13 main-theorem assembly (`AssemblyReal`, `AssemblyScales`,
`AssemblyGradient`, `AssemblyTelescope`, `AssemblyDissipation`, `AssemblyClosure`).  Exposes
`smooth_analytic_limit_dissipation` and `anomalous_dissipation_of_relative`. -/

@[expose] public section

