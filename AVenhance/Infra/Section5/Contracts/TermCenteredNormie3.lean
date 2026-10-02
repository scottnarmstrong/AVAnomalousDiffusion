-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

module

public import AVenhance.Infra.Section5.Contracts.TermCenteredNormie3Contract

/-! # Centered negative-norm source contract of `normie3`

Facade of the producer `normie3CenteredSource_contract` (`TermCenteredNormie3Contract.lean`), built
from the fast factor `n3Fast` (`TermCenteredNormie3Fast.lean`), the slow factor `n3Slow`
(`TermCenteredNormie3Slow.lean`, `TermCenteredNormie3Analytic.lean`), the per-time centered bound
`n3_time_bound` (`TermCenteredNormie3Time.lean`) and the scale arithmetic
(`TermCenteredNormie3Scale.lean`).  Inputs at amplitude `B`: `TPositiveJetsContract`,
`TGradientContract`, `FirstOrderGradJetContract`. -/

@[expose] public section

