-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

module

public import AVenhance.AllStatements

/-!
# Anomalous diffusion by fractal homogenization

Root of the formalization of S. Armstrong and V. Vicol, *Anomalous diffusion by fractal
homogenization* (arXiv:2305.05048). Importing this module brings in every public statement
(`AVenhance.Statements`) together with its proof. The headline results are
`AVenhance.anomalous_dissipation` (Theorem 1.1 of the paper) and
`AVenhance.anomalous_dissipation_full` (Theorem 1.1, Remark r.LeBron.2 and a corrected
no-selection principle, for one drift).
-/
