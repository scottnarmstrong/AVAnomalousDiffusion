-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

module

public import AVenhance.Statements.Roots.L2NormSq
public import Homogenization.Sobolev.WeakDerivatives

/-! Public statement. -/

@[expose] public section

open MeasureTheory Homogenization Filter Topology

noncomputable section

namespace AVenhance

/-- `e.theta0.anal` (3835-3838) = `e.theta0.anal.encore` (8030-8035): with `‖∇ⁿ f‖_X := max_{|α|=n}
‖∂^α f‖_X` (`e.nabla.n`, 944) the two displays coincide.  The maximum over multi-indices is
expressed as a bound for every ordered coordinate tuple `i : Fin n → Fin 2` (as in `barNorm`; equal
for `C^n` functions by symmetry of the derivative), for every `n ∈ ℕ = {1,2,…}`. -/
def IsThetaAnalytic (R : ℝ) (θ₀ : Vec 2 → ℝ) : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ i : Fin n → Fin 2,
    Real.sqrt (∫ x in unitCube, (iteratedFDeriv ℝ n θ₀ x (fun j => basisVec (i j))) ^ 2) ≤
      Real.sqrt (l2NormSq θ₀) * ((n.factorial : ℝ) / R ^ n)

end AVenhance
