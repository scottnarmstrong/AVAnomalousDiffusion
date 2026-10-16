-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

module

public import AVenhance.Statements.Ingredients.HatZetaML

/-! Public statement. -/

@[expose] public section

open MeasureTheory Filter Topology

noncomputable section

namespace AVenhance

namespace Ingredients
variable {β : ℝ} (I : Ingredients β)

/-- `L^κ_{m,n}(t)`, `e.Lmn.def` (3077-3083): `∑_l ζ̂_{m,l}(t) ∫_{-∞}^t ζ̂_{m,l}(s)
(4π²κ(s-t)/ε_m²)ⁿ exp(4π²κ(s-t)/ε_m²) ds`; locally finite in `l` (`hatZetaML_support_finite`),
the integrand is integrable (exponential decay, `ζ̂` bounded). -/
def LMN (κ : ℝ) (m n : ℕ) (t : ℝ) : ℝ :=
  ∑' l : ℤ, I.hatZetaML m l t *
    ∫ s in Set.Iic t,
      I.hatZetaML m l s *
        (4 * Real.pi ^ 2 * κ * (s - t) / epsilon β I.Λ m ^ 2) ^ n *
        Real.exp (4 * Real.pi ^ 2 * κ / epsilon β I.Λ m ^ 2 * (s - t))

end Ingredients
end AVenhance
