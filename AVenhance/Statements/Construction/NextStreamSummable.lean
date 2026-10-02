-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

module

public import AVenhance.Statements.FlowDefs.FlowInv
public import AVenhance.Statements.Section3.SigmaMat
public import AVenhance.Statements.Ingredients.HatZetaML
public import AVenhance.Statements.Ingredients.ZetaMK
public import AVenhance.Statements.Ingredients.Psi
public import AVenhance.Statements.Ingredients.LIdx
public import AVenhance.Statements.Roots.IsHolderClass
public import AVenhance.Statements.Roots.IsDivFree
public import AVenhance.Infra.Flow.SmoothField
public import AVenhance.Infra.Ingredients.LIdxConsequences
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import AVenhance.Infra.Construction.NextStreamFinite

/-! Public statement. -/

@[expose] public section

open MeasureTheory Homogenization Filter Topology

noncomputable section

namespace AVenhance

/-- Well-definedness of the series in `e.psi.recursion`: for every `(t,x)` the family of
terms is summable (indeed finitely supported, since `supp ζ_{m,k} ⊆ [(k-2/3)τ_m,(k+2/3)τ_m]`). -/
theorem Ingredients.nextStream_summable {β : ℝ} (I : Ingredients β) (m : ℕ)
    (φ : ℝ → Vec 2 → ℝ) (hφ : IsAdmissibleStream φ) (t : ℝ) (x : Vec 2) :
    Summable fun k : ℤ => I.nextStreamTerm m φ hφ t x k :=
  summable_of_hasFiniteSupport (Infra.Construction.nextStreamTerm_support_finite I m φ hφ t x)

end AVenhance
