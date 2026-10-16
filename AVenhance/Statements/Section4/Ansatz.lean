-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

module

public import AVenhance.Statements.Ingredients.XiMK
public import AVenhance.Statements.Section4.ChiTilde
public import AVenhance.Statements.Section4.Hm

/-! Public statement. -/

@[expose] public section

open MeasureTheory Homogenization Filter Topology

noncomputable section

namespace AVenhance

namespace Ingredients
variable {β : ℝ} (I : Ingredients β) {Φ : ℕ → ℝ → Vec 2 → ℝ}

/-- The multiscale ansatz `θ̃_m`, `e.ansatz` (4355), SECOND line — the object the source's
proof actually uses (e.tbm1.one, e.timecomp.0, §5.3); the ansatz is line 2,
with the large-scale flow index `l_k` throughout (and `Χ̃_{m,k}` built from `X⁻¹_{m-1,l_k}`):
`θ̃_m = T_{m-1} + ∑_{k∈ℤ} ξ_{m,k} Χ̃_{m,k} · (∇(T_{m-1}∘X_{m-1,l_k})∘X⁻¹_{m-1,l_k}) + H̃_m`.
The `tsum` is finitely supported for each `(t,x)` (FILE 11), no junk. -/
def ansatz (hΦ : IsStreamSeq I Φ) (m : ℕ) (κm : ℝ) (Tm1 : ℝ → Vec 2 → ℝ) (t : ℝ) (x : Vec 2) : ℝ :=
  Tm1 t x +
    (∑' k : ℤ, I.xiMK m k t *
      vecDot (I.chiTilde hΦ m κm k t x)
        (spaceGrad (fun y => Tm1 t (I.xFlow hΦ m (lIdx β I.Λ m k) t y))
          (I.xFlowInv hΦ m (lIdx β I.Λ m k) t x))) +
    I.Hm hΦ m κm Tm1 t x

end Ingredients
end AVenhance
