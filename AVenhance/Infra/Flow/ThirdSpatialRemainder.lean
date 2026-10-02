-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

module

public import AVenhance.Infra.Flow.ThirdFieldTaylor

/-! Quadratic initial-point remainder for the flow's second variation. -/

@[expose] public section

open Homogenization
open Set
open scoped ContDiff NNReal Topology

namespace AVenhance.Infra.Flow

theorem ThirdSpatialRemainder.gronwallBound_zero_scale_thirdSpatialRemainder
    (L a c d : ℝ) :
    gronwallBound 0 L (c * a) d = c * gronwallBound 0 L a d := by
  by_cases hL : L = 0
  · simp [gronwallBound, hL]
    ring
  · simp [gronwallBound, hL]
    ring

theorem ThirdSpatialRemainder.thirdRemainder_linearFlow_bound_on_Ico
    (A : ℝ → Vec 2 →L[ℝ] Vec 2) (M : ℝ)
    (hM₀ : 0 ≤ M) (hA : ∀ q, ‖A q‖ ≤ M)
    {V : ℝ → Vec 2 → ℝ → Vec 2}
    (hV : AVenhance.IsFlow (fun q v => A q v) V)
    (s t : ℝ) (_hst : s ≤ t) :
    ∀ v q, q ∈ Ico s t →
      ‖V q v s‖ ≤ Real.exp (M * (t - s)) * ‖v‖ := by
  have hAL : ∀ q u w, ‖A q u - A q w‖ ≤ M * ‖u - w‖ := by
    intro q u w
    calc
      ‖A q u - A q w‖ = ‖A q (u - w)‖ := by rw [map_sub]
      _ ≤ ‖A q‖ * ‖u - w‖ := (A q).le_opNorm _
      _ ≤ M * ‖u - w‖ := mul_le_mul_of_nonneg_right (hA q) (norm_nonneg _)
  have hzero := linearSystemFlow_zero A M hAL hV s
  intro v q hq
  have hgr := flow_spatial_gronwall (fun r z => A r z) hAL hV v 0 s q
  have hexp : Real.exp (M * |q - s|) ≤ Real.exp (M * (t - s)) := by
    apply Real.exp_le_exp.mpr
    calc
      M * |q - s| = M * (q - s) := by
        rw [abs_of_nonneg (sub_nonneg.mpr hq.1)]
      _ ≤ M * (t - s) :=
        mul_le_mul_of_nonneg_left (by linarith [hq.2]) hM₀
  calc
    ‖V q v s‖ = ‖V q v s - V q 0 s‖ := by rw [hzero q, sub_zero]
    _ ≤ Real.exp (M * |q - s|) * ‖v - 0‖ := hgr
    _ ≤ Real.exp (M * (t - s)) * ‖v‖ := by
      simpa using mul_le_mul_of_nonneg_right hexp (norm_nonneg v)

/-- On a forward interval, the selected third variation is the linear term
in the initial-point Taylor expansion of the second variation, with a
uniform quadratic remainder. -/
theorem exists_flow_secondVariation_quadratic_remainder_all_times_of_le
    {b : ℝ → Vec 2 → Vec 2} (hb : SmoothPeriodicField b)
    {X : ℝ → Vec 2 → ℝ → Vec 2} (hX : AVenhance.IsFlow b X)
    (x : Vec 2) (s t : ℝ) (hst : s ≤ t) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u h k q, q ∈ Icc s t →
      ‖flowSecondVariation hb hX (x + u) s
          (Classical.choose_spec
            (existsUnique_flow_variationalEquation hb hX (x + u) s)).1 h k q 0 s -
        flowSecondVariation hb hX x s
          (Classical.choose_spec (existsUnique_flow_variationalEquation hb hX x s)).1
          h k q 0 s -
        flowThirdVariation hb hX x s
          (Classical.choose_spec (existsUnique_flow_variationalEquation hb hX x s)).1
          u h k q 0 s‖ ≤ C * ‖u‖ * ‖u‖ * ‖h‖ * ‖k‖ := by
  obtain ⟨L, hL₀, hL⟩ := exists_global_spatial_lipschitz hb
  obtain ⟨M, hM₀, hM⟩ := exists_global_jointSpatialFDeriv_bound hb
  obtain ⟨Cjac, hCjac₀, hCjac⟩ := exists_global_spatialFDeriv_lipschitz hb
  obtain ⟨TA, hTA₀, hTA⟩ := exists_global_spatialFDeriv_apply_taylor_remainder hb
  obtain ⟨C₂, hC₂₀, hC₂⟩ := exists_global_spatialSecondDerivativeEval_bound hb
  obtain ⟨TH, hTH₀, hTH⟩ := exists_global_spatialSecondDerivativeEval_taylor_remainder hb
  obtain ⟨C₃, hC₃₀, hC₃⟩ := exists_global_spatialThirdDerivativeEval_bound hb
  let Vx : ℝ → Vec 2 → ℝ → Vec 2 :=
    Classical.choose (existsUnique_flow_variationalEquation hb hX x s)
  have hVx : AVenhance.IsFlow (linearizedFieldAlongFlow b X x s) Vx :=
    (Classical.choose_spec (existsUnique_flow_variationalEquation hb hX x s)).1
  obtain ⟨Ctraj, hCtraj₀, htraj⟩ :=
    flow_variational_quadratic_remainder_all_times_of_le hb hX x s t hst hVx
  obtain ⟨Vbase, hVbase, Bbase, hBbase, Crem, hCrem₀, hCrem⟩ :=
    exists_flow_second_spatial_derivative_of_le hb hX x s t hst
  have hVbaseEq : Vbase = Vx :=
    (Classical.choose_spec (existsUnique_flow_variationalEquation hb hX x s)).2
      Vbase hVbase
  obtain ⟨C₂lip, hC₂lip₀, hC₂lip⟩ := exists_global_spatialSecondDerivativeEval_lipschitz hb
  let K₂diff := flowSecondVariationLipschitzConstant L M Cjac C₂ C₂lip s t
  have hK₂diff₀ : 0 ≤ K₂diff := by
    obtain ⟨C, hC₀, hCeq, _⟩ := exists_flow_secondVariation_lipschitz_all_times_of_le
      hb hX L M Cjac C₂ C₂lip hL₀ hM₀ hCjac₀ hC₂₀ hC₂lip₀
      hL hM hCjac hC₂ hC₂lip x x s t hst 0 0
    dsimp [K₂diff]
    rw [← hCeq]
    exact hC₀
  obtain ⟨K₂x, hK₂x₀, hK₂xEq, hW₂x⟩ :=
    flowSecondVariation_bound_all_times_of_le hb hX M C₂ hM₀ hM hC₂₀ hC₂
      (V := Vx) x s t hst hVx
  let d : ℝ := t - s
  let F : ℝ := Real.exp (L * d)
  let E : ℝ := Real.exp (M * d)
  let Kvar : ℝ := gronwallBound 0 M
    (Cjac * Real.exp (L * d) * Real.exp (M * d)) d
  let K₂ : ℝ := gronwallBound 0 M
    (C₂ * Real.exp (M * d) * Real.exp (M * d)) d
  let K₃ : ℝ := flowThirdVariationGrowthConstant M C₂ C₃ s t
  let Cforce : ℝ :=
    TA * K₂ * F * F * E + C₂ * Ctraj * K₂ + C₂ * E * K₂diff +
    TH * E * E * F * F + C₃ * Ctraj * E * E +
    2 * C₃ * Kvar * E * E + C₂ * Crem * E +
    C₂ * K₂ * Kvar + C₂ * E * Crem
  let C : ℝ := gronwallBound 0 M Cforce d
  have hd₀ : 0 ≤ d := by dsimp [d]; linarith
  have hF₀ : 0 ≤ F := (Real.exp_pos _).le
  have hE₀ : 0 ≤ E := (Real.exp_pos _).le
  have hK₂xEq' : K₂x = K₂ := by simpa [K₂, E, d] using hK₂xEq
  have hK₂₀ : 0 ≤ K₂ := by
    rw [← hK₂xEq']
    exact hK₂x₀
  have hKvar₀ : 0 ≤ Kvar := by
    have hmono := gronwallBound_mono
      (show 0 ≤ (0 : ℝ) by norm_num)
      (mul_nonneg (mul_nonneg hCjac₀ hF₀) hE₀) hM₀
    simpa [Kvar, gronwallBound_x0] using hmono hd₀
  have hK₂diffEq : K₂diff =
      flowSecondVariationLipschitzConstant L M Cjac C₂ C₂lip s t := rfl
  have hCforce₀ : 0 ≤ Cforce := by
    dsimp [Cforce]
    positivity
  have hC₀ : 0 ≤ C := by
    have hmono := gronwallBound_mono
      (show 0 ≤ (0 : ℝ) by norm_num) hCforce₀ hM₀
    simpa [C, gronwallBound_x0] using hmono hd₀
  refine ⟨C, hC₀, ?_⟩
  intro u h k q hq
  let Vy : ℝ → Vec 2 → ℝ → Vec 2 :=
    Classical.choose (existsUnique_flow_variationalEquation hb hX (x + u) s)
  have hVy : AVenhance.IsFlow (linearizedFieldAlongFlow b X (x + u) s) Vy :=
    (Classical.choose_spec (existsUnique_flow_variationalEquation hb hX (x + u) s)).1
  have htrajQ (r : ℝ) (hr : r ∈ Icc s t) :
      ‖X r (x + u) s - X r x s‖ ≤ F * ‖u‖ := by
    have hgr := flow_spatial_gronwall_of_le b hL hX (x + u) x s r hr.1
    have hexp : Real.exp (L * (r - s)) ≤ F := by
      apply Real.exp_le_exp.mpr
      dsimp [F, d]
      exact mul_le_mul_of_nonneg_left (by linarith [hr.2]) hL₀
    calc
      ‖X r (x + u) s - X r x s‖ ≤ Real.exp (L * (r - s)) * ‖(x + u) - x‖ := hgr
      _ ≤ F * ‖u‖ := by simpa using mul_le_mul_of_nonneg_right hexp (norm_nonneg u)
  have htrajRem (r : ℝ) (hr : r ∈ Icc s t) :
      ‖X r (x + u) s - X r x s - Vx r u s‖ ≤ Ctraj * ‖u‖ * ‖u‖ :=
    htraj r hr u
  have hVxBound (v : Vec 2) (r : ℝ) (hr : r ∈ Ico s t) :
      ‖Vx r v s‖ ≤ E * ‖v‖ := by
    exact ThirdSpatialRemainder.thirdRemainder_linearFlow_bound_on_Ico
      (fun r => jointSpatialFDeriv b r (X r x s)) M hM₀
      (fun r => hM r (X r x s)) hVx s t hst v r hr
  have hVyBound (v : Vec 2) (r : ℝ) (hr : r ∈ Ico s t) :
      ‖Vy r v s‖ ≤ E * ‖v‖ := by
    exact ThirdSpatialRemainder.thirdRemainder_linearFlow_bound_on_Ico
      (fun r => jointSpatialFDeriv b r (X r (x + u) s)) M hM₀
      (fun r => hM r (X r (x + u) s)) hVy s t hst v r hr
  obtain ⟨K₂y, hK₂y₀, hK₂yEq, hW₂y⟩ :=
    flowSecondVariation_bound_all_times_of_le hb hX M C₂ hM₀ hM hC₂₀ hC₂
      (V := Vy) (x + u) s t hst hVy
  have hK₂yEq' : K₂y = K₂ := by simpa [K₂, E, d] using hK₂yEq
  obtain ⟨K₃', hK₃'₀, hK₃'Eq, hW₃⟩ :=
    flowThirdVariation_bound_all_times_of_le hb hX x s t hst hVx
      M C₂ C₃ hM₀ hM hC₂₀ hC₂ hC₃₀ hC₃
  have hK₃'Eq : K₃' = K₃ := by simpa [K₃] using hK₃'Eq
  obtain ⟨Vx₀, hVx₀, Vy₀, hVy₀, Kvar₀, hKvar₀, hKvarFormula, hVdiff⟩ :=
    exists_flow_variational_difference_bound_all_times_of_le hb hX
      L M Cjac hL₀ hM₀ hCjac₀ hL hM hCjac x (x + u) s t hst
  have hVx₀Eq : Vx₀ = Vx :=
    (Classical.choose_spec (existsUnique_flow_variationalEquation hb hX x s)).2 Vx₀ hVx₀
  have hVy₀Eq : Vy₀ = Vy :=
    (Classical.choose_spec (existsUnique_flow_variationalEquation hb hX (x + u) s)).2 Vy₀ hVy₀
  have hKvarEq : Kvar₀ = Kvar := by simpa [Kvar, d] using hKvarFormula
  have hsub : x - (x + u) = -u := by abel
  have hVdiffQ (r : ℝ) (hr : r ∈ Icc s t) (v : Vec 2) :
      ‖Vy r v s - Vx r v s‖ ≤ Kvar * ‖u‖ * ‖v‖ := by
    have hdiff := hVdiff r hr v
    rw [hVx₀Eq, hVy₀Eq, hKvarEq] at hdiff
    simpa [hsub] using hdiff
  obtain ⟨Kdiff, hKdiff₀, hKdiffEq, hWdiff⟩ :=
    exists_flow_secondVariation_lipschitz_all_times_of_le hb hX
      L M Cjac C₂ C₂lip hL₀ hM₀ hCjac₀ hC₂₀ hC₂lip₀
      hL hM hCjac hC₂ hC₂lip x (x + u) s t hst h k
  have hKdiffEq' : Kdiff = K₂diff := by simpa [K₂diff] using hKdiffEq
  have hWdiffQ (r : ℝ) (hr : r ∈ Icc s t) :
      ‖flowSecondVariation hb hX (x + u) s hVy h k r 0 s -
        flowSecondVariation hb hX x s hVx h k r 0 s‖ ≤
        K₂diff * ‖u‖ * ‖h‖ * ‖k‖ := by
    have h := hWdiff r hr
    rw [hKdiffEq'] at h
    simpa [hsub] using h
  have hVrem (r : ℝ) (hr : r ∈ Icc s t) (v : Vec 2) :
      ‖Vy r v s - Vx r v s -
        flowSecondVariation hb hX x s hVx u v r 0 s‖ ≤
        Crem * ‖u‖ * ‖u‖ * ‖v‖ := by
    have h := (hCrem u v).2 r hr
    rw [hVbaseEq] at h
    simpa [Vy] using h
  have hWboundX (r : ℝ) (hr : r ∈ Icc s t) :
      ‖flowSecondVariation hb hX x s hVx h k r 0 s‖ ≤ K₂ * ‖h‖ * ‖k‖ := by
    have h := hW₂x r hr h k
    rw [hK₂xEq'] at h
    exact h
  have hWboundY (r : ℝ) (hr : r ∈ Icc s t) :
      ‖flowSecondVariation hb hX (x + u) s hVy h k r 0 s‖ ≤
        K₂ * ‖h‖ * ‖k‖ := by
    have h := hW₂y r hr h k
    rw [hK₂yEq'] at h
    exact h
  have hZbound (r : ℝ) (hr : r ∈ Icc s t) :
      ‖flowThirdVariation hb hX x s hVx u h k r 0 s‖ ≤
        K₃ * ‖u‖ * ‖h‖ * ‖k‖ := by
    have h := hW₃ u h k r hr
    rw [hK₃'Eq] at h
    exact h
  let Wx : ℝ → Vec 2 := fun r =>
    flowSecondVariation hb hX x s hVx h k r 0 s
  let Wy : ℝ → Vec 2 := fun r =>
    flowSecondVariation hb hX (x + u) s hVy h k r 0 s
  let Z : ℝ → Vec 2 := fun r =>
    flowThirdVariation hb hX x s hVx u h k r 0 s
  let Wuh : ℝ → Vec 2 := fun r =>
    flowSecondVariation hb hX x s hVx u h r 0 s
  let Wuk : ℝ → Vec 2 := fun r =>
    flowSecondVariation hb hX x s hVx u k r 0 s
  let Ax : ℝ → Vec 2 →L[ℝ] Vec 2 :=
    fun r => jointSpatialFDeriv b r (X r x s)
  let Ay : ℝ → Vec 2 →L[ℝ] Vec 2 :=
    fun r => jointSpatialFDeriv b r (X r (x + u) s)
  let Hx : ℝ → Vec 2 → Vec 2 → Vec 2 :=
    fun r a c => spatialSecondDerivativeEval b r (X r x s) a c
  let Hy : ℝ → Vec 2 → Vec 2 → Vec 2 :=
    fun r a c => spatialSecondDerivativeEval b r (X r (x + u) s) a c
  let Tx : ℝ → Vec 2 → Vec 2 → Vec 2 → Vec 2 :=
    fun r a c e => spatialThirdDerivativeEval b r (X r x s) a c e
  have hAsplit (r : ℝ) :
      Ay r (Wy r) - Ax r (Wy r) - Hx r (Vx r u s) (Wx r) =
        (Ay r (Wy r) - Ax r (Wy r) -
            Hx r (X r (x + u) s - X r x s) (Wy r)) +
          Hx r (X r (x + u) s - X r x s - Vx r u s) (Wy r) +
          Hx r (Vx r u s) (Wy r - Wx r) := by
    have hδ : X r (x + u) s - X r x s =
        (X r (x + u) s - X r x s - Vx r u s) + Vx r u s := by abel
    have hleft : Hx r (X r (x + u) s - X r x s) (Wy r) =
        Hx r (X r (x + u) s - X r x s - Vx r u s) (Wy r) +
          Hx r (Vx r u s) (Wy r) := by
      calc
        _ = Hx r ((X r (x + u) s - X r x s - Vx r u s) + Vx r u s) (Wy r) :=
          congrArg (fun v => Hx r v (Wy r)) hδ
        _ = _ := by
          dsimp [Hx]
          exact spatialSecondDerivativeEval_add_left b r (X r x s)
            (X r (x + u) s - X r x s - Vx r u s) (Vx r u s) (Wy r)
    have hright : Hx r (Vx r u s) (Wy r - Wx r) =
        Hx r (Vx r u s) (Wy r) - Hx r (Vx r u s) (Wx r) := by
      have hsum : Wy r = (Wy r - Wx r) + Wx r := by abel
      have hadd : Hx r (Vx r u s) ((Wy r - Wx r) + Wx r) =
          Hx r (Vx r u s) (Wy r - Wx r) + Hx r (Vx r u s) (Wx r) := by
        dsimp [Hx]
        exact spatialSecondDerivativeEval_add_right b r (X r x s)
          (Vx r u s) (Wy r - Wx r) (Wx r)
      calc
        Hx r (Vx r u s) (Wy r - Wx r) =
            (Hx r (Vx r u s) (Wy r - Wx r) + Hx r (Vx r u s) (Wx r)) -
              Hx r (Vx r u s) (Wx r) := by abel
        _ = Hx r (Vx r u s) (Wy r) - Hx r (Vx r u s) (Wx r) := by
          rw [← hadd, ← hsum]
    rw [hleft, hright]
    abel
  have hSsplit (r : ℝ) :
      Hy r (Vy r h s) (Vy r k s) - Hx r (Vx r h s) (Vx r k s) -
          Tx r (Vx r u s) (Vx r h s) (Vx r k s) -
          Hx r (Wuh r) (Vx r k s) - Hx r (Wuk r) (Vx r h s) =
        (Hy r (Vy r h s) (Vy r k s) - Hx r (Vy r h s) (Vy r k s) -
            Tx r (X r (x + u) s - X r x s) (Vy r h s) (Vy r k s)) +
          Tx r (X r (x + u) s - X r x s - Vx r u s) (Vy r h s) (Vy r k s) +
          Tx r (Vx r u s) (Vy r h s - Vx r h s) (Vy r k s) +
          Tx r (Vx r u s) (Vx r h s) (Vy r k s - Vx r k s) +
          Hx r ((Vy r h s - Vx r h s) - Wuh r) (Vy r k s) +
          Hx r (Wuh r) (Vy r k s - Vx r k s) +
          Hx r (Vx r h s) ((Vy r k s - Vx r k s) - Wuk r) := by
    let a := Vy r h s
    let b₀ := Vx r h s
    let c := Vy r k s
    let d₀ := Vx r k s
    let p := Vx r u s
    let da := a - b₀
    let dc := c - d₀
    have ha : a = da + b₀ := by dsimp [a, b₀, da]; abel
    have hc : c = dc + d₀ := by dsimp [c, d₀, dc]; abel
    have hTδ : Tx r (X r (x + u) s - X r x s) a c =
        Tx r (X r (x + u) s - X r x s - p) a c +
          Tx r p a c := by
      have hδ : X r (x + u) s - X r x s =
          (X r (x + u) s - X r x s - p) + p := by abel
      calc
        _ = Tx r ((X r (x + u) s - X r x s - p) + p) a c :=
          congrArg (fun v => Tx r v a c) hδ
        _ = _ := by
          dsimp [Tx]
          exact spatialThirdDerivativeEval_add_left hb r (X r x s)
            (X r (x + u) s - X r x s - p) p a c
    have hTdiff : Tx r p a c - Tx r p b₀ d₀ =
        Tx r p da c + Tx r p b₀ dc := by
      rw [ha, hc]
      dsimp [Tx]
      simp only [spatialThirdDerivativeEval_add_middle hb,
        spatialThirdDerivativeEval_add_right hb]
      abel
    have hHdiff : Hx r a c - Hx r b₀ d₀ =
        Hx r da c + Hx r b₀ dc := by
      rw [ha, hc]
      dsimp [Hx]
      simp only [spatialSecondDerivativeEval_add_left b,
        spatialSecondDerivativeEval_add_right b]
      abel
    let e := da - Wuh r
    have he : da = e + Wuh r := by dsimp [e]; abel
    have hHleft : Hx r da c - Hx r (Wuh r) d₀ =
        Hx r e c + Hx r (Wuh r) dc := by
      rw [he, hc]
      dsimp [Hx]
      simp only [spatialSecondDerivativeEval_add_left b,
        spatialSecondDerivativeEval_add_right b]
      abel
    have hHcomm : Hx r (Wuk r) b₀ = Hx r b₀ (Wuk r) := by
      dsimp [Hx]
      exact spatialSecondDerivativeEval_comm hb r (X r x s) (Wuk r) b₀
    let f := dc - Wuk r
    have hf : dc = f + Wuk r := by dsimp [f]; abel
    have hHright : Hx r b₀ dc - Hx r b₀ (Wuk r) = Hx r b₀ f := by
      rw [hf]
      dsimp [Hx]
      simp only [spatialSecondDerivativeEval_add_right b]
      abel
    dsimp [a, b₀, c, d₀, p, da, dc, e, f] at hTδ hTdiff hHdiff hHleft hHcomm hHright ⊢
    linear_combination hTδ + hTdiff + hHdiff + hHleft + hHright - hHcomm
  have hEone : 1 ≤ E := by
    dsimp [E]
    exact Real.one_le_exp_iff.mpr (mul_nonneg hM₀ hd₀)
  let P : ℝ := ‖u‖ * ‖u‖ * ‖h‖ * ‖k‖
  let Csource : ℝ :=
    TH * E * E * F * F + C₃ * Ctraj * E * E +
      2 * C₃ * Kvar * E * E + C₂ * Crem * E +
      C₂ * K₂ * Kvar + C₂ * E * Crem
  have hforceParts (r : ℝ) (hr : r ∈ Ico s t) :
      ‖Ay r (Wy r) - Ax r (Wy r) - Hx r (Vx r u s) (Wx r)‖ ≤
          (TA * K₂ * F * F * E + C₂ * Ctraj * K₂ + C₂ * E * K₂diff) * P ∧
        ‖Hy r (Vy r h s) (Vy r k s) - Hx r (Vx r h s) (Vx r k s) -
            Tx r (Vx r u s) (Vx r h s) (Vx r k s) -
            Hx r (Wuh r) (Vx r k s) - Hx r (Wuk r) (Vx r h s)‖ ≤ Csource * P := by
    have hrc : r ∈ Icc s t := ⟨hr.1, le_of_lt hr.2⟩
    let δ : Vec 2 := X r (x + u) s - X r x s
    have hδ : ‖δ‖ ≤ F * ‖u‖ := by simpa [δ] using htrajQ r hrc
    have hδrem : ‖δ - Vx r u s‖ ≤ Ctraj * ‖u‖ * ‖u‖ := by
      simpa [δ] using htrajRem r hrc
    have hTaylorId : Hx r δ (Wy r) =
        fderiv ℝ (fun z => jointSpatialFDeriv b r z (Wy r))
          (X r x s) δ := by
      exact spatialSecondDerivativeEval_eq_spatialJacobianFDeriv_apply
        hb r (X r x s) δ (Wy r)
    have hTaylor := hTA r (X r x s) (X r (x + u) s) (Wy r)
    rw [← hTaylorId] at hTaylor
    have hAtaylor : ‖Ay r (Wy r) - Ax r (Wy r) - Hx r δ (Wy r)‖ ≤
        TA * ‖Wy r‖ * ‖δ‖ * ‖δ‖ := by
      simpa [Ay, Ax, δ] using hTaylor
    have hAtaylor' :
        ‖Ay r (Wy r) - Ax r (Wy r) - Hx r δ (Wy r)‖ ≤
          (TA * K₂ * F * F * E) * P := by
      calc
        _ ≤ TA * (K₂ * ‖h‖ * ‖k‖) * (F * ‖u‖) * (F * ‖u‖) := by
          apply hAtaylor.trans
          gcongr
          exact hWboundY r hrc
        _ = (TA * K₂ * F * F) * P := by dsimp [P]; ring
        _ ≤ (TA * K₂ * F * F * E) * P := by
          have hcoeff : TA * K₂ * F * F ≤ TA * K₂ * F * F * E := by
            calc
              _ = (TA * K₂ * F * F) * 1 := by ring
              _ ≤ (TA * K₂ * F * F) * E :=
                mul_le_mul_of_nonneg_left hEone (by positivity)
              _ = _ := by ring
          exact mul_le_mul_of_nonneg_right hcoeff (by positivity)
    have hArem₁ : ‖Hx r (δ - Vx r u s) (Wy r)‖ ≤
        (C₂ * Ctraj * K₂) * P := by
      calc
        _ ≤ C₂ * ‖δ - Vx r u s‖ * ‖Wy r‖ := hC₂ r (X r x s) _ _
        _ ≤ C₂ * (Ctraj * ‖u‖ * ‖u‖) * (K₂ * ‖h‖ * ‖k‖) := by
          gcongr
          exact hWboundY r hrc
        _ = (C₂ * Ctraj * K₂) * P := by dsimp [P]; ring
    have hArem₂ : ‖Hx r (Vx r u s) (Wy r - Wx r)‖ ≤
        (C₂ * E * K₂diff) * P := by
      calc
        _ ≤ C₂ * ‖Vx r u s‖ * ‖Wy r - Wx r‖ := hC₂ r (X r x s) _ _
        _ ≤ C₂ * (E * ‖u‖) * (K₂diff * ‖u‖ * ‖h‖ * ‖k‖) := by
          gcongr
          exact hVxBound u r hr
          exact hWdiffQ r hrc
        _ = (C₂ * E * K₂diff) * P := by dsimp [P]; ring
    have hA :
        ‖Ay r (Wy r) - Ax r (Wy r) - Hx r (Vx r u s) (Wx r)‖ ≤
          (TA * K₂ * F * F * E + C₂ * Ctraj * K₂ + C₂ * E * K₂diff) * P := by
      rw [hAsplit r]
      calc
        ‖(Ay r (Wy r) - Ax r (Wy r) - Hx r δ (Wy r)) +
            Hx r (δ - Vx r u s) (Wy r) +
            Hx r (Vx r u s) (Wy r - Wx r)‖ ≤
          ‖Ay r (Wy r) - Ax r (Wy r) - Hx r δ (Wy r)‖ +
            ‖Hx r (δ - Vx r u s) (Wy r)‖ +
            ‖Hx r (Vx r u s) (Wy r - Wx r)‖ := by
          calc
            _ ≤ ‖(Ay r (Wy r) - Ax r (Wy r) - Hx r δ (Wy r)) +
                  Hx r (δ - Vx r u s) (Wy r)‖ +
                ‖Hx r (Vx r u s) (Wy r - Wx r)‖ := norm_add_le _ _
            _ ≤ _ := add_le_add (norm_add_le _ _) (le_refl _)
        _ ≤ (TA * K₂ * F * F * E) * P +
              (C₂ * Ctraj * K₂) * P + (C₂ * E * K₂diff) * P := by
          exact add_le_add (add_le_add hAtaylor' hArem₁) hArem₂
        _ = _ := by ring
    refine ⟨hA, ?_⟩
    let a : Vec 2 := Vy r h s
    let b₀ : Vec 2 := Vx r h s
    let c : Vec 2 := Vy r k s
    let d₀ : Vec 2 := Vx r k s
    have ha : ‖a‖ ≤ E * ‖h‖ := by simpa [a] using hVyBound h r hr
    have hb₀ : ‖b₀‖ ≤ E * ‖h‖ := by simpa [b₀] using hVxBound h r hr
    have hc : ‖c‖ ≤ E * ‖k‖ := by simpa [c] using hVyBound k r hr
    have hd₀ : ‖d₀‖ ≤ E * ‖k‖ := by simpa [d₀] using hVxBound k r hr
    have hdiffh : ‖a - b₀‖ ≤ Kvar * ‖u‖ * ‖h‖ := by
      simpa [a, b₀] using hVdiffQ r hrc h
    have hdiffk : ‖c - d₀‖ ≤ Kvar * ‖u‖ * ‖k‖ := by
      simpa [c, d₀] using hVdiffQ r hrc k
    have hremh : ‖(a - b₀) - Wuh r‖ ≤ Crem * ‖u‖ * ‖u‖ * ‖h‖ := by
      simpa [a, b₀, Wuh] using hVrem r hrc h
    have hremk : ‖(c - d₀) - Wuk r‖ ≤ Crem * ‖u‖ * ‖u‖ * ‖k‖ := by
      simpa [c, d₀, Wuk] using hVrem r hrc k
    have hWuh : ‖Wuh r‖ ≤ K₂ * ‖u‖ * ‖h‖ := by
      have h := hW₂x r hrc u h
      rw [hK₂xEq'] at h
      simpa [Wuh] using h
    have hWuk : ‖Wuk r‖ ≤ K₂ * ‖u‖ * ‖k‖ := by
      have h := hW₂x r hrc u k
      rw [hK₂xEq'] at h
      simpa [Wuk] using h
    have hS₁ : ‖Hy r a c - Hx r a c - Tx r δ a c‖ ≤
        (TH * E * E * F * F) * P := by
      have ht := hTH r (X r x s) (X r (x + u) s) a c
      simpa [Hy, Hx, Tx, δ] using (calc
        ‖Hy r a c - Hx r a c - Tx r δ a c‖ ≤
            TH * ‖a‖ * ‖c‖ * ‖δ‖ * ‖δ‖ := ht
        _ ≤ TH * (E * ‖h‖) * (E * ‖k‖) * (F * ‖u‖) * (F * ‖u‖) := by
          gcongr
        _ = (TH * E * E * F * F) * P := by dsimp [P]; ring)
    have hS₂ : ‖Tx r (δ - Vx r u s) a c‖ ≤
        (C₃ * Ctraj * E * E) * P := by
      calc
        _ ≤ C₃ * ‖δ - Vx r u s‖ * ‖a‖ * ‖c‖ := by
          simpa [Tx] using hC₃ r (X r x s) (δ - Vx r u s) a c
        _ ≤ C₃ * (Ctraj * ‖u‖ * ‖u‖) * (E * ‖h‖) * (E * ‖k‖) := by
          gcongr
        _ = (C₃ * Ctraj * E * E) * P := by dsimp [P]; ring
    have hS₃ : ‖Tx r (Vx r u s) (a - b₀) c‖ ≤
        (C₃ * Kvar * E * E) * P := by
      calc
        _ ≤ C₃ * ‖Vx r u s‖ * ‖a - b₀‖ * ‖c‖ := by
          simpa [Tx] using hC₃ r (X r x s) (Vx r u s) (a - b₀) c
        _ ≤ C₃ * (E * ‖u‖) * (Kvar * ‖u‖ * ‖h‖) * (E * ‖k‖) := by
          gcongr
          exact hVxBound u r hr
        _ = (C₃ * Kvar * E * E) * P := by dsimp [P]; ring
    have hS₄ : ‖Tx r (Vx r u s) b₀ (c - d₀)‖ ≤
        (C₃ * Kvar * E * E) * P := by
      calc
        _ ≤ C₃ * ‖Vx r u s‖ * ‖b₀‖ * ‖c - d₀‖ := by
          simpa [Tx] using hC₃ r (X r x s) (Vx r u s) b₀ (c - d₀)
        _ ≤ C₃ * (E * ‖u‖) * (E * ‖h‖) * (Kvar * ‖u‖ * ‖k‖) := by
          gcongr
          exact hVxBound u r hr
        _ = (C₃ * Kvar * E * E) * P := by dsimp [P]; ring
    have hS₅ : ‖Hx r ((a - b₀) - Wuh r) c‖ ≤
        (C₂ * Crem * E) * P := by
      calc
        _ ≤ C₂ * ‖(a - b₀) - Wuh r‖ * ‖c‖ := hC₂ r (X r x s) _ _
        _ ≤ C₂ * (Crem * ‖u‖ * ‖u‖ * ‖h‖) * (E * ‖k‖) := by
          gcongr
        _ = (C₂ * Crem * E) * P := by dsimp [P]; ring
    have hS₆ : ‖Hx r (Wuh r) (c - d₀)‖ ≤
        (C₂ * K₂ * Kvar) * P := by
      calc
        _ ≤ C₂ * ‖Wuh r‖ * ‖c - d₀‖ := hC₂ r (X r x s) _ _
        _ ≤ C₂ * (K₂ * ‖u‖ * ‖h‖) * (Kvar * ‖u‖ * ‖k‖) := by
          gcongr
        _ = (C₂ * K₂ * Kvar) * P := by dsimp [P]; ring
    have hS₇ : ‖Hx r b₀ ((c - d₀) - Wuk r)‖ ≤
        (C₂ * E * Crem) * P := by
      calc
        _ ≤ C₂ * ‖b₀‖ * ‖(c - d₀) - Wuk r‖ := hC₂ r (X r x s) _ _
        _ ≤ C₂ * (E * ‖h‖) * (Crem * ‖u‖ * ‖u‖ * ‖k‖) := by
          gcongr
        _ = (C₂ * E * Crem) * P := by dsimp [P]; ring
    let e₁ : Vec 2 := Hy r a c - Hx r a c - Tx r δ a c
    let e₂ : Vec 2 := Tx r (δ - Vx r u s) a c
    let e₃ : Vec 2 := Tx r (Vx r u s) (a - b₀) c
    let e₄ : Vec 2 := Tx r (Vx r u s) b₀ (c - d₀)
    let e₅ : Vec 2 := Hx r ((a - b₀) - Wuh r) c
    let e₆ : Vec 2 := Hx r (Wuh r) (c - d₀)
    let e₇ : Vec 2 := Hx r b₀ ((c - d₀) - Wuk r)
    have hnorm₁₂ : ‖e₁ + e₂‖ ≤ ‖e₁‖ + ‖e₂‖ := norm_add_le _ _
    have hnorm₁₃ : ‖e₁ + e₂ + e₃‖ ≤ ‖e₁‖ + ‖e₂‖ + ‖e₃‖ := by
      calc
        _ ≤ ‖e₁ + e₂‖ + ‖e₃‖ := norm_add_le _ _
        _ ≤ _ := add_le_add hnorm₁₂ (le_refl _)
    have hnorm₁₄ : ‖e₁ + e₂ + e₃ + e₄‖ ≤ ‖e₁‖ + ‖e₂‖ + ‖e₃‖ + ‖e₄‖ := by
      calc
        _ ≤ ‖e₁ + e₂ + e₃‖ + ‖e₄‖ := norm_add_le _ _
        _ ≤ _ := add_le_add hnorm₁₃ (le_refl _)
    have hnorm₁₅ : ‖e₁ + e₂ + e₃ + e₄ + e₅‖ ≤
        ‖e₁‖ + ‖e₂‖ + ‖e₃‖ + ‖e₄‖ + ‖e₅‖ := by
      calc
        _ ≤ ‖e₁ + e₂ + e₃ + e₄‖ + ‖e₅‖ := norm_add_le _ _
        _ ≤ _ := add_le_add hnorm₁₄ (le_refl _)
    have hnorm₁₆ : ‖e₁ + e₂ + e₃ + e₄ + e₅ + e₆‖ ≤
        ‖e₁‖ + ‖e₂‖ + ‖e₃‖ + ‖e₄‖ + ‖e₅‖ + ‖e₆‖ := by
      calc
        _ ≤ ‖e₁ + e₂ + e₃ + e₄ + e₅‖ + ‖e₆‖ := norm_add_le _ _
        _ ≤ _ := add_le_add hnorm₁₅ (le_refl _)
    have hnorm₁₇ : ‖e₁ + e₂ + e₃ + e₄ + e₅ + e₆ + e₇‖ ≤
        ‖e₁‖ + ‖e₂‖ + ‖e₃‖ + ‖e₄‖ + ‖e₅‖ + ‖e₆‖ + ‖e₇‖ := by
      calc
        _ ≤ ‖e₁ + e₂ + e₃ + e₄ + e₅ + e₆‖ + ‖e₇‖ := norm_add_le _ _
        _ ≤ _ := add_le_add hnorm₁₆ (le_refl _)
    rw [hSsplit r]
    calc
      ‖(Hy r a c - Hx r a c - Tx r δ a c) +
          Tx r (δ - Vx r u s) a c + Tx r (Vx r u s) (a - b₀) c +
          Tx r (Vx r u s) b₀ (c - d₀) +
          Hx r ((a - b₀) - Wuh r) c + Hx r (Wuh r) (c - d₀) +
          Hx r b₀ ((c - d₀) - Wuk r)‖ ≤
        ‖Hy r a c - Hx r a c - Tx r δ a c‖ +
          ‖Tx r (δ - Vx r u s) a c‖ + ‖Tx r (Vx r u s) (a - b₀) c‖ +
          ‖Tx r (Vx r u s) b₀ (c - d₀)‖ +
          ‖Hx r ((a - b₀) - Wuh r) c‖ + ‖Hx r (Wuh r) (c - d₀)‖ +
          ‖Hx r b₀ ((c - d₀) - Wuk r)‖ := by
        simpa [e₁, e₂, e₃, e₄, e₅, e₆, e₇] using hnorm₁₇
    _ ≤ Csource * P := by
        dsimp [Csource]
        calc
          _ ≤ (TH * E * E * F * F) * P + (C₃ * Ctraj * E * E) * P +
              (C₃ * Kvar * E * E) * P + (C₃ * Kvar * E * E) * P +
              (C₂ * Crem * E) * P + (C₂ * K₂ * Kvar) * P +
              (C₂ * E * Crem) * P := by
            gcongr
          _ = _ := by ring
  let Source : ℝ → Vec 2 := fun r =>
    Hy r (Vy r h s) (Vy r k s) - Hx r (Vx r h s) (Vx r k s) -
      Tx r (Vx r u s) (Vx r h s) (Vx r k s) -
      Hx r (Wuh r) (Vx r k s) - Hx r (Wuk r) (Vx r h s)
  let G : ℝ → Vec 2 := fun r =>
    (Ay r (Wy r) - Ax r (Wy r) - Hx r (Vx r u s) (Wx r)) + Source r
  have hGbound (r : ℝ) (hr : r ∈ Ico s t) : ‖G r‖ ≤ Cforce * P := by
    obtain ⟨hA, hS⟩ := hforceParts r hr
    calc
      ‖(Ay r (Wy r) - Ax r (Wy r) - Hx r (Vx r u s) (Wx r)) + Source r‖ ≤
          ‖Ay r (Wy r) - Ax r (Wy r) - Hx r (Vx r u s) (Wx r)‖ +
            ‖Source r‖ := norm_add_le _ _
      _ ≤ (TA * K₂ * F * F * E + C₂ * Ctraj * K₂ + C₂ * E * K₂diff) * P +
            Csource * P := add_le_add hA hS
      _ = Cforce * P := by dsimp [Cforce, Csource]; ring
  let R : ℝ → Vec 2 := fun r => Wy r - Wx r - Z r
  let f : ℝ → Vec 2 := fun _ => 0
  let g : ℝ → Vec 2 := fun r => R r
  let ε : ℝ := Cforce * P
  have hAL : ∀ r v w, ‖Ax r v - Ax r w‖ ≤ M * ‖v - w‖ := by
    intro r v w
    calc
      ‖Ax r v - Ax r w‖ = ‖Ax r (v - w)‖ := by rw [map_sub]
      _ ≤ ‖Ax r‖ * ‖v - w‖ := (Ax r).le_opNorm _
      _ ≤ M * ‖v - w‖ :=
        mul_le_mul_of_nonneg_right (hM r (X r x s)) (norm_nonneg _)
  let KN : ℝ≥0 := ⟨M, hM₀⟩
  have hALipschitz : ∀ r, LipschitzWith KN (Ax r) := by
    intro r
    apply LipschitzWith.of_dist_le_mul
    intro v w
    rw [dist_eq_norm, dist_eq_norm]
    exact hAL r v w
  have hWxFlow := flowSecondVariation_isFlow hb hX x s hVx h k
  have hWyFlow := flowSecondVariation_isFlow hb hX (x + u) s hVy h k
  have hZFlow := flowThirdVariation_isFlow hb hX x s hVx u h k
  have hRderiv (r : ℝ) : HasDerivAt R (Ax r (R r) + G r) r := by
    have hsum := (hWyFlow.2 0 s r).sub (hWxFlow.2 0 s r)
    have hsub := hsum.sub (hZFlow.2 0 s r)
    have hcomm : Hx r (Wx r) (Vx r u s) = Hx r (Vx r u s) (Wx r) := by
      dsimp [Hx, Wx]
      exact spatialSecondDerivativeEval_comm hb r (X r x s)
        (flowSecondVariation hb hX x s hVx h k r 0 s) (Vx r u s)
    convert hsub using 1
    ext i
    simp [R, G, Source, Wx, Wy, Z, Wuh, Wuk, Ax, Ay, Hx, Hy, Tx,
      map_sub, hcomm]
    abel
  have hfderiv (r : ℝ) : HasDerivAt f (Ax r (f r)) r := by
    simpa [f] using (hasDerivAt_const r (0 : Vec 2))
  have hgderiv (r : ℝ) : HasDerivAt g (Ax r (g r) + G r) r := by
    simpa [g, R] using hRderiv r
  have hfcont : ContinuousOn f (Icc s t) := continuousOn_const
  have hgcont : ContinuousOn g (Icc s t) :=
    HasDerivAt.continuousOn (fun r _ => hgderiv r)
  have hfwithin : ∀ r ∈ Ico s t,
      HasDerivWithinAt f (Ax r (f r)) (Ici r) r :=
    fun r _ => (hfderiv r).hasDerivWithinAt
  have hgwithin : ∀ r ∈ Ico s t,
      HasDerivWithinAt g (Ax r (g r) + G r) (Ici r) r :=
    fun r _ => (hgderiv r).hasDerivWithinAt
  have hfapprox : ∀ r ∈ Ico s t,
      dist (Ax r (f r)) (Ax r (f r)) ≤ (0 : ℝ) := by
    intro r hr
    simp
  have hgapprox : ∀ r ∈ Ico s t,
      dist (Ax r (g r) + G r) (Ax r (g r)) ≤ ε := by
    intro r hr
    rw [dist_eq_norm, add_sub_cancel_left]
    simpa [ε, P] using hGbound r hr
  have hstart : dist (f s) (g s) ≤ (0 : ℝ) := by
    simp [f, g, R, Wy, Wx, Z, hWyFlow.1, hWxFlow.1, hZFlow.1]
  have hcomp := dist_le_of_approx_trajectories_ODE
    (K := KN) (v := fun r z => Ax r z)
    (f := f) (g := g)
    (f' := fun r => Ax r (f r))
    (g' := fun r => Ax r (g r) + G r)
    (a := s) (b := t) (εf := 0) (εg := ε) (δ := 0)
    hALipschitz hfcont hfwithin hfapprox hgcont hgwithin hgapprox hstart
  have hKcast : (KN : ℝ) = M := rfl
  have hdist := hcomp q hq
  have hdist' : ‖R q‖ ≤ gronwallBound 0 M ε (q - s) := by
    simpa [f, g, R, dist_eq_norm, hKcast, zero_add, norm_sub_rev] using hdist
  have htime : q - s ≤ d := by dsimp [d]; linarith [hq.2]
  have hmono := gronwallBound_mono
    (show 0 ≤ (0 : ℝ) by norm_num) hCforce₀ hM₀
  have hscale : gronwallBound 0 M ε (q - s) =
      P * gronwallBound 0 M Cforce (q - s) := by
    rw [show ε = P * Cforce by dsimp [ε, P]; ring]
    rw [ThirdSpatialRemainder.gronwallBound_zero_scale_thirdSpatialRemainder M Cforce P (q - s)]
  have hCbound : gronwallBound 0 M Cforce (q - s) ≤ C := by
    dsimp [C]
    exact hmono htime
  have hP₀ : 0 ≤ P := by dsimp [P]; positivity
  calc
    ‖flowSecondVariation hb hX (x + u) s hVy h k q 0 s -
        flowSecondVariation hb hX x s hVx h k q 0 s -
        flowThirdVariation hb hX x s hVx u h k q 0 s‖ = ‖R q‖ := by
          simp [R, Wy, Wx, Z]
    _ ≤ gronwallBound 0 M ε (q - s) := hdist'
    _ = P * gronwallBound 0 M Cforce (q - s) := hscale
    _ ≤ P * C := mul_le_mul_of_nonneg_left hCbound hP₀
    _ = C * ‖u‖ * ‖u‖ * ‖h‖ * ‖k‖ := by dsimp [P]; ring

end AVenhance.Infra.Flow
