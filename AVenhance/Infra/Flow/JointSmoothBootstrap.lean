-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

module

public import AVenhance.Infra.Flow.JointC3All

/-! An all-orders joint-flow bootstrap from regularity of the spatial jet. -/

@[expose] public section

open Homogenization
open scoped ContDiff Topology

namespace AVenhance.Infra.Flow

noncomputable section

def JointSmoothBootstrap.flowTimeVelocityN
    (b : ℝ → Vec 2 → Vec 2) (X : ℝ → Vec 2 → ℝ → Vec 2)
    (p : ℝ × Vec 2 × ℝ) : Vec 2 :=
  b p.1 (X p.1 p.2.1 p.2.2)

def JointSmoothBootstrap.flowSpatialJacobianN
    (X : ℝ → Vec 2 → ℝ → Vec 2) (p : ℝ × Vec 2 × ℝ) :
    Vec 2 →L[ℝ] Vec 2 :=
  fderiv ℝ (fun y => X p.1 y p.2.2) p.2.1

def JointSmoothBootstrap.flowStartVelocityN
    (b : ℝ → Vec 2 → Vec 2) (X : ℝ → Vec 2 → ℝ → Vec 2)
    (p : ℝ × Vec 2 × ℝ) : Vec 2 :=
  -(JointSmoothBootstrap.flowSpatialJacobianN X p (b p.2.2 p.2.1))

def JointSmoothBootstrap.flowStartCLMN
    (b : ℝ → Vec 2 → Vec 2) (X : ℝ → Vec 2 → ℝ → Vec 2)
    (p : ℝ × Vec 2 × ℝ) : ℝ →L[ℝ] Vec 2 :=
  ContinuousLinearMap.toSpanSingleton ℝ (JointSmoothBootstrap.flowStartVelocityN b X p)

def JointSmoothBootstrap.flowParameterDerivativeN
    (b : ℝ → Vec 2 → Vec 2) (X : ℝ → Vec 2 → ℝ → Vec 2)
    (p : ℝ × Vec 2 × ℝ) : (Vec 2 × ℝ) →L[ℝ] Vec 2 :=
  (JointSmoothBootstrap.flowSpatialJacobianN X p).coprod (JointSmoothBootstrap.flowStartCLMN b X p)

def JointSmoothBootstrap.flowJointDerivativeN
    (b : ℝ → Vec 2 → Vec 2) (X : ℝ → Vec 2 → ℝ → Vec 2)
    (p : ℝ × Vec 2 × ℝ) : (ℝ × Vec 2 × ℝ) →L[ℝ] Vec 2 :=
  (ContinuousLinearMap.toSpanSingleton ℝ (JointSmoothBootstrap.flowTimeVelocityN b X p)).coprod
    (JointSmoothBootstrap.flowParameterDerivativeN b X p)

end

end AVenhance.Infra.Flow
