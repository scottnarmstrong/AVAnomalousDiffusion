-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

module

public import AVenhance.Infra.Section5.Terms.ScaleTools
public import AVenhance.Infra.Section5.Terms

/-! Source-scale estimate for the complete `tiny` term. The mean-zero and
spatial L² premises are kept as explicit inputs. -/

@[expose] public section

noncomputable section
open MeasureTheory Homogenization
namespace AVenhance.Infra.Section5

open AVenhance

variable {β : ℝ} (I : Ingredients β) {Φ : ℕ → ℝ → Vec 2 → ℝ}

end AVenhance.Infra.Section5
end
