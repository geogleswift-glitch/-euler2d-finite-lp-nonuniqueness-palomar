module

public import RequestProject.Euler.CircularConstrainedReturnConjugacy

/-! Exact recovery of an existing chart coordinate from an actual
material endpoint in the image of the same chart. -/

@[expose] public section

set_option maxHeartbeats 2000000

noncomputable section

open scoped NNReal

namespace Euler2D

theorem circularConstrainedReturnMap_of_chart_endpoint {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1)
    (E : (Fin 2 → LittleContourSpace γ) → Fin 2 → LittleContourSpace γ)
    (v u : CircularConstrainedTangentSpace γ)
    (he : E (circularConstrainedChart hγ hγ1 v) = circularConstrainedChart hγ hγ1 u) :
    circularConstrainedReturnMap hγ hγ1 E v = u := by
  have hf : ∀ i, E (circularConstrainedChart hγ hγ1 v) i ∈ fourfoldLittleContourSubmodule γ := by
    rw [he]
    exact circularConstrainedChart_fourfold hγ hγ1 u
  apply Subtype.ext
  rw [circularConstrainedReturnMap_val_of_fourfold hγ hγ1 E v hf, he]
  exact circularAreaChartInverseFamily_chart hγ hγ1 u

end Euler2D

end
