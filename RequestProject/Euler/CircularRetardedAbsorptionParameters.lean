module

public import RequestProject.Euler.CircularSlowCumulativeTransferChoice
public import RequestProject.Euler.CircularReferenceUniformTube
public import RequestProject.Euler.RetardedLogarithmicAbsorption

/-! The self-field constant is first fixed on one genuine all-time
circular reference tube. A nonzero transfer ratio of the same original
profile is then selected, before every rho and every logarithmic
capture horizon. The real geometric feedback is absorbable with every
fixed polynomial loss in that horizon. -/

@[expose] public section

set_option maxHeartbeats 3000000

noncomputable section

open Set Filter Topology Metric
open scoped NNReal

namespace Euler2D
namespace CircularMaterialTransferProfile

variable {γ : ℝ≥0} {hγ : 0 < γ} {hγ1 : (γ : ℝ) < 1}
    (P : CircularMaterialTransferProfile hγ hγ1)

theorem exists_nonzeroTransfer_uniformRetarded_response_parameters :
    ∃ U : Set (Fin 2 → LittleContourSpace γ), IsOpen U ∧
      U ⊆ circularBanachDomain hγ hγ1 ∧
      ∃ K : ℝ≥0, ∃ r > 0, ∃ L > 0,
      LipschitzOnWith K (circularBanachField hγ hγ1) U ∧
      (∀ t : ℝ, closedBall (littleCircularMaterialContours hγ hγ1 t) r ⊆ U) ∧
      (∀ Z ∈ U, ‖Z‖ ≤ L) ∧
      ∃ b ∈ Ioo (0 : ℝ) (1 / 4),
        bilateral P.moment ((b : ℂ) * (sigma + 5 / 4 * Complex.I)) ≠ 0 ∧
        6 * (K : ℝ) * b / ((1 - b) * sigma) < 1 / 2 ∧
        (∀ C feedback : ℝ, ∀ᶠ x : ℝ in atTop,
          2 * (b * retardedLogHorizon b (6 / sigma) C x *
            Real.exp ((K : ℝ) * b * retardedLogHorizon b (6 / sigma) C x)) *
            (feedback * b * (Real.exp (-x)) ^ 2 / (1 - b * (Real.exp (-x)) ^ 2)) ≤ 1) ∧
        (∀ (C : ℝ) (n : ℕ), Tendsto (fun x : ℝ =>
          (Real.exp (-x)) ^ 2 *
            (b * retardedLogHorizon b (6 / sigma) C x *
              Real.exp ((K : ℝ) * b * retardedLogHorizon b (6 / sigma) C x)) *
            (1 + retardedLogHorizon b (6 / sigma) C x) ^ n /
              (1 - b * (Real.exp (-x)) ^ 2)) atTop (𝓝 0)) := by
  obtain ⟨U, hU, hUD, _hUref, K, r, hr, L, hL, hLip, htube, hbound⟩ :=
    exists_circular_reference_uniform_lipschitz_tube hγ hγ1
  obtain ⟨b, hb, hnonzero, hslow⟩ := P.exists_nonzero_transfer_ratio_with_slow_cumulative_self K
  have hgap : (K : ℝ) * b * (6 / sigma) / (1 - b) < 2 := by
    have heq : (K : ℝ) * b * (6 / sigma) / (1 - b) =
        6 * (K : ℝ) * b / ((1 - b) * sigma) := by
      field_simp [sigma_pos.ne', ne_of_gt (show 0 < 1 - b by linarith [hb.2])]
      <;> ring
    rw [heq]
    linarith
  exact ⟨U, hU, hUD, K, r, hr, L, hL, hLip, htube, hbound,
    b, hb, hnonzero, hslow,
    fun C feedback => eventually_retardedResponse_absorption b K (6 / sigma) C feedback hgap,
    fun C n => tendsto_retardedResponse_geometric_polynomial b K (6 / sigma) C n hgap⟩

end CircularMaterialTransferProfile
end Euler2D

end
