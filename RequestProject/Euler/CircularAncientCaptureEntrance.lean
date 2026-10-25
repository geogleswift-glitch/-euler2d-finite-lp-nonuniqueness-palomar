module

public import RequestProject.Euler.CircularFlattenedAncientCaptureSeed
public import RequestProject.Euler.CircularDeepestCaptureInitialState
public import RequestProject.Euler.CaptureFiniteHorizon

/-! Choose a genuine original ancient entrance, its positive section,
and a finite amplification horizon before choosing rho or a cutoff.
The flattened complement is exactly zero and the actual rho^6 source
budget then holds for all sufficiently small rho=exp(-xi). -/

@[expose] public section

set_option maxHeartbeats 8000000
set_option maxRecDepth 6000

noncomputable section

open Complex Set Filter Topology Metric
open scoped NNReal ENNReal

namespace Euler2D

attribute [local instance 2000] ancientSeedLittle_group ancientSeedLittle_space ancientSeedFamily_tower
  ancientSeedTangent_group ancientSeedTangent_space ancientSeedTangent_continuousAdd
attribute [local irreducible] circularConstrainedTangentSubmodule circularConstrainedUnstableProjectionCLM
  circularConstrainedChart circularConstraintProjectionToTangentCLM

namespace CircularMaterialTransferProfile

variable {γ : ℝ≥0} {hγ : 0 < γ} {hγ1 : (γ : ℝ) < 1}
    (P : CircularMaterialTransferProfile hγ hγ1)

theorem exists_actual_ancient_capture_entrance
    {F : CircularConstrainedTangentSpace γ → CircularConstrainedTangentSpace γ} {r : ℝ}
    {x : CircularConstrainedTangentSpace γ → ℕ → CircularConstrainedTangentSpace γ}
    (hg : IsLocalWeightedBackwardGraph F (circularConstrainedUnstableProjectionCLM hγ hγ1.le)
      circularAncientBackwardWeight r x)
    (hsamples : ∃ N : ℕ, ∀ n ≥ N, ∃ α : CircularConstrainedTangentSpace γ,
      circularConstrainedUnstableProjectionCLM hγ hγ1.le α = α ∧ ‖α‖ ≤ r / 2 ∧
      P.ancient (-(n : ℝ) * (period + period)) = circularConstrainedChart hγ hγ1 (x α 0))
    {lam Damp η : ℝ} (hlam : 1 < lam) (hDamp : 0 < Damp) (hη : 0 < η) :
    ∃ δ > 0, ∃ n : ℕ,
      let s := -(n : ℝ) * (period + period)
      let v := circularConstraintProjectionToTangentCLM hγ hγ1.le
        (P.ancient s - littleCircularReference hγ hγ1)
      let α := circularConstrainedUnstableProjectionCLM hγ hγ1.le v
      s ≤ 0 ∧ (∀ i, ‖(P.ancient s i).val - circularReferenceC1 hγ hγ1 i‖ ≤ η) ∧
      0 < ‖α‖ ∧ ‖α‖ < δ ∧ ‖α‖ ≤ r / 2 ∧
      v = x α 0 ∧ (v - α) - (x α 0 - α) = 0 ∧
      ∃ Ncap : ℕ, 0 < Ncap ∧ δ < (3 / 4 : ℝ) * ‖α‖ * lam ^ Ncap ∧
        ‖α‖ * lam ^ Ncap ≤ Damp ∧
        (Ncap : ℝ) ≤ Real.log ((4 / 3 : ℝ) * δ / ‖α‖) / Real.log lam + 1 ∧
        ∀ C B : ℝ, ∀ᶠ ξ : ℝ in atTop, C * B * Real.exp (-ξ) ^ 6 ≤ ‖α‖ / 32 := by
  have hlam0 : 0 < lam := zero_lt_one.trans hlam
  let δ := Damp / (4 * lam)
  have hδ : 0 < δ := div_pos hDamp (mul_pos (by norm_num) hlam0)
  have hwindow : (4 / 3 : ℝ) * lam * δ ≤ Damp := by
    have heq : (4 / 3 : ℝ) * lam * δ = Damp / 3 := by
      dsimp only [δ]
      field_simp [hlam0.ne']
      <;> ring
    rw [heq]
    linarith only [hDamp]
  have hseed := P.ancient_flattened_samples_eventually_seed (F := F) (r := r) (x := x) hg hsamples hδ
  have hnear : ∀ᶠ n : ℕ in atTop,
      ‖P.ancient (-(n : ℝ) * (period + period)) - littleCircularReference hγ hγ1‖ < η := by
    simpa only [mem_ball, dist_eq_norm] using
      P.ancient_samples_tendsto.eventually (Metric.ball_mem_nhds (littleCircularReference hγ hγ1) hη)
  obtain ⟨n, hnseed, hnnear⟩ := (hseed.and hnear).exists
  dsimp only at hnseed
  let s := -(n : ℝ) * (period + period)
  let v := circularConstraintProjectionToTangentCLM hγ hγ1.le
    (P.ancient s - littleCircularReference hγ hγ1)
  let α := circularConstrainedUnstableProjectionCLM hγ hγ1.le v
  obtain ⟨hs, hα, hαδ, hαr, hv, hw⟩ := hnseed
  have hgeom : ∀ i, ‖(P.ancient s i).val - circularReferenceC1 hγ hγ1 i‖ ≤ η := by
    have hm := (pi_norm_le_iff_of_nonneg hη.le).mp hnnear.le
    intro i
    change ‖(P.ancient s - littleCircularReference hγ hγ1) i‖ ≤ η
    exact hm i
  obtain ⟨Ncap, hNcap, hcross, hterminal, hlog⟩ := exists_capture_finite_horizon hlam hα hαδ
  refine ⟨δ, hδ, n, hs, hgeom, hα, hαδ, hαr, hv, hw, Ncap, hNcap,
    hcross, hterminal.trans hwindow, hlog, ?_⟩
  intro C B
  have hlim : Tendsto (fun ξ : ℝ => C * B * Real.exp (-ξ) ^ 6) atTop (𝓝 0) := by
    simpa only [zero_pow (by decide : (6 : ℕ) ≠ 0), mul_zero] using
      (Real.tendsto_exp_neg_atTop_nhds_zero.pow 6).const_mul (C * B)
  exact (hlim.eventually (eventually_lt_nhds (div_pos hα (by norm_num : (0 : ℝ) < 32)))).mono
    (fun _ h => h.le)

end CircularMaterialTransferProfile
end Euler2D

end
