module

public import RequestProject.Euler.CircularAncientCaptureEntrance
public import RequestProject.Euler.CircularCaptureBackwardMoment

/-! A fixed original ancient section admits arbitrarily small earlier
capture seeds, chosen before rho and the finite cutoff. The actual
section norm and the proved forward capture envelope then enforce a
minimum capture duration, rather than assuming a lookback fits. -/

@[expose] public section

set_option maxHeartbeats 16000000
set_option maxRecDepth 6500

noncomputable section

open Complex Set Filter Topology Metric
open scoped NNReal ENNReal

namespace Euler2D

attribute [local instance 2000] ancientSeedLittle_group ancientSeedLittle_space ancientSeedFamily_tower
  ancientSeedTangent_group ancientSeedTangent_space ancientSeedTangent_continuousAdd
attribute [local irreducible] circularConstrainedTangentSubmodule circularConstrainedUnstableProjectionCLM
  circularConstrainedChart circularConstraintProjectionToTangentCLM

theorem circularCapture_section_time_gt_of_small_seed {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1)
    {H seed δ L exit : ℝ} (hH : 0 ≤ H) (hseed : 0 ≤ seed)
    (y : ℝ → Fin 2 → LittleContourSpace γ)
    (hforward : ‖y exit - littleCircularMaterialContours hγ hγ1 exit‖ ≤
      H * seed * Real.exp (sigma * exit))
    (hsection : ‖circularConstrainedUnstableProjectionCLM hγ hγ1.le
      (circularConstraintProjectionToTangentCLM hγ hγ1.le
        (circularCoRotationCLM γ exit (y exit) - littleCircularReference hγ hγ1))‖ = δ)
    (hsmall : (‖circularConstrainedUnstableProjectionCLM hγ hγ1.le‖ *
      ‖circularConstraintProjectionToTangentCLM hγ hγ1.le‖) * H * seed * Real.exp (sigma * L) < δ) :
    L < exit := by
  let Q := circularConstrainedUnstableProjectionCLM hγ hγ1.le
  let J := circularConstraintProjectionToTangentCLM hγ hγ1.le
  have hbound : δ ≤ (‖Q‖ * ‖J‖) * H * seed * Real.exp (sigma * exit) := by
    rw [← hsection]
    calc
      _ ≤ ‖Q‖ * ‖J (circularCoRotationCLM γ exit (y exit) - littleCircularReference hγ hγ1)‖ := Q.le_opNorm _
      _ ≤ ‖Q‖ * (‖J‖ * ‖circularCoRotationCLM γ exit (y exit) - littleCircularReference hγ hγ1‖) :=
        mul_le_mul_of_nonneg_left (J.le_opNorm _) (norm_nonneg Q)
      _ = (‖Q‖ * ‖J‖) * ‖y exit - littleCircularMaterialContours hγ hγ1 exit‖ := by
        rw [norm_circularCoRotationCLM_sub_reference hγ hγ1]
        ring
      _ ≤ (‖Q‖ * ‖J‖) * (H * seed * Real.exp (sigma * exit)) :=
        mul_le_mul_of_nonneg_left hforward (mul_nonneg (norm_nonneg Q) (norm_nonneg J))
      _ = _ := by ring
  by_contra hbad
  have hexit : exit ≤ L := not_lt.mp hbad
  have he : Real.exp (sigma * exit) ≤ Real.exp (sigma * L) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hexit sigma_pos.le)
  have hh := mul_le_mul_of_nonneg_left he
    (show 0 ≤ (‖Q‖ * ‖J‖) * H * seed by positivity)
  exact (not_lt_of_ge (hbound.trans hh)) hsmall

namespace CircularMaterialTransferProfile

variable {γ : ℝ≥0} {hγ : 0 < γ} {hγ1 : (γ : ℝ) < 1}
    (P : CircularMaterialTransferProfile hγ hγ1)

theorem exists_actual_ancient_capture_entrance_arbitrarily_small
    {F : CircularConstrainedTangentSpace γ → CircularConstrainedTangentSpace γ} {r : ℝ}
    {x : CircularConstrainedTangentSpace γ → ℕ → CircularConstrainedTangentSpace γ}
    (hg : IsLocalWeightedBackwardGraph F (circularConstrainedUnstableProjectionCLM hγ hγ1.le)
      circularAncientBackwardWeight r x)
    (hsamples : ∃ N : ℕ, ∀ n ≥ N, ∃ α : CircularConstrainedTangentSpace γ,
      circularConstrainedUnstableProjectionCLM hγ hγ1.le α = α ∧ ‖α‖ ≤ r / 2 ∧
      P.ancient (-(n : ℝ) * (period + period)) = circularConstrainedChart hγ hγ1 (x α 0))
    {lam Damp η : ℝ} (hlam : 1 < lam) (hDamp : 0 < Damp) (hη : 0 < η) :
    ∃ δ > 0, ∀ seedBound > 0, ∀ nMin : ℕ, ∃ n ≥ nMin,
      let s := -(n : ℝ) * (period + period)
      let v := circularConstraintProjectionToTangentCLM hγ hγ1.le
        (P.ancient s - littleCircularReference hγ hγ1)
      let α := circularConstrainedUnstableProjectionCLM hγ hγ1.le v
      s ≤ 0 ∧ (∀ i, ‖(P.ancient s i).val - circularReferenceC1 hγ hγ1 i‖ ≤ η) ∧
      0 < ‖α‖ ∧ ‖α‖ < δ ∧ ‖α‖ < seedBound ∧ ‖α‖ ≤ r / 2 ∧
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
  refine ⟨δ, hδ, ?_⟩
  intro seedBound hseedBound nMin
  have hseed := P.ancient_flattened_samples_eventually_seed (F := F) (r := r) (x := x)
    hg hsamples (lt_min hδ hseedBound)
  have hnear : ∀ᶠ n : ℕ in atTop,
      ‖P.ancient (-(n : ℝ) * (period + period)) - littleCircularReference hγ hγ1‖ < η := by
    simpa only [mem_ball, dist_eq_norm] using
      P.ancient_samples_tendsto.eventually (Metric.ball_mem_nhds (littleCircularReference hγ hγ1) hη)
  obtain ⟨n, hnMin, hnseed, hnnear⟩ :=
    ((eventually_ge_atTop nMin).and (hseed.and hnear)).exists
  dsimp only at hnseed
  let s := -(n : ℝ) * (period + period)
  let v := circularConstraintProjectionToTangentCLM hγ hγ1.le
    (P.ancient s - littleCircularReference hγ hγ1)
  let α := circularConstrainedUnstableProjectionCLM hγ hγ1.le v
  obtain ⟨hs, hα, hαsmall, hαr, hv, hw⟩ := hnseed
  have hαδ : ‖α‖ < δ := hαsmall.trans_le (min_le_left _ _)
  have hαseed : ‖α‖ < seedBound := hαsmall.trans_le (min_le_right _ _)
  have hgeom : ∀ i, ‖(P.ancient s i).val - circularReferenceC1 hγ hγ1 i‖ ≤ η := by
    have hm := (pi_norm_le_iff_of_nonneg hη.le).mp hnnear.le
    intro i
    change ‖(P.ancient s - littleCircularReference hγ hγ1) i‖ ≤ η
    exact hm i
  obtain ⟨Ncap, hNcap, hcross, hterminal, hlog⟩ := exists_capture_finite_horizon hlam hα hαδ
  refine ⟨n, hnMin, hs, hgeom, hα, hαδ, hαseed, hαr, hv, hw, Ncap, hNcap,
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
