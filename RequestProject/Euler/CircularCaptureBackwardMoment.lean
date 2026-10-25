module

public import RequestProject.Euler.CircularStoppedSharpCaptureEnvelope
public import RequestProject.Euler.CircularBoundaryFourthMoment
public import RequestProject.Euler.CircularCoRotatedFlow

/-! The SAME stopped capture path has an exponential bound relative
to its actual endpoint. Its seed and capture duration cancel using
the already proved grid lower bound. The original boundary moment
vanishes at the circular reference and obeys the same past envelope. -/

@[expose] public section

set_option maxHeartbeats 14000000
set_option maxRecDepth 6500

noncomputable section

open Complex Set Filter Topology Metric
open scoped NNReal ContDiff

namespace Euler2D

attribute [local instance 2000] captureBlockLittle_group captureBlockLittle_space
  captureBlockFamily_tower captureBlockTangent_group captureBlockTangent_space
  captureBlockTangent_continuousAdd captureBlockEndo_monoid captureBlockTangent_complete

attribute [local irreducible] circularConstrainedTangentSubmodule
  circularConstrainedUnstableProjectionCLM circularConstraintProjectionToTangentCLM

theorem exists_circularBoundaryFourthMoment_moving_reference_bound {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1) :
    ∃ C > 0, ∃ r > 0, ∀ (t : ℝ) (Y : Fin 2 → LittleContourSpace γ),
      ‖Y - littleCircularMaterialContours hγ hγ1 t‖ ≤ r →
      ‖circularBoundaryFourthMoment Y‖ ≤ C * ‖Y - littleCircularMaterialContours hγ hγ1 t‖ := by
  have hf : ContDiff ℝ 1 (@circularBoundaryFourthMoment γ) :=
    (contDiff_circularBoundaryFourthMoment γ).of_le (by norm_num)
  obtain ⟨K, U, hU, hLip⟩ :=
    (hf.contDiffAt (x := littleCircularReference hγ hγ1)).exists_lipschitzOnWith
  obtain ⟨a, ha, haU⟩ := Metric.mem_nhds_iff.mp hU
  refine ⟨(K : ℝ) + 1, by positivity, a / 2, half_pos ha, ?_⟩
  intro t Y hY
  let Z := circularCoRotationCLM γ t Y
  have hnorm : ‖Z - littleCircularReference hγ hγ1‖ =
      ‖Y - littleCircularMaterialContours hγ hγ1 t‖ :=
    norm_circularCoRotationCLM_sub_reference hγ hγ1 t Y
  have hZU : Z ∈ U := haU (mem_ball_iff_norm.mpr (by
    rw [hnorm]
    exact hY.trans_lt (half_lt_self ha)))
  have hrefU : littleCircularReference hγ hγ1 ∈ U := haU (mem_ball_self ha)
  have hmoment : circularBoundaryFourthMoment Z = circularBoundaryFourthMoment Y :=
    circularBoundaryFourthMoment_parameterShift _ Y
  have hh := hLip.dist_le_mul Z hZU (littleCircularReference hγ hγ1) hrefU
  rw [dist_eq_norm, dist_eq_norm, circularBoundaryFourthMoment_reference hγ hγ1,
    sub_zero, hmoment, hnorm] at hh
  exact hh.trans (mul_le_mul_of_nonneg_right (by linarith : (K : ℝ) ≤ (K : ℝ) + 1) (norm_nonneg _))

theorem circularCapture_backward_envelope_of_stopped_bounds {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1) {k N : ℕ} (hk : 0 < k)
    {D H a r : ℝ} (hD : 0 ≤ D) (hH : 0 ≤ H) (ha : 0 ≤ a)
    (hDN : D ≤ (N : ℝ) * circularCaptureBlockTime k)
    (y : ℝ → Fin 2 → LittleContourSpace γ)
    (hforward : ∀ t ∈ Icc (0 : ℝ) D,
      ‖y t - littleCircularMaterialContours hγ hγ1 t‖ ≤ H * a * Real.exp (sigma * t))
    (hnear : ∀ t ∈ Icc (0 : ℝ) D, ‖y t - littleCircularMaterialContours hγ hγ1 t‖ ≤ r)
    (hlower : ∀ n ≤ N, (n : ℝ) * circularCaptureBlockTime k ≤ D →
      (3 / 4 : ℝ) * a * circularCaptureBlockMultiplier k ^ n ≤
        ‖circularConstrainedUnstableProjectionCLM hγ hγ1.le
          (circularConstraintProjectionToTangentCLM hγ hγ1.le
            (y ((n : ℝ) * circularCaptureBlockTime k) - littleCircularReference hγ hγ1))‖) :
    ∀ t ∈ Icc (0 : ℝ) D,
      ‖y t - littleCircularMaterialContours hγ hγ1 t‖ ≤
        (H * (4 / 3) * circularCaptureBlockMultiplier k *
          (‖circularConstrainedUnstableProjectionCLM hγ hγ1.le‖ *
            ‖circularConstraintProjectionToTangentCLM hγ hγ1.le‖)) * r *
              Real.exp (-sigma * (D - t)) := by
  let T := circularCaptureBlockTime k
  let lam := circularCaptureBlockMultiplier k
  let Q := circularConstrainedUnstableProjectionCLM hγ hγ1.le
  let J := circularConstraintProjectionToTangentCLM hγ hγ1.le
  have hT : 0 < T := circularCaptureBlockTime_pos hk
  have hLam : lam = Real.exp (sigma * T) := circularCaptureBlockMultiplier_eq_exp k
  have hLam0 : 0 ≤ lam := by rw [hLam]; exact (Real.exp_pos _).le
  let m := ⌊D / T⌋₊
  have hquot : 0 ≤ D / T := div_nonneg hD hT.le
  have hmT : (m : ℝ) * T ≤ D := (le_div_iff₀ hT).mp (Nat.floor_le hquot)
  have hmN : m ≤ N := by
    have hh := (Nat.floor_le hquot).trans ((div_le_iff₀ hT).mpr hDN)
    exact_mod_cast hh
  have hnext : D ≤ (m : ℝ) * T + T := by
    have hh := (div_lt_iff₀ hT).mp (Nat.lt_floor_add_one (D / T))
    nlinarith only [hh]
  have hperiod : Function.Periodic (littleCircularMaterialContours hγ hγ1) T :=
    (periodic_littleCircularMaterialContours hγ hγ1).nat_mul (2 * k)
  have hcgrid : littleCircularMaterialContours hγ hγ1 ((m : ℝ) * T) =
      littleCircularReference hγ hγ1 := by
    have hh := (hperiod.nat_mul m) 0
    simpa only [zero_add, littleCircularMaterialContours_zero] using hh
  have hygrid : ‖y ((m : ℝ) * T) - littleCircularReference hγ hγ1‖ ≤ r := by
    rw [← hcgrid]
    exact hnear _ ⟨mul_nonneg (Nat.cast_nonneg m) hT.le, hmT⟩
  have hprojection : ‖Q (J (y ((m : ℝ) * T) - littleCircularReference hγ hγ1))‖ ≤
      (‖Q‖ * ‖J‖) * r := by
    calc
      _ ≤ ‖Q‖ * ‖J (y ((m : ℝ) * T) - littleCircularReference hγ hγ1)‖ := Q.le_opNorm _
      _ ≤ ‖Q‖ * (‖J‖ * r) := mul_le_mul_of_nonneg_left
        ((J.le_opNorm _).trans (mul_le_mul_of_nonneg_left hygrid (norm_nonneg J))) (norm_nonneg Q)
      _ = _ := by ring
  have hseed : a * lam ^ m ≤ (4 / 3 : ℝ) * (‖Q‖ * ‖J‖) * r := by
    have hh := hlower m hmN hmT
    change (3 / 4 : ℝ) * a * lam ^ m ≤ ‖Q (J _)‖ at hh
    linarith only [hh, hprojection]
  have hpow : lam ^ m = Real.exp (sigma * ((m : ℝ) * T)) := by
    rw [hLam, ← Real.exp_nat_mul]
    congr 1
    ring
  have hExpD : Real.exp (sigma * D) ≤ lam * lam ^ m := by
    rw [hpow, hLam, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith only [hnext, sigma_pos]
  have hseedD : a * Real.exp (sigma * D) ≤
      (4 / 3 : ℝ) * lam * (‖Q‖ * ‖J‖) * r := by
    calc
      _ ≤ a * (lam * lam ^ m) := mul_le_mul_of_nonneg_left hExpD ha
      _ = lam * (a * lam ^ m) := by ring
      _ ≤ lam * ((4 / 3 : ℝ) * (‖Q‖ * ‖J‖) * r) := mul_le_mul_of_nonneg_left hseed hLam0
      _ = _ := by ring
  intro t ht
  have hExp : Real.exp (sigma * t) = Real.exp (sigma * D) * Real.exp (-sigma * (D - t)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc
    _ ≤ H * a * Real.exp (sigma * t) := hforward t ht
    _ = H * (a * Real.exp (sigma * D)) * Real.exp (-sigma * (D - t)) := by rw [hExp]; ring
    _ ≤ H * ((4 / 3 : ℝ) * lam * (‖Q‖ * ‖J‖) * r) * Real.exp (-sigma * (D - t)) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hseedD hH) (Real.exp_pos _).le
    _ = _ := by dsimp only [lam, Q, J]; ring

end Euler2D

end
