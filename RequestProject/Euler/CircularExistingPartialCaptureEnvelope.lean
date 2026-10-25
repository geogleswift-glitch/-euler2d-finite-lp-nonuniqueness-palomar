module

public import RequestProject.Euler.CircularReferenceUniformTube
public import RequestProject.Euler.CircularAreaChartQuadratic
public import RequestProject.Euler.BanachCurrentBlockEnvelope

/-! The final partial capture block uses only the path on its actual
provisional interval. No existence on a later complete block is used. -/

@[expose] public section

set_option maxHeartbeats 9000000
set_option maxRecDepth 4500

noncomputable section

open Set Metric
open scoped NNReal

namespace Euler2D

attribute [local instance 2000] quadraticChartLittle_group quadraticChartLittle_space
  quadraticChartFamily_tower quadraticChartTangent_group quadraticChartTangent_space
  quadraticChartTangent_continuousAdd

attribute [local irreducible] circularConstrainedTangentSubmodule circularConstrainedChart
  circularBanachField circularBanachDomain

theorem exists_circular_existing_partial_capture_envelope {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1) {T : ℝ} (hT : 0 < T) :
    ∃ d > 0, ∃ r > 0, ∃ H > 0, ∃ κ₀ > 0,
      ∀ v ∈ closedBall (0 : CircularConstrainedTangentSpace γ) d,
      ∀ {B κ D : ℝ}, 0 ≤ B → 0 ≤ κ → κ ≤ κ₀ → D ∈ Icc (0 : ℝ) T →
      ∀ y p : ℝ → Fin 2 → LittleContourSpace γ,
        y 0 = circularConstrainedChart hγ hγ1 v →
        (∀ t ∈ Icc (0 : ℝ) D, HasDerivAt y (circularBanachField hγ hγ1 (y t) + p t) t) →
        (∀ t ∈ Icc (0 : ℝ) D, ‖y t - littleCircularMaterialContours hγ hγ1 t‖ ≤ r) →
        (∀ t ∈ Icc (0 : ℝ) D, ‖p t‖ ≤ B + κ * ‖y t - littleCircularMaterialContours hγ hγ1 t‖) →
        ∀ t ∈ Icc (0 : ℝ) D,
          ‖y t - littleCircularMaterialContours hγ hγ1 t‖ ≤ H * (‖v‖ + B) := by
  obtain ⟨U, _, _, _, K, r, hr, _, _, hLip, htube, _⟩ :=
    exists_circular_reference_uniform_lipschitz_tube hγ hγ1
  obtain ⟨Cc, hCc, d, hd, hchart⟩ := exists_circularConstrainedChart_quadratic_bound hγ hγ1
  let M := 1 + Cc * d
  let H₀ := 2 * Real.exp ((K : ℝ) * T)
  let H := H₀ * (M + T + 1)
  let κ₀ := (2 * (T * Real.exp ((K : ℝ) * T)))⁻¹
  have hM : 0 < M := by dsimp only [M]; positivity
  have hH₀ : 0 < H₀ := by dsimp only [H₀]; positivity
  have hH : 0 < H := by dsimp only [H]; positivity
  have hκ₀ : 0 < κ₀ := by dsimp only [κ₀]; positivity
  refine ⟨d, hd, r, hr, H, hH, κ₀, hκ₀, ?_⟩
  intro v hv B κ D hB hκ hκcap hD y p hinit hyd hnear hp t ht
  have hfull : 2 * (T * Real.exp ((K : ℝ) * T)) * κ ≤ 1 := by
    have hh := mul_le_mul_of_nonneg_left hκcap
      (show 0 ≤ 2 * (T * Real.exp ((K : ℝ) * T)) by positivity)
    simpa only [κ₀, mul_inv_cancel₀
      (show 2 * (T * Real.exp ((K : ℝ) * T)) ≠ 0 by positivity)] using hh
  have hprod : D * Real.exp ((K : ℝ) * D) ≤ T * Real.exp ((K : ℝ) * T) :=
    mul_le_mul hD.2 (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hD.2 K.coe_nonneg))
      (Real.exp_pos _).le hT.le
  have hsmall : 2 * (D * Real.exp ((K : ℝ) * D)) * κ ≤ 1 :=
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hprod (by norm_num : (0 : ℝ) ≤ 2)) hκ).trans hfull
  have hy0 : ‖y 0 - littleCircularMaterialContours hγ hγ1 0‖ ≤ M * ‖v‖ := by
    rw [littleCircularMaterialContours_zero, hinit]
    exact (hchart v hv).2
  have hym (u : ℝ) (hu : u ∈ Icc (0 : ℝ) D) : y u ∈ U :=
    htube u (by simpa only [mem_closedBall, dist_eq_norm] using hnear u hu)
  have hh := current_existing_block_envelope hLip hD.1 hB hκ y
    (littleCircularMaterialContours hγ hγ1) p hyd
    (fun u _ => by simpa only [circularBanachField] using
      littleCircularMaterialContours_hasDerivAt hγ hγ1 u)
    hym (fun u _ => htube u (mem_closedBall_self hr.le)) hp hsmall t ht
  have hcoef : 2 * Real.exp ((K : ℝ) * D) ≤ H₀ :=
    mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hD.2 K.coe_nonneg)) (by norm_num)
  have hsum : ‖y 0 - littleCircularMaterialContours hγ hγ1 0‖ + D * B ≤ M * ‖v‖ + T * B :=
    add_le_add hy0 (mul_le_mul_of_nonneg_right hD.2 hB)
  have hbound : ‖y t - littleCircularMaterialContours hγ hγ1 t‖ ≤ H₀ * (M * ‖v‖ + T * B) :=
    hh.trans (mul_le_mul hcoef hsum
      (add_nonneg (norm_nonneg _) (mul_nonneg hD.1 hB)) hH₀.le)
  have hs : M * ‖v‖ + T * B ≤ (M + T + 1) * (‖v‖ + B) := by
    nlinarith only [mul_nonneg hM.le hB, mul_nonneg hT.le (norm_nonneg v), norm_nonneg v, hB]
  exact hbound.trans ((mul_le_mul_of_nonneg_left hs hH₀.le).trans_eq (by dsimp only [H]; ring))

end Euler2D

end
