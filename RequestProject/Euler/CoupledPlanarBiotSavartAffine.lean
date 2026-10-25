module

public import RequestProject.Euler.CoupledPlanarBiotSavartEstimate
public import RequestProject.Euler.PlanarBiotSavartL1Stability

/-! An epsilon-affine majorant for the actual singular nonlinear
particle comparison, valid for every uniform displacement bound. -/

@[expose] public section

set_option maxHeartbeats 4000000

noncomputable section

open MeasureTheory Set Filter Topology

namespace Euler2D

theorem planarMaterialBiotSavart_eq_spatial (w : R2 → ℝ)
    (X : R2 ≃ₜ R2) (hX : MeasurePreserving X volume volume) (x : R2) :
    planarMaterialLabelVelocity kernelK w X x =
      planarKernelVelocity kernelK (fun y => w (X.symm y)) x := by
  have hc := hX.integral_comp X.measurableEmbedding
    (fun y => w (X.symm y) • kernelK (x - y))
  simpa only [Homeomorph.symm_apply_apply] using hc

theorem norm_planarMaterialBiotSavart_le_sum
    {w : R2 → ℝ} {B : ℝ} (hw : Integrable w) (hB : ∀ b, ‖w b‖ ≤ B)
    (X : R2 ≃ₜ R2) (hX : MeasurePreserving X volume volume) (x : R2) :
    ‖planarMaterialLabelVelocity kernelK w X x‖ ≤ B + ∫ b, ‖w b‖ := by
  have hiX : MeasurePreserving X.symm volume volume := MeasurePreserving.symm X.toMeasurableEquiv hX
  have hwi : Integrable (fun y => w (X.symm y)) := hiX.integrable_comp_of_integrable hw
  have hA : (∫ y, ‖w (X.symm y)‖) = ∫ b, ‖w b‖ :=
    hiX.integral_comp X.symm.measurableEmbedding (fun b : R2 => ‖w b‖)
  rw [planarMaterialBiotSavart_eq_spatial w X hX]
  have hb := norm_planarBiotSavart_le_mass_amplitude hwi (fun y => hB (X.symm y)) x
  rw [hA] at hb
  refine hb.trans ?_
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  have hA0 : 0 ≤ ∫ b, ‖w b‖ := integral_nonneg (fun b => norm_nonneg _)
  nlinarith [sq_nonneg (Real.sqrt (∫ b, ‖w b‖) - Real.sqrt B), Real.sq_sqrt hB0, Real.sq_sqrt hA0]

theorem logFlowModulus_le_epsilon_affine {d ε : ℝ} (hd : 0 ≤ d) (hε : 0 < ε) :
    logFlowModulus d ≤ (1 - Real.log ε) * d + ε := by
  rcases hd.eq_or_lt with rfl | hd
  · simp only [logFlowModulus, zero_mul, mul_zero, sub_zero, zero_add]
    exact hε.le
  have hl := Real.log_le_sub_one_of_pos (div_pos hε hd)
  rw [Real.log_div hε.ne' hd.ne'] at hl
  have hm := mul_le_mul_of_nonneg_left hl hd.le
  have he : d * (ε / d - 1) = ε - d := by field_simp
  rw [he] at hm
  unfold logFlowModulus
  nlinarith

theorem norm_coupled_planarBiotSavart_le_epsilon_affine
    {w : R2 → ℝ} {B D ε : ℝ} (hw : Integrable w) (hB : ∀ b, ‖w b‖ ≤ B)
    (X Y : R2 ≃ₜ R2) (hX : MeasurePreserving X volume volume)
    (hY : MeasurePreserving Y volume volume)
    (hD : 0 ≤ D) (hdist : ∀ b, ‖X b - Y b‖ ≤ D) (a : R2)
    (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ‖planarMaterialLabelVelocity kernelK w X (X a) -
      planarMaterialLabelVelocity kernelK w Y (Y a)‖ ≤
      (20 * (B + ∫ b, ‖w b‖)) * ((1 - Real.log ε) * D + ε) := by
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  have hA0 : 0 ≤ ∫ b, ‖w b‖ := integral_nonneg (fun b => norm_nonneg _)
  have hsum : 0 ≤ B + ∫ b, ‖w b‖ := add_nonneg hB0 hA0
  have hK : 1 ≤ 1 - Real.log ε := by linarith [Real.log_nonpos hε.le hε1]
  rcases hD.eq_or_lt with hDz | hDpos
  · have hxy : (X : R2 → R2) = Y := by
      funext b
      exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm (by simpa only [← hDz] using hdist b) (norm_nonneg _)))
    simp only [hxy, sub_self, norm_zero]
    positivity
  · by_cases hsmall : D ≤ 1 / 8
    · exact (norm_coupled_planarBiotSavart_le_logFlowModulus hw hB X Y hX hY hDpos hsmall hdist a).trans
        (mul_le_mul_of_nonneg_left (logFlowModulus_le_epsilon_affine hD hε) (by positivity))
    · have hlarge : 1 / 8 ≤ D := (lt_of_not_ge hsmall).le
      have hb : ‖planarMaterialLabelVelocity kernelK w X (X a) -
          planarMaterialLabelVelocity kernelK w Y (Y a)‖ ≤ 2 * (B + ∫ b, ‖w b‖) :=
        (norm_sub_le _ _).trans (by linarith [norm_planarMaterialBiotSavart_le_sum hw hB X hX (X a),
          norm_planarMaterialBiotSavart_le_sum hw hB Y hY (Y a)])
      refine hb.trans ?_
      have hprod : D ≤ (1 - Real.log ε) * D := by nlinarith
      have heps : 0 ≤ (1 - Real.log ε) * D + ε - D := by linarith
      nlinarith [mul_le_mul_of_nonneg_left hlarge hsum, mul_nonneg hsum heps]

end Euler2D

end
