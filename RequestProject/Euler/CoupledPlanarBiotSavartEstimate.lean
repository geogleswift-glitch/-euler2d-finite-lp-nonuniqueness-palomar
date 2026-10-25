module

public import RequestProject.Euler.CoupledKernelSplit
public import RequestProject.Euler.PlanarMaterialLabelComparison

/-! An actual nonlinear coupling estimate for singular planar
Biot--Savart velocities. The two near singularities are integrated
using the two genuine volume-preserving maps separately. -/

@[expose] public section

set_option maxHeartbeats 5000000

noncomputable section

open MeasureTheory Complex Set Filter Topology

namespace Euler2D

theorem integrable_planarMaterialBiotSavart_integrand
    {w : R2 → ℝ} {B : ℝ} (hw : Integrable w) (hB : ∀ b, ‖w b‖ ≤ B)
    (X : R2 ≃ₜ R2) (hX : MeasurePreserving X volume volume) (x : R2) :
    Integrable (fun b => w b • kernelK (x - X b)) := by
  have hiX : MeasurePreserving X.symm volume volume := MeasurePreserving.symm X.toMeasurableEquiv hX
  have hwi := hiX.integrable_comp_of_integrable hw
  have hi := integrable_planarBiotSavart_integrand hwi (fun y => hB (X.symm y)) x
  have hh := hX.integrable_comp_of_integrable hi
  change Integrable (fun b => w (X.symm (X b)) • kernelK (x - X b)) at hh
  simpa only [Homeomorph.symm_apply_apply] using hh

theorem integrable_complex_profile_material
    (q : ℂ → ℝ) (hq : Integrable q) (X : R2 ≃ₜ R2)
    (hX : MeasurePreserving X volume volume) (x : R2) :
    Integrable (fun b => q (complexPhysicalPlane.symm (x - X b))) :=
  hX.integrable_comp_of_integrable
    ((complexPhysicalPlane.symm.measurePreserving.integrable_comp_of_integrable hq).comp_sub_left x)

theorem integral_complex_profile_material
    (q : ℂ → ℝ) (X : R2 ≃ₜ R2) (hX : MeasurePreserving X volume volume) (x : R2) :
    (∫ b, q (complexPhysicalPlane.symm (x - X b))) = ∫ z, q z := by
  calc
    _ = ∫ y, q (complexPhysicalPlane.symm (x - y)) :=
      hX.integral_comp X.measurableEmbedding _
    _ = ∫ y : R2, q (complexPhysicalPlane.symm y) :=
      integral_sub_left_eq_self (μ := (volume : Measure R2)) (fun y : R2 => q (complexPhysicalPlane.symm y)) x
    _ = _ := complexPhysicalPlane.symm.measurePreserving.integral_comp
      complexPhysicalPlane.symm.toHomeomorph.measurableEmbedding q

theorem norm_coupled_planarBiotSavart_le_raw
    {w : R2 → ℝ} {B h : ℝ} (hw : Integrable w) (hB : ∀ b, ‖w b‖ ≤ B)
    (X Y : R2 ≃ₜ R2) (hX : MeasurePreserving X volume volume)
    (hY : MeasurePreserving Y volume volume)
    (hh : 0 < h) (hh1 : 2 * h ≤ 1) (x y : R2)
    (hargs : ∀ b, ‖(x - X b) - (y - Y b)‖ ≤ h) :
    ‖planarMaterialLabelVelocity kernelK w X x - planarMaterialLabelVelocity kernelK w Y y‖ ≤
      B * (5 * h + 2 * h * Real.log (1 / (2 * h))) + h / Real.pi * ∫ b, ‖w b‖ := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  let A (b : R2) := truncInvNorm (2 * h) (complexPhysicalPlane.symm (x - X b))
  let C (b : R2) := truncInvNorm (3 * h) (complexPhysicalPlane.symm (y - Y b))
  let R (b : R2) := annKernel h (complexPhysicalPlane.symm (x - X b))
  have hAi : Integrable A := integrable_complex_profile_material _ (integrable_truncInvNorm _) X hX x
  have hCi : Integrable C := integrable_complex_profile_material _ (integrable_truncInvNorm _) Y hY y
  have hRi : Integrable R := integrable_complex_profile_material _ (integrable_annKernel hh) X hX x
  let G (b : R2) := B / (2 * Real.pi) * A b + B / (2 * Real.pi) * C b +
    B * h / Real.pi * R b + h / Real.pi * ‖w b‖
  have i1 := hAi.const_mul (B / (2 * Real.pi))
  have i2 := hCi.const_mul (B / (2 * Real.pi))
  have i3 := hRi.const_mul (B * h / Real.pi)
  have i4 := hw.norm.const_mul (h / Real.pi)
  have i12 : Integrable (fun b => B / (2 * Real.pi) * A b + B / (2 * Real.pi) * C b) := i1.add i2
  have i123 : Integrable (fun b => B / (2 * Real.pi) * A b + B / (2 * Real.pi) * C b +
      B * h / Real.pi * R b) := i12.add i3
  have hGi : Integrable G := ((i1.add i2).add i3).add i4
  have hbound (b : R2) : ‖w b • (kernelK (x - X b) - kernelK (y - Y b))‖ ≤ G b := by
    rw [norm_smul]
    have hk := planar_kernel_diff_split_bounded hh (hargs b)
    have hAn : 0 ≤ A b := truncInvNorm_nonneg _ _
    have hCn : 0 ≤ C b := truncInvNorm_nonneg _ _
    have hRn : 0 ≤ R b := annKernel_nonneg _ _
    have hP : 0 ≤ (A b + C b) / (2 * Real.pi) + h / Real.pi * R b := by positivity
    calc
      _ ≤ ‖w b‖ * ((A b + C b) / (2 * Real.pi) + h / Real.pi * R b + h / Real.pi) :=
        mul_le_mul_of_nonneg_left hk (norm_nonneg _)
      _ ≤ B * ((A b + C b) / (2 * Real.pi) + h / Real.pi * R b) + h / Real.pi * ‖w b‖ := by
        nlinarith [mul_le_mul_of_nonneg_right (hB b) hP]
      _ = G b := by dsimp only [G]; ring
  have e1 : (∫ b, A b) = 2 * Real.pi * (2 * h) := by
    rw [show A = fun b => truncInvNorm (2 * h) (complexPhysicalPlane.symm (x - X b)) from rfl,
      integral_complex_profile_material _ X hX x, integral_truncInvNorm (by positivity)]
  have e2 : (∫ b, C b) = 2 * Real.pi * (3 * h) := by
    rw [show C = fun b => truncInvNorm (3 * h) (complexPhysicalPlane.symm (y - Y b)) from rfl,
      integral_complex_profile_material _ Y hY y, integral_truncInvNorm (by positivity)]
  have e3 : (∫ b, R b) = 2 * Real.pi * Real.log (1 / (2 * h)) := by
    rw [show R = fun b => annKernel h (complexPhysicalPlane.symm (x - X b)) from rfl,
      integral_complex_profile_material _ X hX x, integral_annKernel hh hh1]
  have hIG : (∫ b, G b) = B * (5 * h + 2 * h * Real.log (1 / (2 * h))) +
      h / Real.pi * ∫ b, ‖w b‖ := by
    dsimp only [G]
    rw [integral_add i123 i4, integral_add i12 i3,
      integral_add i1 i2, integral_const_mul, integral_const_mul, integral_const_mul,
      integral_const_mul, e1, e2, e3]
    field_simp
    ring
  unfold planarMaterialLabelVelocity
  rw [← integral_sub (integrable_planarMaterialBiotSavart_integrand hw hB X hX x)
    (integrable_planarMaterialBiotSavart_integrand hw hB Y hY y)]
  have he : (fun b => w b • kernelK (x - X b) - w b • kernelK (y - Y b)) =
      (fun b => w b • (kernelK (x - X b) - kernelK (y - Y b))) :=
    funext (fun b => (smul_sub _ _ _).symm)
  rw [he]
  exact (norm_integral_le_of_norm_le hGi (ae_of_all _ hbound)).trans_eq hIG

theorem norm_coupled_planarBiotSavart_le_logFlowModulus
    {w : R2 → ℝ} {B D : ℝ} (hw : Integrable w) (hB : ∀ b, ‖w b‖ ≤ B)
    (X Y : R2 ≃ₜ R2) (hX : MeasurePreserving X volume volume)
    (hY : MeasurePreserving Y volume volume)
    (hD : 0 < D) (hD1 : D ≤ 1 / 8) (hdist : ∀ b, ‖X b - Y b‖ ≤ D) (a : R2) :
    ‖planarMaterialLabelVelocity kernelK w X (X a) -
      planarMaterialLabelVelocity kernelK w Y (Y a)‖ ≤
      (20 * (B + ∫ b, ‖w b‖)) * logFlowModulus D := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  have hA0 : 0 ≤ ∫ b, ‖w b‖ := integral_nonneg (fun b => norm_nonneg _)
  have hh := norm_coupled_planarBiotSavart_le_raw hw hB X Y hX hY
    (show 0 < 2 * D by positivity) (show 2 * (2 * D) ≤ 1 by linarith) (X a) (Y a)
    (fun b => by
      have he : (X a - X b) - (Y a - Y b) = (X a - Y a) - (X b - Y b) := by abel
      rw [he]
      exact (norm_sub_le _ _).trans (by linarith [hdist a, hdist b]))
  have hlog : Real.log (1 / (2 * (2 * D))) ≤ -Real.log D := by
    rw [← Real.log_inv]
    apply Real.log_le_log (by positivity)
    rw [one_div, inv_le_inv₀ (by positivity) hD]
    linarith
  have hlog0 : 0 ≤ -Real.log D := neg_nonneg.mpr (Real.log_nonpos hD.le (by linarith))
  have htail : (2 * D) / Real.pi * (∫ b, ‖w b‖) ≤ 2 * D * (∫ b, ‖w b‖) := by
    apply mul_le_mul_of_nonneg_right _ hA0
    exact div_le_self (by positivity) (by linarith [Real.pi_gt_three])
  refine hh.trans ?_
  unfold logFlowModulus
  have hlogmul := mul_le_mul_of_nonneg_left hlog (show 0 ≤ B * (2 * (2 * D)) by positivity)
  nlinarith [mul_nonneg (mul_nonneg hB0 hD.le) hlog0,
    mul_nonneg (mul_nonneg hA0 hD.le) hlog0]

end Euler2D

end
