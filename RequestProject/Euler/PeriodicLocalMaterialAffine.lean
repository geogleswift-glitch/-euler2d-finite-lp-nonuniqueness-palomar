module

public import RequestProject.Euler.PeriodicLocalMaterialCoupling
public import RequestProject.Euler.CoupledPlanarBiotSavartAffine

/-! The actual periodic local singular material field has a global
epsilon-affine comparison on active source labels. The same genuine
Lipschitz correction can be added on the two particle configurations. -/

@[expose] public section

set_option maxHeartbeats 5000000

noncomputable section

open MeasureTheory Set Filter Topology Metric Real
open scoped NNReal

namespace Euler2D

def periodicLocalCouplingCoefficient (C : ℝ) : ℝ :=
  10 + 16 * Real.pi * C + 8 * C + 16 * ∫ z in torusBox, ‖periodicLocalKernel z‖

theorem periodicLocalCouplingCoefficient_nonneg {C : ℝ} (hC : 0 ≤ C) :
    0 ≤ periodicLocalCouplingCoefficient C := by
  dsimp only [periodicLocalCouplingCoefficient]
  positivity

theorem norm_periodicLocalMaterial_sub_le_logFlowModulus
    {w : R2 → ℝ} {B C D : ℝ} (hw : Integrable w μT) (hB0 : 0 ≤ B)
    (hB : ∀ᵐ b ∂μT, ‖w b‖ ≤ B) (hC : 0 ≤ C)
    (hderiv : ∀ z : R2, z ≠ 0 → ‖fderiv ℝ localPlanarKernel z‖ ≤ C * (‖z‖ ^ 2)⁻¹)
    {X Y : R2 → R2} (hX : TorusAreaPreserving X) (hY : TorusAreaPreserving Y)
    (hD : 0 < D) (hD1 : D ≤ 1 / 8) (x y : R2) (hxy : ‖x - y‖ ≤ D)
    (hdist : ∀ᵐ b ∂μT, w b ≠ 0 → ‖X b - Y b‖ ≤ D) :
    ‖periodicLocalMaterialVelocity w X x - periodicLocalMaterialVelocity w Y y‖ ≤
      (periodicLocalCouplingCoefficient C * (B + ∫ b in torusBox, ‖w b‖)) * logFlowModulus D := by
  have hA0 : 0 ≤ ∫ b in torusBox, ‖w b‖ := integral_nonneg (fun _ => norm_nonneg _)
  have hJ0 : 0 ≤ ∫ z in torusBox, ‖periodicLocalKernel z‖ := integral_nonneg (fun _ => norm_nonneg _)
  have hargs : ∀ᵐ b ∂μT, w b ≠ 0 →
      ‖((x + torusCenter) - X b) - ((y + torusCenter) - Y b)‖ ≤ 2 * D := by
    filter_upwards [hdist] with b hb hwb
    have he : ((x + torusCenter) - X b) - ((y + torusCenter) - Y b) = (x - y) - (X b - Y b) := by abel
    rw [he]
    exact (norm_sub_le _ _).trans (by linarith [hb hwb])
  have hh := norm_periodicLocalMaterial_sub_le_raw hw hB0 hB hC hderiv hX hY
    (show 0 < 2 * D by positivity) (show 2 * D ≤ 1 / 4 by linarith) x y hargs
  have hlog : Real.log (1 / (2 * (2 * D))) ≤ -Real.log D := by
    rw [← Real.log_inv]
    apply Real.log_le_log (by positivity)
    rw [one_div, inv_le_inv₀ (by positivity) hD]
    linarith
  have hl0 : 0 ≤ -Real.log D := neg_nonneg.mpr (Real.log_nonpos hD.le (by linarith))
  have hm1 : D ≤ logFlowModulus D := by unfold logFlowModulus; nlinarith
  have hm2 : D * (-Real.log D) ≤ logFlowModulus D := by unfold logFlowModulus; linarith
  have hm0 : 0 ≤ logFlowModulus D := hD.le.trans hm1
  have hlogterm : (8 * Real.pi * C * B * (2 * D)) * Real.log (1 / (2 * (2 * D))) ≤
      (16 * Real.pi * C * B) * logFlowModulus D := by
    calc
      _ ≤ (16 * Real.pi * C * B) * (D * (-Real.log D)) := by
        have he := mul_le_mul_of_nonneg_left hlog (show 0 ≤ 8 * Real.pi * C * B * (2 * D) by positivity)
        nlinarith
      _ ≤ _ := mul_le_mul_of_nonneg_left hm2 (by positivity)
  have hnear := mul_le_mul_of_nonneg_left hm1 (show 0 ≤ 10 * B by positivity)
  have hfar := mul_le_mul_of_nonneg_left hm1 (show 0 ≤ 8 * C * ∫ b in torusBox, ‖w b‖ by positivity)
  have hcoef : 10 * B + 16 * Real.pi * C * B + 8 * C * (∫ b in torusBox, ‖w b‖) ≤
      periodicLocalCouplingCoefficient C * (B + ∫ b in torusBox, ‖w b‖) := by
    dsimp only [periodicLocalCouplingCoefficient]
    nlinarith [mul_nonneg (show 0 ≤ 10 + 16 * Real.pi * C by positivity) hA0,
      mul_nonneg (show 0 ≤ 8 * C by positivity) hB0,
      mul_nonneg (show 0 ≤ 16 * ∫ z in torusBox, ‖periodicLocalKernel z‖ by positivity) (add_nonneg hB0 hA0)]
  have hlast := mul_le_mul_of_nonneg_right hcoef hm0
  nlinarith

theorem norm_periodicLocalMaterial_sub_le_epsilon_affine
    {w : R2 → ℝ} {B C D ε : ℝ} (hw : Integrable w μT) (hB0 : 0 ≤ B)
    (hB : ∀ᵐ b ∂μT, ‖w b‖ ≤ B) (hC : 0 ≤ C)
    (hderiv : ∀ z : R2, z ≠ 0 → ‖fderiv ℝ localPlanarKernel z‖ ≤ C * (‖z‖ ^ 2)⁻¹)
    {X Y : R2 → R2} (hX : TorusAreaPreserving X) (hY : TorusAreaPreserving Y)
    (hD : 0 ≤ D) (x y : R2) (hxy : ‖x - y‖ ≤ D)
    (hdist : ∀ᵐ b ∂μT, w b ≠ 0 → ‖X b - Y b‖ ≤ D) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ‖periodicLocalMaterialVelocity w X x - periodicLocalMaterialVelocity w Y y‖ ≤
      (periodicLocalCouplingCoefficient C * (B + ∫ b in torusBox, ‖w b‖)) * ((1 - Real.log ε) * D + ε) := by
  have hA0 : 0 ≤ ∫ b in torusBox, ‖w b‖ := integral_nonneg (fun _ => norm_nonneg _)
  have hJ0 : 0 ≤ ∫ z in torusBox, ‖periodicLocalKernel z‖ := integral_nonneg (fun _ => norm_nonneg _)
  have hCoef0 : 0 ≤ periodicLocalCouplingCoefficient C := periodicLocalCouplingCoefficient_nonneg hC
  have hK : 1 ≤ 1 - Real.log ε := by linarith [Real.log_nonpos hε.le hε1]
  rcases hD.eq_or_lt with hD0 | hDpos
  · have hxy0 : x = y := sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm (by simpa only [← hD0] using hxy) (norm_nonneg _)))
    have hvel : periodicLocalMaterialVelocity w X x = periodicLocalMaterialVelocity w Y y := by
      unfold periodicLocalMaterialVelocity
      apply integral_congr_ae
      filter_upwards [hdist] with b hb
      by_cases hw0 : w b = 0
      · simp only [hw0, zero_smul]
      · have hmaps : X b = Y b := sub_eq_zero.mp (norm_eq_zero.mp
          (le_antisymm (by simpa only [← hD0] using hb hw0) (norm_nonneg _)))
        rw [hxy0, hmaps]
    rw [hvel, sub_self, norm_zero]
    positivity
  · by_cases hsmall : D ≤ 1 / 8
    · exact (norm_periodicLocalMaterial_sub_le_logFlowModulus hw hB0 hB hC hderiv hX hY
        hDpos hsmall x y hxy hdist).trans
        (mul_le_mul_of_nonneg_left (logFlowModulus_le_epsilon_affine hD hε) (by positivity))
    · have hlarge : 1 / 8 ≤ D := (lt_of_not_ge hsmall).le
      have hb : ‖periodicLocalMaterialVelocity w X x - periodicLocalMaterialVelocity w Y y‖ ≤
          2 * B * (∫ z in torusBox, ‖periodicLocalKernel z‖) :=
        (norm_sub_le _ _).trans (by linarith [norm_periodicLocalMaterialVelocity_le hB hX x,
          norm_periodicLocalMaterialVelocity_le hB hY y])
      have hc : 16 * B * (∫ z in torusBox, ‖periodicLocalKernel z‖) ≤
          periodicLocalCouplingCoefficient C * (B + ∫ b in torusBox, ‖w b‖) := by
        dsimp only [periodicLocalCouplingCoefficient]
        nlinarith [mul_nonneg (show 0 ≤ 10 + 16 * Real.pi * C + 8 * C by positivity) (add_nonneg hB0 hA0),
          mul_nonneg hJ0 hA0]
      have hdlarge := mul_le_mul_of_nonneg_left hlarge (show 0 ≤ 16 * B * ∫ z in torusBox, ‖periodicLocalKernel z‖ by positivity)
      have hcD := mul_le_mul_of_nonneg_right hc hD
      have heps : D ≤ (1 - Real.log ε) * D + ε := by nlinarith
      have hbig := mul_le_mul_of_nonneg_left heps (show 0 ≤ periodicLocalCouplingCoefficient C * (B + ∫ b in torusBox, ‖w b‖) by positivity)
      nlinarith

theorem norm_periodicLocalMaterial_add_common_field_sub_le_affine
    {w : R2 → ℝ} {B C D ε : ℝ} (hw : Integrable w μT) (hB0 : 0 ≤ B)
    (hB : ∀ᵐ b ∂μT, ‖w b‖ ≤ B) (hC : 0 ≤ C)
    (hderiv : ∀ z : R2, z ≠ 0 → ‖fderiv ℝ localPlanarKernel z‖ ≤ C * (‖z‖ ^ 2)⁻¹)
    {X Y : R2 → R2} (hX : TorusAreaPreserving X) (hY : TorusAreaPreserving Y)
    (hD : 0 ≤ D) (x y : R2) (hxy : ‖x - y‖ ≤ D)
    (hdist : ∀ᵐ b ∂μT, w b ≠ 0 → ‖X b - Y b‖ ≤ D) (hε : 0 < ε) (hε1 : ε ≤ 1)
    {E : R2 → R2} {L : ℝ≥0} (hE : LipschitzWith L E) :
    ‖(periodicLocalMaterialVelocity w X x + E x) - (periodicLocalMaterialVelocity w Y y + E y)‖ ≤
      (periodicLocalCouplingCoefficient C * (B + ∫ b in torusBox, ‖w b‖) + (L : ℝ)) *
        ((1 - Real.log ε) * D + ε) := by
  have hmain := norm_periodicLocalMaterial_sub_le_epsilon_affine hw hB0 hB hC hderiv hX hY hD x y hxy hdist hε hε1
  have he := hE.dist_le_mul x y
  rw [dist_eq_norm, dist_eq_norm] at he
  have hEl := he.trans (mul_le_mul_of_nonneg_left hxy L.coe_nonneg)
  have hK : 1 ≤ 1 - Real.log ε := by linarith [Real.log_nonpos hε.le hε1]
  have hεD : D ≤ (1 - Real.log ε) * D + ε := by nlinarith
  have hEnd := mul_le_mul_of_nonneg_left hεD L.coe_nonneg
  rw [add_sub_add_comm]
  have hh := (norm_add_le _ _).trans (add_le_add hmain hEl)
  nlinarith

end Euler2D

end
