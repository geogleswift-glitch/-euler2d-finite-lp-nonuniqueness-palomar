module
public import RequestProject.Euler.HybridTorusPlanarMaterialCoupling

/-! Mixed true torus/plane material comparison with a common smooth field. -/
@[expose] public section
set_option maxHeartbeats 3000000
noncomputable section
open MeasureTheory Set Filter Topology Metric Real
open scoped NNReal
namespace Euler2D

def hybridLocalCouplingCoefficient : ℝ := 20 + 8 * ∫ z in torusBox, ‖periodicLocalKernel z‖

theorem hybridLocalCouplingCoefficient_nonneg : 0 ≤ hybridLocalCouplingCoefficient := by
  dsimp only [hybridLocalCouplingCoefficient]
  positivity

theorem norm_hybrid_material_sub_le_logFlowModulus
    {w : R2 → ℝ} {B D : ℝ} (hw : Integrable w) (hB : ∀ b, ‖w b‖ ≤ B)
    (hwzero : ∀ b, b ∉ torusBox → w b = 0)
    {X : R2 → R2} (hX : TorusAreaPreserving X) (Y : R2 ≃ₜ R2)
    (hY : MeasurePreserving Y volume volume)
    (hD : 0 < D) (hD1 : D ≤ 1 / 8) (x y : R2) (hxy : ‖x - y‖ ≤ D)
    (hsmall : ∀ᵐ b ∂μT, w b ≠ 0 → ‖x - X b‖ ≤ 1 / 2)
    (hdist : ∀ᵐ b ∂μT, w b ≠ 0 → ‖X b - Y b‖ ≤ D) :
    ‖periodicLocalMaterialVelocity w X x - planarMaterialLabelVelocity kernelK w Y y‖ ≤
      (20 * (B + ∫ b in torusBox, ‖w b‖)) * logFlowModulus D := by
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  have hA0 : 0 ≤ ∫ b in torusBox, ‖w b‖ := integral_nonneg (fun _ => norm_nonneg _)
  have hargs : ∀ᵐ b ∂μT, w b ≠ 0 → ‖(x - X b) - (y - Y b)‖ ≤ 2 * D := by
    filter_upwards [hdist] with b hb hwb
    have he : (x - X b) - (y - Y b) = (x - y) - (X b - Y b) := by abel
    rw [he]
    exact (norm_sub_le _ _).trans (by linarith [hb hwb])
  have hh := norm_hybrid_periodicLocal_planarMaterial_sub_le_raw hw hB hwzero hX Y hY
    (show 0 < 2 * D by positivity) (show 2 * D ≤ 1 / 4 by linarith) x y hsmall hargs
  have hlog : Real.log (1 / (2 * (2 * D))) ≤ -Real.log D := by
    rw [← Real.log_inv]
    apply Real.log_le_log (by positivity)
    rw [one_div, inv_le_inv₀ (by positivity) hD]
    linarith
  have hlog0 : 0 ≤ -Real.log D := neg_nonneg.mpr (Real.log_nonpos hD.le (by linarith))
  have htail : (2 * D) / Real.pi * (∫ b in torusBox, ‖w b‖) ≤ 2 * D * (∫ b in torusBox, ‖w b‖) := by
    apply mul_le_mul_of_nonneg_right _ hA0
    exact div_le_self (by positivity) (by linarith [Real.pi_gt_three])
  refine hh.trans ?_
  unfold logFlowModulus
  have hlogmul := mul_le_mul_of_nonneg_left hlog (show 0 ≤ B * (2 * (2 * D)) by positivity)
  nlinarith [mul_nonneg (mul_nonneg hB0 hD.le) hlog0,
    mul_nonneg (mul_nonneg hA0 hD.le) hlog0]

theorem norm_hybrid_material_sub_le_epsilon_affine
    {w : R2 → ℝ} {B D ε : ℝ} (hw : Integrable w) (hB : ∀ b, ‖w b‖ ≤ B)
    (hwzero : ∀ b, b ∉ torusBox → w b = 0)
    {X : R2 → R2} (hX : TorusAreaPreserving X) (Y : R2 ≃ₜ R2)
    (hY : MeasurePreserving Y volume volume)
    (hD : 0 ≤ D) (x y : R2) (hxy : ‖x - y‖ ≤ D)
    (hsmall : ∀ᵐ b ∂μT, w b ≠ 0 → ‖x - X b‖ ≤ 1 / 2)
    (hdist : ∀ᵐ b ∂μT, w b ≠ 0 → ‖X b - Y b‖ ≤ D) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ‖periodicLocalMaterialVelocity w X x - planarMaterialLabelVelocity kernelK w Y y‖ ≤
      (hybridLocalCouplingCoefficient * (B + ∫ b in torusBox, ‖w b‖)) * ((1 - Real.log ε) * D + ε) := by
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  have hA0 : 0 ≤ ∫ b in torusBox, ‖w b‖ := integral_nonneg (fun _ => norm_nonneg _)
  have hJ0 : 0 ≤ ∫ z in torusBox, ‖periodicLocalKernel z‖ := integral_nonneg (fun _ => norm_nonneg _)
  have hK : 1 ≤ 1 - Real.log ε := by linarith [Real.log_nonpos hε.le hε1]
  have hcoef : 20 ≤ hybridLocalCouplingCoefficient := by dsimp only [hybridLocalCouplingCoefficient]; linarith
  rcases hD.eq_or_lt with hD0 | hDpos
  · have hxy0 : x = y := sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm (by simpa only [← hD0] using hxy) (norm_nonneg _)))
    have he : periodicLocalMaterialVelocity w X x = planarMaterialLabelVelocity kernelK w Y y := by
      rw [planarMaterialLabelVelocity_eq_box_of_support hwzero Y y]
      unfold periodicLocalMaterialVelocity
      apply integral_congr_ae
      filter_upwards [hdist, hsmall] with b hb hs
      by_cases hw0 : w b = 0
      · simp only [hw0, zero_smul]
      · have hmaps : X b = Y b := sub_eq_zero.mp (norm_eq_zero.mp
          (le_antisymm (by simpa only [← hD0] using hb hw0) (norm_nonneg _)))
        have hn : ‖((x + torusCenter) - X b) - torusCenter‖ ≤ 1 / 2 := by
          convert hs hw0 using 1 <;> congr 1 <;> abel
        rw [periodicLocalKernel_eq_kernelK_near hn]
        congr 2
        rw [← hxy0, ← hmaps]
        abel
    rw [he, sub_self, norm_zero]
    exact mul_nonneg (mul_nonneg hybridLocalCouplingCoefficient_nonneg (add_nonneg hB0 hA0)) (by nlinarith)
  · by_cases hsmallD : D ≤ 1 / 8
    · have hm := norm_hybrid_material_sub_le_logFlowModulus hw hB hwzero hX Y hY hDpos hsmallD x y hxy hsmall hdist
      have heps := logFlowModulus_le_epsilon_affine hD hε
      have heps0 : 0 ≤ (1 - Real.log ε) * D + ε := by positivity
      exact (hm.trans (mul_le_mul_of_nonneg_left heps (by positivity))).trans
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcoef (add_nonneg hB0 hA0)) heps0)
    · have hlarge : 1 / 8 ≤ D := (lt_of_not_ge hsmallD).le
      have hAeq : (∫ b, ‖w b‖) = ∫ b in torusBox, ‖w b‖ :=
        (setIntegral_eq_integral_of_forall_compl_eq_zero (fun b hb => by rw [hwzero b hb, norm_zero])).symm
      have hbY := norm_planarMaterialBiotSavart_le_sum hw hB Y hY y
      rw [hAeq] at hbY
      have hb : ‖periodicLocalMaterialVelocity w X x - planarMaterialLabelVelocity kernelK w Y y‖ ≤
          ((∫ z in torusBox, ‖periodicLocalKernel z‖) + 1) * (B + ∫ b in torusBox, ‖w b‖) := by
        have hh := (norm_sub_le _ _).trans (add_le_add
          (norm_periodicLocalMaterialVelocity_le (ae_of_all _ hB) hX x) hbY)
        nlinarith [mul_nonneg hJ0 hA0]
      have hc : 8 * ((∫ z in torusBox, ‖periodicLocalKernel z‖) + 1) ≤ hybridLocalCouplingCoefficient := by
        dsimp only [hybridLocalCouplingCoefficient]
        linarith
      have heps : D ≤ (1 - Real.log ε) * D + ε := by nlinarith
      have hV := add_nonneg hB0 hA0
      have hJ1 : 0 ≤ (∫ z in torusBox, ‖periodicLocalKernel z‖) + 1 := by positivity
      have h1 := mul_le_mul_of_nonneg_left hlarge (mul_nonneg hJ1 hV)
      have h2 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc hV) hD
      have h3 := mul_le_mul_of_nonneg_left heps (mul_nonneg hybridLocalCouplingCoefficient_nonneg hV)
      nlinarith

theorem norm_hybrid_material_add_common_field_sub_le_affine
    {w : R2 → ℝ} {B D ε : ℝ} (hw : Integrable w) (hB : ∀ b, ‖w b‖ ≤ B)
    (hwzero : ∀ b, b ∉ torusBox → w b = 0)
    {X : R2 → R2} (hX : TorusAreaPreserving X) (Y : R2 ≃ₜ R2)
    (hY : MeasurePreserving Y volume volume)
    (hD : 0 ≤ D) (x y : R2) (hxy : ‖x - y‖ ≤ D)
    (hsmall : ∀ᵐ b ∂μT, w b ≠ 0 → ‖x - X b‖ ≤ 1 / 2)
    (hdist : ∀ᵐ b ∂μT, w b ≠ 0 → ‖X b - Y b‖ ≤ D) (hε : 0 < ε) (hε1 : ε ≤ 1)
    {E : R2 → R2} {L : ℝ≥0} (hE : LipschitzWith L E) :
    ‖(periodicLocalMaterialVelocity w X x + E x) - (planarMaterialLabelVelocity kernelK w Y y + E y)‖ ≤
      (hybridLocalCouplingCoefficient * (B + ∫ b in torusBox, ‖w b‖) + (L : ℝ)) *
        ((1 - Real.log ε) * D + ε) := by
  have hmain := norm_hybrid_material_sub_le_epsilon_affine hw hB hwzero hX Y hY hD x y hxy hsmall hdist hε hε1
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
