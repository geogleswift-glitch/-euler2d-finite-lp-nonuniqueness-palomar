module

public import RequestProject.Euler.CoupledPlanarBiotSavartAffine
public import RequestProject.Euler.UniformLogLabelParticleStability

/-! Genuine singular material stability, allowing distinct initial
sources and restricting particle comparisons to their active labels. -/

@[expose] public section

set_option maxHeartbeats 1500000
set_option maxRecDepth 6500

noncomputable section

open MeasureTheory Complex Set Filter Topology

namespace Euler2D

theorem norm_active_planarMaterial_sub_le_raw
    {w : R2 → ℝ} {B h : ℝ} (hw : Integrable w) (hB : ∀ b, ‖w b‖ ≤ B)
    (X Y : R2 ≃ₜ R2) (hX : MeasurePreserving X volume volume)
    (hY : MeasurePreserving Y volume volume)
    (hh : 0 < h) (hh1 : 2 * h ≤ 1) (x y : R2)
    (hargs : ∀ b, w b ≠ 0 → ‖(x - X b) - (y - Y b)‖ ≤ h) :
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
    have hAn : 0 ≤ A b := truncInvNorm_nonneg _ _
    have hCn : 0 ≤ C b := truncInvNorm_nonneg _ _
    have hRn : 0 ≤ R b := annKernel_nonneg _ _
    by_cases hw0 : w b = 0
    · simp only [hw0, zero_smul, norm_zero]
      dsimp only [G]
      positivity
    · rw [norm_smul]
      have hk := planar_kernel_diff_split_bounded hh (hargs b hw0)
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

theorem norm_active_planarMaterial_sub_le_epsilon_affine
    {w : R2 → ℝ} {B D ε : ℝ} (hw : Integrable w) (hB : ∀ b, ‖w b‖ ≤ B)
    (X Y : R2 ≃ₜ R2) (hX : MeasurePreserving X volume volume)
    (hY : MeasurePreserving Y volume volume)
    (hD : 0 ≤ D) (x y : R2) (hxy : ‖x - y‖ ≤ D)
    (hdist : ∀ b, w b ≠ 0 → ‖X b - Y b‖ ≤ D) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ‖planarMaterialLabelVelocity kernelK w X x - planarMaterialLabelVelocity kernelK w Y y‖ ≤
      (20 * (B + ∫ b, ‖w b‖)) * ((1 - Real.log ε) * D + ε) := by
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  have hA0 : 0 ≤ ∫ b, ‖w b‖ := integral_nonneg (fun _ => norm_nonneg _)
  have hV : 0 ≤ B + ∫ b, ‖w b‖ := add_nonneg hB0 hA0
  have hlogε : 1 ≤ 1 - Real.log ε := by linarith [Real.log_nonpos hε.le hε1]
  have heps0 : 0 ≤ (1 - Real.log ε) * D + ε := by positivity
  rcases hD.eq_or_lt with hD0 | hDpos
  · have hxy0 : x = y := sub_eq_zero.mp (norm_eq_zero.mp
      (le_antisymm (by simpa only [← hD0] using hxy) (norm_nonneg _)))
    have he : planarMaterialLabelVelocity kernelK w X x = planarMaterialLabelVelocity kernelK w Y y := by
      unfold planarMaterialLabelVelocity
      apply integral_congr_ae
      apply ae_of_all
      intro b
      change w b • kernelK (x - X b) = w b • kernelK (y - Y b)
      by_cases hw0 : w b = 0
      · simp only [hw0, zero_smul]
      · have hb0 : X b = Y b := sub_eq_zero.mp (norm_eq_zero.mp
          (le_antisymm (by simpa only [← hD0] using hdist b hw0) (norm_nonneg _)))
        rw [hxy0, hb0]
    rw [he, sub_self, norm_zero]
    positivity
  · by_cases hsmall : D ≤ 1 / 8
    · have hh := norm_active_planarMaterial_sub_le_raw hw hB X Y hX hY
        (show 0 < 2 * D by positivity) (show 2 * (2 * D) ≤ 1 by linarith) x y
        (by
          intro b hb
          have he : (x - X b) - (y - Y b) = (x - y) - (X b - Y b) := by abel
          rw [he]
          exact (norm_sub_le _ _).trans (by linarith [hdist b hb]))
      have hlog : Real.log (1 / (2 * (2 * D))) ≤ -Real.log D := by
        rw [← Real.log_inv]
        apply Real.log_le_log (by positivity)
        rw [one_div, inv_le_inv₀ (by positivity) hDpos]
        linarith
      have hlog0 : 0 ≤ -Real.log D := neg_nonneg.mpr (Real.log_nonpos hDpos.le (by linarith))
      have htail : (2 * D) / Real.pi * (∫ b, ‖w b‖) ≤ 2 * D * (∫ b, ‖w b‖) :=
        mul_le_mul_of_nonneg_right
          (div_le_self (by positivity) (by linarith [Real.pi_gt_three])) hA0
      have hmain : ‖planarMaterialLabelVelocity kernelK w X x - planarMaterialLabelVelocity kernelK w Y y‖ ≤
          (20 * (B + ∫ b, ‖w b‖)) * logFlowModulus D := by
        refine hh.trans ?_
        unfold logFlowModulus
        have hlogmul := mul_le_mul_of_nonneg_left hlog (show 0 ≤ B * (2 * (2 * D)) by positivity)
        nlinarith [mul_nonneg (mul_nonneg hB0 hDpos.le) hlog0,
          mul_nonneg (mul_nonneg hA0 hDpos.le) hlog0]
      exact hmain.trans (mul_le_mul_of_nonneg_left (logFlowModulus_le_epsilon_affine hDpos.le hε)
        (by positivity))
    · have hlarge : 1 / 8 ≤ D := (lt_of_not_ge hsmall).le
      have hb : ‖planarMaterialLabelVelocity kernelK w X x - planarMaterialLabelVelocity kernelK w Y y‖ ≤
          2 * (B + ∫ b, ‖w b‖) :=
        (norm_sub_le _ _).trans (by linarith [norm_planarMaterialBiotSavart_le_sum hw hB X hX x,
          norm_planarMaterialBiotSavart_le_sum hw hB Y hY y])
      have heps : D ≤ (1 - Real.log ε) * D + ε := by nlinarith
      have hlargeV := mul_le_mul_of_nonneg_left hlarge hV
      have hepsV := mul_nonneg hV (sub_nonneg.mpr heps)
      exact hb.trans (by nlinarith only [hlargeV, hepsV, hV])

theorem norm_planarMaterial_sub_source_le_L1
    {w f : R2 → ℝ} {B : ℝ} (hw : Integrable w) (hf : Integrable f)
    (hB : ∀ b, ‖w b‖ ≤ B) (hfB : ∀ b, ‖f b‖ ≤ B)
    (Y : R2 ≃ₜ R2) (hY : MeasurePreserving Y volume volume) (x : R2) :
    ‖planarMaterialLabelVelocity kernelK w Y x - planarMaterialLabelVelocity kernelK f Y x‖ ≤
      2 * Real.sqrt (∫ b, ‖w b - f b‖) * Real.sqrt (2 * B) := by
  have hiY : MeasurePreserving Y.symm volume volume := MeasurePreserving.symm Y.toMeasurableEquiv hY
  rw [planarMaterialBiotSavart_eq_spatial w Y hY, planarMaterialBiotSavart_eq_spatial f Y hY]
  have he : (∫ b, ‖w (Y.symm b) - f (Y.symm b)‖) = ∫ b, ‖w b - f b‖ :=
    hiY.integral_comp Y.symm.measurableEmbedding (fun b => ‖w b - f b‖)
  simpa only [Function.comp_def, he] using norm_planarBiotSavart_sub_le_L1
    (hiY.integrable_comp_of_integrable hw) (hiY.integrable_comp_of_integrable hf)
    (fun b => hB (Y.symm b)) (fun b => hfB (Y.symm b)) x

theorem planar_material_particle_stability_active
    {T B M H ε : ℝ} (hT : 0 ≤ T) (hB : 0 ≤ B) (hM : 0 ≤ M) (hH : 0 ≤ H) (hε : 0 < ε) :
    ∃ δ > 0, ∀ {w f : R2 → ℝ} (hw : Integrable w) (hf : Integrable f),
      (∀ b, ‖w b‖ ≤ B) → (∀ b, ‖f b‖ ≤ B) → (∫ b, ‖w b‖) ≤ M →
      2 * Real.sqrt (∫ b, ‖w b - f b‖) * Real.sqrt (2 * B) ≤ δ / 2 →
      ∀ {A : Set R2}, (∀ b, w b ≠ 0 → b ∈ A) →
      ∀ (X Y vx vy : ℝ → R2 → R2)
        (XH YH : Icc (0 : ℝ) T → R2 ≃ₜ R2),
      (∀ t, (XH t : R2 → R2) = X t) → (∀ t, (YH t : R2 → R2) = Y t) →
      (∀ t, MeasurePreserving (XH t) volume volume) →
      (∀ t, MeasurePreserving (YH t) volume volume) →
      (∀ a ∈ A, Continuous (fun t => vx t a)) → (∀ a ∈ A, Continuous (fun t => vy t a)) →
      (∀ t ∈ Icc (0 : ℝ) T, ∀ a ∈ A, HasDerivAt (fun s => X s a) (vx t a) t) →
      (∀ t ∈ Icc (0 : ℝ) T, ∀ a ∈ A, HasDerivAt (fun s => Y s a) (vy t a) t) →
      (∀ a ∈ A, ‖X 0 a - Y 0 a‖ ≤ δ) →
      (∀ t ∈ Icc (0 : ℝ) T, ∀ a ∈ A, ‖X t a - Y t a‖ ≤ H) →
      (∀ t ∈ Icc (0 : ℝ) T, ∀ a ∈ A,
        ‖vx t a - planarMaterialLabelVelocity kernelK w (X t) (X t a)‖ +
          ‖vy t a - planarMaterialLabelVelocity kernelK f (Y t) (Y t a)‖ ≤ δ / 2) →
      ∀ t ∈ Icc (0 : ℝ) T, ∀ a ∈ A, ‖X t a - Y t a‖ < ε := by
  classical
  let C := 20 * (B + M)
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  obtain ⟨δ₀, hδ₀, hstable₀⟩ := uniform_log_label_particle_stability
    (ι := R2) (E := R2) hT hH hC hε
  refine ⟨δ₀, hδ₀, ?_⟩
  intro w f hw hf hwB hfB hmass hsource A hactive X Y vx vy XH YH hXH hYH hXmp hYmp
    hvc hwc hXd hYd hinit hbound herror
  -- Inactive labels are given a constant zero path and zero velocity.
  let XX : ℝ → R2 → R2 := fun t a => if a ∈ A then X t a else 0
  let YY : ℝ → R2 → R2 := fun t a => if a ∈ A then Y t a else 0
  let VV : ℝ → R2 → R2 := fun t a => if a ∈ A then vx t a else 0
  let WW : ℝ → R2 → R2 := fun t a => if a ∈ A then vy t a else 0
  have he := hstable₀ XX YY VV WW
    (by intro a; by_cases ha : a ∈ A <;> simp only [VV, ha, if_pos, if_neg]; exact hvc _ ha; exact continuous_const)
    (by intro a; by_cases ha : a ∈ A <;> simp only [WW, ha, if_pos, if_neg]; exact hwc _ ha; exact continuous_const)
    (by intro t ht a; by_cases ha : a ∈ A <;> simp only [XX, VV, ha, if_pos, if_neg]; exact hXd t ht _ ha; exact hasDerivAt_const t 0)
    (by intro t ht a; by_cases ha : a ∈ A <;> simp only [YY, WW, ha, if_pos, if_neg]; exact hYd t ht _ ha; exact hasDerivAt_const t 0)
    (by intro a; by_cases ha : a ∈ A <;> simp only [XX, YY, ha, if_pos, if_neg]; exact hinit _ ha; simpa using hδ₀.le)
    (by intro t ht a; by_cases ha : a ∈ A <;> simp only [XX, YY, ha, if_pos, if_neg]; exact hbound t ht _ ha; simpa using hH)
    (by
      intro t ht D hD hd a η hη hη1
      have haff : 0 ≤ (1 - Real.log η) * D + η := by
        have hl : 0 ≤ 1 - Real.log η := by linarith [Real.log_nonpos hη.le hη1]
        positivity
      by_cases ha : a ∈ A
      · have hdist (b : R2) (hb : w b ≠ 0) : ‖XH ⟨t, ht⟩ b - YH ⟨t, ht⟩ b‖ ≤ D := by
          rw [hXH, hYH]
          have hh := hd b
          simpa only [XX, YY, if_pos (hactive b hb)] using hh
        have hxy : ‖X t a - Y t a‖ ≤ D := by
          simpa only [XX, YY, if_pos ha] using hd a
        have hmain := norm_active_planarMaterial_sub_le_epsilon_affine hw hwB
          (XH ⟨t, ht⟩) (YH ⟨t, ht⟩) (hXmp _) (hYmp _) hD (X t a) (Y t a) hxy hdist hη hη1
        rw [hXH, hYH] at hmain
        have hmodel := norm_planarMaterial_sub_source_le_L1 hw hf hwB hfB
          (YH ⟨t, ht⟩) (hYmp _) (Y t a)
        rw [hYH] at hmodel
        have hcoef : 20 * (B + ∫ b, ‖w b‖) ≤ C := by dsimp only [C]; linarith only [hmass]
        have hmain' := hmain.trans (mul_le_mul_of_nonneg_right hcoef haff)
        have hmid := (norm_sub_le_norm_sub_add_norm_sub
          (planarMaterialLabelVelocity kernelK w (X t) (X t a))
          (planarMaterialLabelVelocity kernelK w (Y t) (Y t a))
          (planarMaterialLabelVelocity kernelK f (Y t) (Y t a))).trans
          (add_le_add hmain' hmodel)
        have htriangle := (norm_sub_le_norm_sub_add_norm_sub (vx t a)
          (planarMaterialLabelVelocity kernelK w (X t) (X t a)) (vy t a)).trans
          (add_le_add le_rfl (norm_sub_le_norm_sub_add_norm_sub
            (planarMaterialLabelVelocity kernelK w (X t) (X t a))
            (planarMaterialLabelVelocity kernelK f (Y t) (Y t a)) (vy t a)))
        have herr := herror t ht a ha
        rw [norm_sub_rev (planarMaterialLabelVelocity kernelK f (Y t) (Y t a)) (vy t a)] at htriangle
        simp only [VV, WW, if_pos ha]
        linarith only [htriangle, hmid, herr, hsource]
      · simp only [VV, WW, if_neg ha, sub_self, norm_zero]
        exact add_nonneg (mul_nonneg hC haff) hδ₀.le)
  intro t ht a ha
  simpa only [XX, YY, if_pos ha] using he t ht a

end Euler2D

end

