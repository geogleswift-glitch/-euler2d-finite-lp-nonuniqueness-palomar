module

public import RequestProject.Euler.PeriodicLocalMaterialAffine

/-! A genuine mixed torus/whole-plane singular coupling. Only the first
configuration preserves torus area; the second is a true volume-preserving
plane homeomorphism. Local charts are required solely on active sources. -/

@[expose] public section
set_option maxHeartbeats 3000000
noncomputable section
open MeasureTheory Set Filter Topology Metric Real
namespace Euler2D

theorem periodicLocalKernel_eq_kernelK_near {z : R2} (hz : ‖z - torusCenter‖ ≤ 1 / 2) :
    periodicLocalKernel z = kernelK (z - torusCenter) := by
  rw [periodicLocalKernel_eq_on_box (norm_sub_center_lt_one_mem_box (by linarith)),
    localPlanarKernel_eq_kernelK_of_norm_le_half hz]

theorem planarMaterialLabelVelocity_eq_box_of_support
    {w : R2 → ℝ} (hwzero : ∀ b, b ∉ torusBox → w b = 0)
    (Y : R2 → R2) (y : R2) :
    planarMaterialLabelVelocity kernelK w Y y = ∫ b in torusBox, w b • kernelK (y - Y b) := by
  unfold planarMaterialLabelVelocity
  exact (setIntegral_eq_integral_of_forall_compl_eq_zero (fun b hb => by rw [hwzero b hb, zero_smul])).symm

theorem norm_hybrid_periodicLocal_planarMaterial_sub_le_raw
    {w : R2 → ℝ} {B h : ℝ} (hw : Integrable w) (hB : ∀ b, ‖w b‖ ≤ B)
    (hwzero : ∀ b, b ∉ torusBox → w b = 0)
    {X : R2 → R2} (hX : TorusAreaPreserving X) (Y : R2 ≃ₜ R2)
    (hY : MeasurePreserving Y volume volume)
    (hh : 0 < h) (hh1 : h ≤ 1 / 4) (x y : R2)
    (hsmall : ∀ᵐ b ∂μT, w b ≠ 0 → ‖x - X b‖ ≤ 1 / 2)
    (hargs : ∀ᵐ b ∂μT, w b ≠ 0 → ‖(x - X b) - (y - Y b)‖ ≤ h) :
    ‖periodicLocalMaterialVelocity w X x - planarMaterialLabelVelocity kernelK w Y y‖ ≤
      B * (5 * h + 2 * h * Real.log (1 / (2 * h))) + h / Real.pi * ∫ b in torusBox, ‖w b‖ := by
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  have hzero1 := coupledNearProfile_zero_of_one_le (show 2 * h ≤ 1 by linarith)
  have hzero3 := coupledAnnularProfile_zero_of_one_le h
  let N₁ (b : R2) := periodicCenteredSource (coupledNearProfile (2 * h)) ((x + torusCenter) - X b)
  let N₂ (b : R2) := coupledNearProfile (3 * h) (y - Y b)
  let A (b : R2) := periodicCenteredSource (coupledAnnularProfile h) ((x + torusCenter) - X b)
  have hi₁ : Integrable N₁ μT := integrable_periodicCenteredSource_material (integrable_coupledNearProfile _) hzero1 hX x
  have hi₂global : Integrable N₂ := integrable_complex_profile_material _ (integrable_truncInvNorm _) Y hY y
  have hi₂ : Integrable N₂ μT := hi₂global.integrableOn
  have hi₃ : Integrable A μT := integrable_periodicCenteredSource_material (integrable_coupledAnnularProfile hh) hzero3 hX x
  have hn₁ (b : R2) : 0 ≤ N₁ b := periodicCenteredSource_nonneg hzero1 (fun _ => truncInvNorm_nonneg _ _) _
  have hn₂ (b : R2) : 0 ≤ N₂ b := truncInvNorm_nonneg _ _
  have hn₃ (b : R2) : 0 ≤ A b := periodicCenteredSource_nonneg hzero3 (fun _ => annKernel_nonneg _ _) _
  let G (b : R2) := B / (2 * Real.pi) * N₁ b + B / (2 * Real.pi) * N₂ b +
    B * h / Real.pi * A b + h / Real.pi * ‖w b‖
  have i1 := hi₁.const_mul (B / (2 * Real.pi))
  have i2 := hi₂.const_mul (B / (2 * Real.pi))
  have i3 := hi₃.const_mul (B * h / Real.pi)
  have i4 : Integrable (fun b => h / Real.pi * ‖w b‖) μT := hw.norm.integrableOn.const_mul _
  have i12 : Integrable (fun b => B / (2 * Real.pi) * N₁ b + B / (2 * Real.pi) * N₂ b) μT := i1.add i2
  have i123 : Integrable (fun b => B / (2 * Real.pi) * N₁ b + B / (2 * Real.pi) * N₂ b + B * h / Real.pi * A b) μT := i12.add i3
  have hGi : Integrable G μT := i123.add i4
  have hbound : ∀ᵐ b ∂μT,
      ‖w b • (periodicLocalKernel ((x + torusCenter) - X b) - kernelK (y - Y b))‖ ≤ G b := by
    filter_upwards [hsmall, hargs] with b hb harg
    have hN1 := hn₁ b
    have hN2 := hn₂ b
    have hAn := hn₃ b
    by_cases hw0 : w b = 0
    · simp only [hw0, zero_smul, norm_zero]
      dsimp only [G]
      positivity
    · have hnorm : ‖((x + torusCenter) - X b) - torusCenter‖ ≤ 1 / 2 := by
        convert hb hw0 using 1 <;> congr 1 <;> abel
      have hbox : (x + torusCenter) - X b ∈ torusBox := norm_sub_center_lt_one_mem_box (by linarith)
      have heN : N₁ b = coupledNearProfile (2 * h) (x - X b) := by
        dsimp only [N₁]
        rw [periodicCenteredSource_eq_on_box hzero1 hbox]
        congr 1
        abel
      have heA : A b = coupledAnnularProfile h (x - X b) := by
        dsimp only [A]
        rw [periodicCenteredSource_eq_on_box hzero3 hbox]
        congr 1
        abel
      have heK : periodicLocalKernel ((x + torusCenter) - X b) = kernelK (x - X b) := by
        rw [periodicLocalKernel_eq_kernelK_near hnorm]
        congr 1
        abel
      rw [norm_smul, heK]
      have hk := planar_kernel_diff_split_bounded hh (harg hw0)
      change ‖kernelK (x - X b) - kernelK (y - Y b)‖ ≤
        (coupledNearProfile (2 * h) (x - X b) + N₂ b) / (2 * Real.pi) +
          h / Real.pi * coupledAnnularProfile h (x - X b) + h / Real.pi at hk
      rw [← heN, ← heA] at hk
      have hP : 0 ≤ (N₁ b + N₂ b) / (2 * Real.pi) + h / Real.pi * A b := by positivity
      calc
        _ ≤ ‖w b‖ * ((N₁ b + N₂ b) / (2 * Real.pi) + h / Real.pi * A b + h / Real.pi) :=
          mul_le_mul_of_nonneg_left hk (norm_nonneg _)
        _ ≤ B * ((N₁ b + N₂ b) / (2 * Real.pi) + h / Real.pi * A b) + h / Real.pi * ‖w b‖ := by
          nlinarith [mul_le_mul_of_nonneg_right (hB b) hP]
        _ = _ := by dsimp only [G]; ring
  have e1 : (∫ b in torusBox, N₁ b) = 2 * Real.pi * (2 * h) :=
    (integral_periodicCenteredSource_material (integrable_coupledNearProfile _) hzero1 hX x).trans
      (integral_coupledNearProfile (by positivity))
  have e2 : (∫ b in torusBox, N₂ b) ≤ 2 * Real.pi * (3 * h) := by
    refine (setIntegral_le_integral hi₂global (ae_of_all _ hn₂)).trans_eq ?_
    exact (integral_complex_profile_material _ Y hY y).trans (integral_truncInvNorm (by positivity))
  have e3 : (∫ b in torusBox, A b) = 2 * Real.pi * Real.log (1 / (2 * h)) :=
    (integral_periodicCenteredSource_material (integrable_coupledAnnularProfile hh) hzero3 hX x).trans
      (integral_coupledAnnularProfile hh (by linarith))
  have hIG : (∫ b in torusBox, G b) ≤
      B * (5 * h + 2 * h * Real.log (1 / (2 * h))) + h / Real.pi * ∫ b in torusBox, ‖w b‖ := by
    dsimp only [G]
    rw [integral_add i123 i4, integral_add i12 i3, integral_add i1 i2,
      integral_const_mul, integral_const_mul, integral_const_mul, integral_const_mul, e1, e3]
    have he2 := mul_le_mul_of_nonneg_left e2 (show 0 ≤ B / (2 * Real.pi) by positivity)
    have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
    field_simp at he2 ⊢
    nlinarith
  unfold periodicLocalMaterialVelocity
  rw [planarMaterialLabelVelocity_eq_box_of_support hwzero Y y,
    ← integral_sub (integrable_periodicLocalMaterial_integrand hw.integrableOn (ae_of_all _ hB) hX x)
      (integrable_planarMaterialBiotSavart_integrand hw hB Y hY y).integrableOn]
  have he : (fun b => w b • periodicLocalKernel ((x + torusCenter) - X b) - w b • kernelK (y - Y b)) =
      (fun b => w b • (periodicLocalKernel ((x + torusCenter) - X b) - kernelK (y - Y b))) :=
    funext (fun b => (smul_sub _ _ _).symm)
  rw [he]
  exact (norm_integral_le_of_norm_le hGi hbound).trans hIG

end Euler2D
end
