module

public import RequestProject.Euler.TorusCoupledKernelSplit
public import RequestProject.Euler.TorusSmoothKernelBounds

/-! A true near/far mass-amplitude estimate for the original periodic
Biot--Savart kernel. No bound by the total maximal finite amplitude is used. -/

@[expose] public section

set_option maxHeartbeats 2200000

noncomputable section

open MeasureTheory Set Filter Topology Metric Real
open scoped NNReal ENNReal

namespace Euler2D

theorem norm_localPlanarKernel_near_far {r : ℝ} (hr : 0 < r) (z : R2) :
    ‖localPlanarKernel z‖ ≤ (coupledNearProfile r z + r⁻¹) / (2 * Real.pi) := by
  have hcoef : 0 ≤ (2 * Real.pi)⁻¹ := by positivity
  apply (norm_localPlanarKernel_le z).trans
  by_cases hn : ‖z‖ < r
  · have he : coupledNearProfile r z = ‖z‖⁻¹ := by
      simp only [coupledNearProfile, truncInvNorm, LinearIsometryEquiv.norm_map, if_pos hn]
    rw [he, div_eq_mul_inv]
    nlinarith [mul_nonneg hcoef (inv_nonneg.mpr hr.le)]
  · have hi : ‖z‖⁻¹ ≤ r⁻¹ := inv_anti₀ hr (not_lt.mp hn)
    have hN : 0 ≤ coupledNearProfile r z := truncInvNorm_nonneg _ _
    rw [div_eq_mul_inv]
    nlinarith [mul_le_mul_of_nonneg_left hi hcoef, mul_nonneg hcoef hN]

theorem norm_torusBiotSavartKernel_near_far {r C : ℝ} (hr : 0 < r) (hr1 : r ≤ 1)
    (hC : ∀ x, ‖perpGradient torusGreenCorrection x‖ ≤ C) (x : R2) :
    ‖torusBiotSavartKernel x‖ ≤
      (periodicCenteredSource (coupledNearProfile r) x + r⁻¹) / (2 * Real.pi) + C := by
  have hzero := coupledNearProfile_zero_of_one_le hr1
  have hh := norm_localPlanarKernel_near_far hr (torusWrap x - torusCenter)
  rw [← periodicCenteredSource_eq_wrapped hzero x] at hh
  exact (norm_add_le _ _).trans
    (add_le_add (by simpa only [periodicLocalKernel_eq_wrapped] using hh) (hC x))

theorem torusKernelVelocity_bound_split {w : R2 → ℝ} {M C r : ℝ}
    (hw : Integrable w μT) (hM0 : 0 ≤ M) (hM : ∀ᵐ y ∂μT, ‖w y‖ ≤ M)
    (hC : ∀ x, ‖perpGradient torusGreenCorrection x‖ ≤ C)
    (hr : 0 < r) (hr1 : r ≤ 1) (x : R2) :
    ‖torusKernelVelocity w x‖ ≤
      M * r + (∫ y in torusBox, |w y|) / r + C * ∫ y in torusBox, |w y| := by
  let N := periodicCenteredSource (coupledNearProfile r)
  have hzero := coupledNearProfile_zero_of_one_le hr1
  have hNi : Integrable N μT := integrable_periodicCenteredSource (integrable_coupledNearProfile r) hzero
  have hNp : IsTorusPeriodic N := isTorusPeriodic_periodicCenteredSource _
  have harg : (fun y => N (x - y + torusCenter)) = N ∘ (fun y => (x + torusCenter) - y) := by
    funext y
    congr 1
    abel
  have hNarg : Integrable (fun y => N (x - y + torusCenter)) μT := by
    rw [harg]
    exact (torusAreaPreserving_sub_left _).integrable_comp hNi hNp
  have hNint : (∫ y in torusBox, N (x - y + torusCenter)) = 2 * Real.pi * r := by
    rw [harg]
    exact ((torusAreaPreserving_sub_left _).integral_comp hNi.aestronglyMeasurable hNp).trans
      ((integral_periodicCenteredSource hzero).trans (integral_coupledNearProfile hr))
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0)
  have hBint : Integrable (fun y => M / (2 * Real.pi) * N (x - y + torusCenter) +
      (r⁻¹ / (2 * Real.pi) + C) * |w y|) μT :=
    (hNarg.const_mul _).add (hw.abs.const_mul _)
  have hbound : ‖torusKernelVelocity w x‖ ≤
      ∫ y in torusBox, M / (2 * Real.pi) * N (x - y + torusCenter) +
        (r⁻¹ / (2 * Real.pi) + C) * |w y| := by
    apply norm_integral_le_of_norm_le hBint
    filter_upwards [hM] with y hy
    have hN0 : 0 ≤ N (x - y + torusCenter) :=
      periodicCenteredSource_nonneg hzero (fun _ => truncInvNorm_nonneg _ _) _
    have hK := norm_torusBiotSavartKernel_near_far hr hr1 hC (x - y + torusCenter)
    rw [norm_smul]
    calc
      _ ≤ ‖w y‖ * ((N (x - y + torusCenter) + r⁻¹) / (2 * Real.pi) + C) :=
        mul_le_mul_of_nonneg_left hK (norm_nonneg _)
      _ = ‖w y‖ * (N (x - y + torusCenter) / (2 * Real.pi)) +
          (r⁻¹ / (2 * Real.pi) + C) * |w y| := by rw [Real.norm_eq_abs]; ring
      _ ≤ M * (N (x - y + torusCenter) / (2 * Real.pi)) +
          (r⁻¹ / (2 * Real.pi) + C) * |w y| := by
        have hh : ‖w y‖ * (N (x - y + torusCenter) / (2 * Real.pi)) ≤
            M * (N (x - y + torusCenter) / (2 * Real.pi)) :=
          mul_le_mul_of_nonneg_right hy (div_nonneg hN0 (by positivity : 0 ≤ 2 * Real.pi))
        exact add_le_add hh le_rfl
      _ = _ := by ring
  rw [integral_add (hNarg.const_mul _) (hw.abs.const_mul _), integral_const_mul,
    integral_const_mul, hNint] at hbound
  have he : M / (2 * Real.pi) * (2 * Real.pi * r) = M * r := by
    field_simp
  rw [he] at hbound
  have hpi : (2 * Real.pi)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith [Real.pi_gt_three])
  have hA : 0 ≤ ∫ y in torusBox, |w y| := integral_nonneg (fun y => abs_nonneg _)
  refine hbound.trans ?_
  simp only [div_eq_mul_inv]
  nlinarith [mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hpi (inv_nonneg.mpr hr.le)) hA]

theorem exists_torusKernelVelocity_scaled_mass_amplitude_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {w : R2 → ℝ} {A r B₁ Binf : ℝ},
      Integrable w μT → 0 ≤ A → 0 < r → r ≤ 1 → 0 ≤ B₁ → 0 ≤ Binf →
      (∀ᵐ y ∂μT, ‖w y‖ ≤ Binf * A) →
      (∫ y in torusBox, |w y|) ≤ B₁ * A * r ^ 2 → ∀ x,
      ‖torusKernelVelocity w x‖ ≤ (Binf + B₁ + C * B₁) * A * r := by
  obtain ⟨C, hC, _, _⟩ := exists_torusGreenCorrection_perpGradient_bounds
  refine ⟨C, C.coe_nonneg, ?_⟩
  intro w A r B₁ Binf hw hA hr hr1 hB₁ hBinf hM hmass x
  have hh := torusKernelVelocity_bound_split hw (mul_nonneg hBinf hA) hM hC hr hr1 x
  have hAr : 0 ≤ B₁ * A * r := by positivity
  calc
    _ ≤ (Binf * A) * r + (B₁ * A * r ^ 2) / r + (C : ℝ) * (B₁ * A * r ^ 2) := by
      refine hh.trans (add_le_add (add_le_add le_rfl
        (div_le_div_of_nonneg_right hmass hr.le)) (mul_le_mul_of_nonneg_left hmass C.coe_nonneg))
    _ = (Binf * A) * r + B₁ * A * r + (C : ℝ) * (B₁ * A * r ^ 2) := by
      field_simp
      <;> ring
    _ ≤ (Binf * A) * r + B₁ * A * r + (C : ℝ) * (B₁ * A * r) := by
      apply add_le_add le_rfl
      apply mul_le_mul_of_nonneg_left _ C.coe_nonneg
      nlinarith [mul_nonneg hAr (sub_nonneg.mpr hr1)]
    _ = _ := by ring

end Euler2D

end
