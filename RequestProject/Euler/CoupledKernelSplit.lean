module

public import RequestProject.Euler.LogLipschitz
public import RequestProject.Euler.ComplexPlanarBiotSavart

/-! A uniform near/annular/far splitting for two actual singular
Biot--Savart kernel arguments whose distance is bounded by h. -/

@[expose] public section

set_option maxHeartbeats 2500000

noncomputable section

open MeasureTheory Complex ComplexConjugate Set Filter Topology

namespace Euler2D

theorem complex_kernel_diff_split_bounded {a b : ℂ} {h : ℝ}
    (hh : 0 < h) (hab : ‖a - b‖ ≤ h) :
    ‖I * a / (2 * Real.pi * ‖a‖ ^ 2) - I * b / (2 * Real.pi * ‖b‖ ^ 2)‖ ≤
      (truncInvNorm (2 * h) a + truncInvNorm (3 * h) b) / (2 * Real.pi) +
        h / Real.pi * annKernel h a + h / Real.pi := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have hT1 := truncInvNorm_nonneg (2 * h) a
  have hT2 := truncInvNorm_nonneg (3 * h) b
  have hA := annKernel_nonneg h a
  have hhp : 0 ≤ h / Real.pi := by positivity
  have h2 : ‖(2 * (Real.pi : ℂ))‖ = 2 * Real.pi := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpi]
    norm_num
  have hK (z : ℂ) : ‖I * z / (2 * Real.pi * ‖z‖ ^ 2)‖ = ‖z‖⁻¹ / (2 * Real.pi) := by
    rw [kernel_eq_inv_conj, norm_mul, norm_div, Complex.norm_I, h2,
      norm_inv, Complex.norm_conj]
    ring
  by_cases hnear : ‖a‖ < 2 * h
  · have hbnear : ‖b‖ < 3 * h := by
      have htri : ‖b‖ ≤ ‖a‖ + ‖a - b‖ := by
        calc
          _ = ‖a - (a - b)‖ := by congr 1; abel
          _ ≤ _ := norm_sub_le _ _
      linarith
    have e1 : truncInvNorm (2 * h) a = ‖a‖⁻¹ := by simp [truncInvNorm, hnear]
    have e2 : truncInvNorm (3 * h) b = ‖b‖⁻¹ := by simp [truncInvNorm, hbnear]
    calc
      _ ≤ ‖I * a / (2 * Real.pi * ‖a‖ ^ 2)‖ + ‖I * b / (2 * Real.pi * ‖b‖ ^ 2)‖ := norm_sub_le _ _
      _ = (truncInvNorm (2 * h) a + truncInvNorm (3 * h) b) / (2 * Real.pi) := by
        rw [hK, hK, e1, e2]
        ring
      _ ≤ _ := by nlinarith [mul_nonneg hhp hA]
  · have hnear' : 2 * h ≤ ‖a‖ := le_of_not_gt hnear
    have ha : a ≠ 0 := norm_pos_iff.mp (by linarith)
    have hd := kernel_diff_bound ha (show 2 * ‖a - b‖ ≤ ‖a‖ by linarith)
    have he : a - (a - b) = b := by abel
    rw [he] at hd
    have hmain :
        ‖I * a / (2 * Real.pi * ‖a‖ ^ 2) - I * b / (2 * Real.pi * ‖b‖ ^ 2)‖ ≤
          h / Real.pi * (‖a‖ ^ 2)⁻¹ := by
      rw [kernel_eq_inv_conj, kernel_eq_inv_conj, norm_sub_rev, ← mul_sub]
      calc
        _ ≤ ‖a - b‖ / (Real.pi * ‖a‖ ^ 2) := hd
        _ ≤ h / (Real.pi * ‖a‖ ^ 2) :=
          div_le_div_of_nonneg_right hab (by positivity)
        _ = _ := by ring
    refine hmain.trans ?_
    have hT : 0 ≤ (truncInvNorm (2 * h) a + truncInvNorm (3 * h) b) / (2 * Real.pi) := by positivity
    by_cases hfar : ‖a‖ < 1
    · have e3 : annKernel h a = (‖a‖ ^ 2)⁻¹ := by simp [annKernel, hnear', hfar]
      rw [e3]
      linarith
    · have hinv : (‖a‖ ^ 2)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by nlinarith [le_of_not_gt hfar])
      have hle := mul_le_mul_of_nonneg_left hinv hhp
      nlinarith [mul_nonneg hhp hA]

theorem planar_kernel_diff_split_bounded {a b : R2} {h : ℝ}
    (hh : 0 < h) (hab : ‖a - b‖ ≤ h) :
    ‖kernelK a - kernelK b‖ ≤
      (truncInvNorm (2 * h) (complexPhysicalPlane.symm a) +
        truncInvNorm (3 * h) (complexPhysicalPlane.symm b)) / (2 * Real.pi) +
      h / Real.pi * annKernel h (complexPhysicalPlane.symm a) + h / Real.pi := by
  have he (z : R2) : kernelK z = complexPhysicalPlane
      (I * complexPhysicalPlane.symm z / (2 * Real.pi * ‖complexPhysicalPlane.symm z‖ ^ 2)) := by
    rw [complexPhysicalPlane_planar_kernel, LinearIsometryEquiv.apply_symm_apply]
  rw [he a, he b, ← map_sub, LinearIsometryEquiv.norm_map]
  exact complex_kernel_diff_split_bounded hh (by
    simpa only [← map_sub, LinearIsometryEquiv.norm_map] using hab)

end Euler2D

end
