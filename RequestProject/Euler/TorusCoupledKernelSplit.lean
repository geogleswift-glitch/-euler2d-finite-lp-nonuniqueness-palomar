module

public import RequestProject.Euler.TorusCoupledProfiles

/-! A genuine uniform splitting of the original torus kernel for
two nearby material arguments, including all chart-boundary cases. -/

@[expose] public section

set_option maxHeartbeats 3500000

noncomputable section

open MeasureTheory Set Filter Topology Metric Real
open scoped NNReal

namespace Euler2D

def coupledNearProfile (r : ℝ) (x : R2) : ℝ := truncInvNorm r (complexPhysicalPlane.symm x)

def coupledAnnularProfile (h : ℝ) (x : R2) : ℝ := annKernel h (complexPhysicalPlane.symm x)

theorem coupledNearProfile_zero_of_one_le {r : ℝ} (hr : r ≤ 1) (x : R2) (hx : 1 ≤ ‖x‖) :
    coupledNearProfile r x = 0 := by
  have hh : ¬ ‖complexPhysicalPlane.symm x‖ < r := by
    rw [LinearIsometryEquiv.norm_map]
    linarith
  simp only [coupledNearProfile, truncInvNorm, if_neg hh]

theorem coupledAnnularProfile_zero_of_one_le (h : ℝ) (x : R2) (hx : 1 ≤ ‖x‖) :
    coupledAnnularProfile h x = 0 := by
  simp [coupledAnnularProfile, annKernel, LinearIsometryEquiv.norm_map, not_lt.mpr hx]

theorem integrable_coupledNearProfile (r : ℝ) : Integrable (coupledNearProfile r) :=
  complexPhysicalPlane.symm.measurePreserving.integrable_comp_of_integrable (integrable_truncInvNorm r)

theorem integrable_coupledAnnularProfile {h : ℝ} (hh : 0 < h) : Integrable (coupledAnnularProfile h) :=
  complexPhysicalPlane.symm.measurePreserving.integrable_comp_of_integrable (integrable_annKernel hh)

theorem integral_coupledNearProfile {r : ℝ} (hr : 0 < r) :
    (∫ x, coupledNearProfile r x) = 2 * Real.pi * r := by
  have he := complexPhysicalPlane.symm.measurePreserving.integral_comp
    complexPhysicalPlane.symm.toHomeomorph.measurableEmbedding (truncInvNorm r)
  exact he.trans (integral_truncInvNorm hr)

theorem integral_coupledAnnularProfile {h : ℝ} (hh : 0 < h) (hh1 : 2 * h ≤ 1) :
    (∫ x, coupledAnnularProfile h x) = 2 * Real.pi * Real.log (1 / (2 * h)) := by
  have he := complexPhysicalPlane.symm.measurePreserving.integral_comp
    complexPhysicalPlane.symm.toHomeomorph.measurableEmbedding (annKernel h)
  exact he.trans (integral_annKernel hh hh1)

theorem periodicCenteredSource_nonneg {q : R2 → ℝ}
    (hq : ∀ x, 1 ≤ ‖x‖ → q x = 0) (hn : ∀ x, 0 ≤ q x) (x : R2) :
    0 ≤ periodicCenteredSource q x := by rw [periodicCenteredSource_eq_wrapped hq]; exact hn _

theorem local_kernel_diff_split_bounded {C h : ℝ} (hC : 0 ≤ C)
    (hderiv : ∀ z : R2, z ≠ 0 → ‖fderiv ℝ localPlanarKernel z‖ ≤ C * (‖z‖ ^ 2)⁻¹)
    (hh : 0 < h) {a b : R2} (hab : ‖a - b‖ ≤ h) :
    ‖localPlanarKernel a - localPlanarKernel b‖ ≤
      (coupledNearProfile (2 * h) a + coupledNearProfile (3 * h) b) / (2 * Real.pi) +
        (4 * C * h) * coupledAnnularProfile h a + 4 * C * h := by
  have hN1 : 0 ≤ coupledNearProfile (2 * h) a := truncInvNorm_nonneg _ _
  have hN2 : 0 ≤ coupledNearProfile (3 * h) b := truncInvNorm_nonneg _ _
  have hA : 0 ≤ coupledAnnularProfile h a := annKernel_nonneg _ _
  by_cases hnear : ‖a‖ < 2 * h
  · have hbnear : ‖b‖ < 3 * h := by
      have htri : ‖b‖ ≤ ‖a‖ + ‖a - b‖ := by
        calc _ = ‖a - (a - b)‖ := by congr 1; abel
             _ ≤ _ := norm_sub_le _ _
      linarith
    have he1 : coupledNearProfile (2 * h) a = ‖a‖⁻¹ := by
      simp only [coupledNearProfile, truncInvNorm, LinearIsometryEquiv.norm_map, if_pos hnear]
    have he2 : coupledNearProfile (3 * h) b = ‖b‖⁻¹ := by
      simp only [coupledNearProfile, truncInvNorm, LinearIsometryEquiv.norm_map, if_pos hbnear]
    calc
      _ ≤ ‖localPlanarKernel a‖ + ‖localPlanarKernel b‖ := norm_sub_le _ _
      _ ≤ (2 * Real.pi)⁻¹ * ‖a‖⁻¹ + (2 * Real.pi)⁻¹ * ‖b‖⁻¹ :=
        add_le_add (norm_localPlanarKernel_le a) (norm_localPlanarKernel_le b)
      _ = (coupledNearProfile (2 * h) a + coupledNearProfile (3 * h) b) / (2 * Real.pi) := by
        rw [he1, he2]; ring
      _ ≤ _ := by
        nlinarith [mul_nonneg (show 0 ≤ 4 * C * h by positivity) hA]
  · have hnear' : 2 * h ≤ ‖a‖ := le_of_not_gt hnear
    have ha : a ≠ 0 := norm_pos_iff.mp (by linarith)
    have hd := norm_localPlanarKernel_sub_le hC hderiv ha
      (show ‖b - a‖ ≤ ‖a‖ / 2 by rw [norm_sub_rev]; linarith)
    have hmain : ‖localPlanarKernel a - localPlanarKernel b‖ ≤ (4 * C * h) * (‖a‖ ^ 2)⁻¹ := by
      calc
        _ = ‖localPlanarKernel b - localPlanarKernel a‖ := norm_sub_rev _ _
        _ ≤ (4 * C * (‖a‖ ^ 2)⁻¹) * ‖b - a‖ := hd
        _ ≤ (4 * C * (‖a‖ ^ 2)⁻¹) * h :=
          mul_le_mul_of_nonneg_left (by rw [norm_sub_rev]; exact hab) (by positivity)
        _ = _ := by ring
    refine hmain.trans ?_
    have hN : 0 ≤ (coupledNearProfile (2 * h) a + coupledNearProfile (3 * h) b) / (2 * Real.pi) := by positivity
    by_cases hfar : ‖a‖ < 1
    · have he : coupledAnnularProfile h a = (‖a‖ ^ 2)⁻¹ := by
        have hc : 2 * h ≤ ‖a‖ ∧ ‖a‖ < 1 := ⟨hnear', hfar⟩
        simp only [coupledAnnularProfile, annKernel, LinearIsometryEquiv.norm_map, if_pos hc]
      rw [he]
      nlinarith [mul_nonneg hC hh.le]
    · have hinv : (‖a‖ ^ 2)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by nlinarith [le_of_not_gt hfar])
      have hb := mul_le_mul_of_nonneg_left hinv (show 0 ≤ 4 * C * h by positivity)
      nlinarith [mul_nonneg (show 0 ≤ 4 * C * h by positivity) hA]

theorem periodicLocalKernel_common_chart (a b : R2) (hab : ‖b - a‖ ≤ 1 / 2) :
    periodicLocalKernel b = localPlanarKernel (torusWrap a + (b - a) - torusCenter) := by
  have hp := isTorusPeriodic_comp_add_right isTorusPeriodic_periodicLocalKernel (b - a)
  have he := hp.eq_torusWrap a
  change periodicLocalKernel (torusWrap a + (b - a)) = periodicLocalKernel (a + (b - a)) at he
  rw [show a + (b - a) = b by abel] at he
  rw [← he]
  exact periodicLocalKernel_add_eq_on_box (torusRep_mem _) hab

theorem torus_kernel_diff_split_bounded {C h : ℝ} {L : ℝ≥0} (hC : 0 ≤ C)
    (hderiv : ∀ z : R2, z ≠ 0 → ‖fderiv ℝ localPlanarKernel z‖ ≤ C * (‖z‖ ^ 2)⁻¹)
    (hLip : LipschitzWith L (perpGradient torusGreenCorrection))
    (hh : 0 < h) (hh1 : h ≤ 1 / 4) {a b : R2} (hab : ‖a - b‖ ≤ h) :
    ‖torusBiotSavartKernel a - torusBiotSavartKernel b‖ ≤
      (periodicCenteredSource (coupledNearProfile (2 * h)) a +
        periodicCenteredSource (coupledNearProfile (3 * h)) b) / (2 * Real.pi) +
      (4 * C * h) * periodicCenteredSource (coupledAnnularProfile h) a + (4 * C + (L : ℝ)) * h := by
  have hsmall : ‖b - a‖ ≤ 1 / 2 := by rw [norm_sub_rev]; linarith
  let u := torusWrap a - torusCenter
  let v := torusWrap a + (b - a) - torusCenter
  have huv : ‖u - v‖ ≤ h := by
    have he : u - v = a - b := by dsimp only [u, v]; abel
    rw [he]; exact hab
  have hlocal := local_kernel_diff_split_bounded hC hderiv hh huv
  have hpa : periodicLocalKernel a = localPlanarKernel u := by
    rw [← isTorusPeriodic_periodicLocalKernel.eq_torusWrap a]
    exact periodicLocalKernel_eq_on_box (torusRep_mem _)
  have hpb : periodicLocalKernel b = localPlanarKernel v := periodicLocalKernel_common_chart a b hsmall
  have hn1 : periodicCenteredSource (coupledNearProfile (2 * h)) a = coupledNearProfile (2 * h) u :=
    periodicCenteredSource_eq_wrapped (coupledNearProfile_zero_of_one_le (by linarith)) a
  have hn2 : periodicCenteredSource (coupledNearProfile (3 * h)) b = coupledNearProfile (3 * h) v :=
    periodicCenteredSource_common_chart (coupledNearProfile_zero_of_one_le (by linarith)) a b hsmall
  have ha1 : periodicCenteredSource (coupledAnnularProfile h) a = coupledAnnularProfile h u :=
    periodicCenteredSource_eq_wrapped (coupledAnnularProfile_zero_of_one_le h) a
  have hcorr : ‖perpGradient torusGreenCorrection a - perpGradient torusGreenCorrection b‖ ≤ (L : ℝ) * h := by
    have hl := hLip.dist_le_mul a b
    rw [dist_eq_norm, dist_eq_norm] at hl
    exact hl.trans (mul_le_mul_of_nonneg_left hab L.coe_nonneg)
  change ‖(periodicLocalKernel a + perpGradient torusGreenCorrection a) -
    (periodicLocalKernel b + perpGradient torusGreenCorrection b)‖ ≤ _
  rw [add_sub_add_comm, hn1, hn2, ha1]
  have hmain := (norm_add_le (periodicLocalKernel a - periodicLocalKernel b)
    (perpGradient torusGreenCorrection a - perpGradient torusGreenCorrection b)).trans
      (add_le_add (by simpa only [hpa, hpb] using hlocal) hcorr)
  nlinarith

end Euler2D

end
