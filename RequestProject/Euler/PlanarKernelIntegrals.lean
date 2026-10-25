module

public import RequestProject.Euler.PlanarKernelBounds
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! Exact radial integrals for the near/far kernel estimates. -/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology Metric Real
open scoped ContDiff

namespace Euler2D

lemma integral_polar_angle_one :
    (∫ _θ in Ioo (-Real.pi) Real.pi, (1 : ℝ)) = 2 * Real.pi := by
  rw [setIntegral_congr_set Ioo_ae_eq_Ioc,
    ← intervalIntegral.integral_of_le (neg_le_self Real.pi_pos.le), intervalIntegral.integral_const]
  simp only [smul_eq_mul]
  ring

theorem integral_radialR2 (f : ℝ → ℝ) :
    (∫ x : R2, f ‖x‖) = (∫ r in Ioi (0 : ℝ), r * f r) * (2 * Real.pi) := by
  rw [← integral_polarR2 (fun x : R2 => f ‖x‖)]
  calc
    _ = ∫ p in polarCoord.target, (p.1 * f p.1) * (1 : ℝ) := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem polarCoord.open_target.measurableSet] with p hp
      have hp0 : 0 < p.1 := hp.1
      simp only [norm_polarPoint, abs_of_pos hp0, smul_eq_mul, mul_one]
    _ = _ := by
      change (∫ p in Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi,
        (p.1 * f p.1) * (1 : ℝ)) = _
      rw [Measure.volume_eq_prod, ← integral_polar_angle_one]
      exact setIntegral_prod_mul (fun r : ℝ => r * f r) (fun _ : ℝ => (1 : ℝ))
        (Ioi (0 : ℝ)) (Ioo (-Real.pi) Real.pi)

theorem integrable_radialR2 {f : ℝ → ℝ}
    (hf : AEStronglyMeasurable (fun x : R2 => f ‖x‖))
    (hI : IntegrableOn (fun r : ℝ => r * f r) (Ioi (0 : ℝ))) :
    Integrable (fun x : R2 => f ‖x‖) := by
  apply integrable_of_polarR2 hf
  have hA : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Ioo (-Real.pi) Real.pi) :=
    integrableOn_const (by simp)
  have hprod := hI.mul_prod hA
  rw [Measure.prod_restrict, ← Measure.volume_eq_prod] at hprod
  apply hprod.congr
  filter_upwards [ae_restrict_mem polarCoord.open_target.measurableSet] with p hp
  have hp0 : 0 < p.1 := hp.1
  simp only [smul_eq_mul, norm_polarPoint, abs_of_pos hp0, mul_one]

theorem integral_norm_kernelK_closedBall {r : ℝ} (hr : 0 ≤ r) :
    (∫ x in closedBall (0 : R2) r, ‖kernelK x‖) = r := by
  rw [← integral_indicator measurableSet_closedBall]
  let f : ℝ → ℝ := fun s => (Icc (0 : ℝ) r).indicator
    (fun s => (2 * Real.pi)⁻¹ * s⁻¹) s
  have he (x : R2) : (closedBall (0 : R2) r).indicator (fun x => ‖kernelK x‖) x = f ‖x‖ := by
    by_cases hx : ‖x‖ ≤ r
    · simp only [Set.indicator_of_mem (mem_closedBall_zero_iff.mpr hx), f,
        Set.indicator_of_mem (show ‖x‖ ∈ Icc (0 : ℝ) r from ⟨norm_nonneg x, hx⟩), norm_planar_kernelK]
    · simp only [Set.indicator_of_notMem (show x ∉ closedBall (0 : R2) r from
          fun h => hx (mem_closedBall_zero_iff.mp h)), f,
        Set.indicator_of_notMem (show ‖x‖ ∉ Icc (0 : ℝ) r from fun h => hx h.2)]
  simp_rw [he]
  rw [integral_radialR2]
  have hradial : (∫ s in Ioi (0 : ℝ), s * f s) = r * (2 * Real.pi)⁻¹ := by
    calc
      _ = ∫ s in Ioi (0 : ℝ), (Ioc (0 : ℝ) r).indicator (fun _ => (2 * Real.pi)⁻¹) s := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
        have hs0 : 0 < s := hs
        by_cases hsr : s ≤ r
        · simp only [f, Set.indicator_of_mem (show s ∈ Icc (0 : ℝ) r from ⟨hs.le, hsr⟩),
            Set.indicator_of_mem (show s ∈ Ioc (0 : ℝ) r from ⟨hs, hsr⟩)]
          field_simp [hs0.ne']
        · simp only [f, Set.indicator_of_notMem (show s ∉ Icc (0 : ℝ) r from fun h => hsr h.2),
            Set.indicator_of_notMem (show s ∉ Ioc (0 : ℝ) r from fun h => hsr h.2), mul_zero]
      _ = ∫ s in Ioc (0 : ℝ) r, (2 * Real.pi)⁻¹ := by
        rw [setIntegral_indicator measurableSet_Ioc, inter_eq_right.mpr (fun _ h => h.1)]
      _ = r * (2 * Real.pi)⁻¹ := by
        rw [← intervalIntegral.integral_of_le hr, intervalIntegral.integral_const]
        simp only [sub_zero, smul_eq_mul]
  rw [hradial]
  field_simp [Real.pi_ne_zero]

theorem integrableOn_norm_kernelK_closedBall {r : ℝ} (hr : 0 ≤ r) :
    IntegrableOn (fun x => ‖kernelK x‖) (closedBall (0 : R2) r) := by
  by_cases hr0 : r = 0
  · subst r
    rw [closedBall_zero]
    exact integrableOn_singleton (by simp) (isCompact_singleton (x := (0 : R2))).measure_lt_top
  · by_contra hn
    have hz : (∫ x in closedBall (0 : R2) r, ‖kernelK x‖) = 0 := integral_undef hn
    rw [integral_norm_kernelK_closedBall hr] at hz
    exact hr0 hz

theorem integral_norm_localPlanarKernel_closedBall_le {r : ℝ} (hr : 0 ≤ r) :
    (∫ x in closedBall (0 : R2) r, ‖localPlanarKernel x‖) ≤ r := by
  calc
    _ ≤ ∫ x in closedBall (0 : R2) r, ‖kernelK x‖ := by
      apply integral_mono (integrable_localPlanarKernel.norm.integrableOn)
        (integrableOn_norm_kernelK_closedBall hr)
      intro x
      simpa only [norm_planar_kernelK] using norm_localPlanarKernel_le x
    _ = r := integral_norm_kernelK_closedBall hr

theorem integral_norm_localPlanarKernel_le_one : (∫ x, ‖localPlanarKernel x‖) ≤ 1 := by
  have he : (∫ x in closedBall (0 : R2) 1, ‖localPlanarKernel x‖) =
      ∫ x, ‖localPlanarKernel x‖ := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    have hn : 1 < ‖x‖ := lt_of_not_ge (fun h => hx (mem_closedBall_zero_iff.mpr h))
    rw [localPlanarKernel_eq_zero_of_one_le_norm hn.le, norm_zero]
  rw [← he]
  exact integral_norm_localPlanarKernel_closedBall_le (by norm_num)

theorem integral_inverse_sq_annulus {r R : ℝ} (hr : 0 < r) (hR : r ≤ R) :
    (∫ x in closedBall (0 : R2) R \ closedBall (0 : R2) r, (‖x‖ ^ 2)⁻¹) =
      (2 * Real.pi) * Real.log (R / r) := by
  rw [← integral_indicator (measurableSet_closedBall.diff measurableSet_closedBall)]
  let f : ℝ → ℝ := fun s => (Ioc r R).indicator (fun s => (s ^ 2)⁻¹) s
  have he (x : R2) :
      (closedBall (0 : R2) R \ closedBall (0 : R2) r).indicator
        (fun x => (‖x‖ ^ 2)⁻¹) x = f ‖x‖ := by
    have hc : x ∈ closedBall (0 : R2) R \ closedBall (0 : R2) r ↔ ‖x‖ ∈ Ioc r R := by
      simp only [mem_diff, mem_closedBall_zero_iff, mem_Ioc, not_le, and_comm]
    by_cases hx : ‖x‖ ∈ Ioc r R
    · simp only [Set.indicator_of_mem (hc.mpr hx), f, Set.indicator_of_mem hx]
    · simp only [Set.indicator_of_notMem (fun h => hx (hc.mp h)), f, Set.indicator_of_notMem hx]
  simp_rw [he]
  rw [integral_radialR2]
  have hradial : (∫ s in Ioi (0 : ℝ), s * f s) = Real.log (R / r) := by
    calc
      _ = ∫ s in Ioi (0 : ℝ), (Ioc r R).indicator (fun s : ℝ => s⁻¹) s := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
        have hs0 : 0 < s := hs
        by_cases hsr : s ∈ Ioc r R
        · simp only [f, Set.indicator_of_mem hsr]
          field_simp [hs0.ne']
        · simp only [f, Set.indicator_of_notMem hsr, mul_zero]
      _ = ∫ s in Ioc r R, s⁻¹ := by
        have hsub : Ioc r R ⊆ Ioi (0 : ℝ) := fun _ h => hr.trans h.1
        rw [setIntegral_indicator measurableSet_Ioc, inter_eq_right.mpr hsub]
      _ = Real.log (R / r) := by
        rw [← intervalIntegral.integral_of_le hR]
        exact integral_inv_of_pos hr (hr.trans_le hR)
  rw [hradial, mul_comm]

theorem integrableOn_inverse_sq_annulus {r R : ℝ} (hr : 0 < r) :
    IntegrableOn (fun x : R2 => (‖x‖ ^ 2)⁻¹)
      (closedBall (0 : R2) R \ closedBall (0 : R2) r) := by
  let s := closedBall (0 : R2) R \ closedBall (0 : R2) r
  have hs : MeasurableSet s := measurableSet_closedBall.diff measurableSet_closedBall
  have hfinite : volume s ≠ ⊤ := measure_ne_top_of_subset diff_subset
    (isCompact_closedBall (0 : R2) R).measure_ne_top
  have hI : IntegrableOn (fun _ : R2 => (r ^ 2)⁻¹) s := integrableOn_const hfinite
  apply hI.mono' (measurable_norm.pow_const 2).inv.aestronglyMeasurable
  filter_upwards [ae_restrict_mem hs] with x hx
  have hxr : r < ‖x‖ := lt_of_not_ge (fun h => hx.2 (mem_closedBall_zero_iff.mpr h))
  rw [Pi.inv_apply, Real.norm_of_nonneg (inv_nonneg.mpr (sq_nonneg _))]
  exact (inv_le_inv₀ (sq_pos_of_pos (hr.trans hxr)) (sq_pos_of_pos hr)).mpr (by nlinarith)

end Euler2D

end
