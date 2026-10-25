module

public import RequestProject.Euler.PlanarKernelWeak

/-! Genuine integrability and off-origin smoothness of the local kernel. -/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology Metric Real
open scoped ENNReal ContDiff

namespace Euler2D

lemma integrableOn_polar_of_continuous_radialSupport
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {f : ℝ × ℝ → F}
    (hf : Continuous f) {R : ℝ}
    (hzero : ∀ p ∈ polarCoord.target, R ≤ p.1 → f p = 0) :
    IntegrableOn f polarCoord.target := by
  let Q : Set (ℝ × ℝ) := Icc (0 : ℝ) R ×ˢ Icc (-Real.pi) Real.pi
  have hQ : MeasurableSet Q := measurableSet_Icc.prod measurableSet_Icc
  have hI : IntegrableOn f Q :=
    hf.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
  apply hI.integrable_indicator hQ |>.integrableOn.congr
  filter_upwards [ae_restrict_mem polarCoord.open_target.measurableSet] with p hp
  by_cases hr : p.1 ≤ R
  · have hpQ : p ∈ Q := ⟨⟨hp.1.le, hr⟩, hp.2.1.le, hp.2.2.le⟩
    exact Set.indicator_of_mem hpQ _
  · have hpQ : p ∉ Q := fun h => hr h.1.2
    rw [Set.indicator_of_notMem hpQ, hzero p hp (le_of_not_ge hr)]

lemma polar_cutoffKernelK (χ : ℝ → ℝ) (r θ : ℝ) (hr : 0 < r) :
    r • cutoffKernelK χ (polarPoint r θ) =
      (χ (r ^ 2) / (2 * Real.pi)) • perpJ (polarUnit θ) := by
  unfold cutoffKernelK radialKernelCutoff
  rw [norm_polarPoint, abs_of_pos hr, polarPoint, kernelK_smul hr, kernelK, norm_polarUnit]
  simp only [one_pow, mul_one, smul_smul]
  congr 1
  field_simp [hr.ne', Real.pi_ne_zero]

/-- The local singularity `1/|x|` is genuinely integrable in the plane;
the cutoff is only required to be continuous and compactly supported. -/
theorem integrable_cutoffKernelK {χ : ℝ → ℝ} (hχ : Continuous χ)
    (hs : HasCompactSupport χ) : Integrable (cutoffKernelK χ) := by
  let B : ℝ × ℝ → R2 := fun p =>
    (χ (p.1 ^ 2) / (2 * Real.pi)) • perpJ (polarUnit p.2)
  have hB : Continuous B :=
    ((hχ.comp (continuous_fst.pow 2)).div_const (2 * Real.pi)).smul
      (continuous_polarPerpUnit.comp continuous_snd)
  obtain ⟨R, hR, hzero⟩ := hs.exists_pos_le_norm
  have hI : IntegrableOn B polarCoord.target := by
    apply integrableOn_polar_of_continuous_radialSupport hB (R := R + 1)
    intro p hp hr
    have hb : R ≤ p.1 ^ 2 := by nlinarith
    have hz : χ (p.1 ^ 2) = 0 :=
      hzero _ (by simpa only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg p.1)] using hb)
    simp only [B, hz, zero_div, zero_smul]
  have hmeas : Measurable (cutoffKernelK χ) :=
    (hχ.measurable.comp (continuous_norm.measurable.pow_const 2)).smul measurable_kernelK
  apply integrable_of_polarR2 hmeas.aestronglyMeasurable
  apply hI.congr
  filter_upwards [ae_restrict_mem polarCoord.open_target.measurableSet] with p hp
  exact (polar_cutoffKernelK χ p.1 p.2 hp.1).symm

theorem integrable_localPlanarKernel : Integrable localPlanarKernel :=
  integrable_cutoffKernelK contDiff_planarCutoff.continuous hasCompactSupport_planarCutoff

lemma hasCompactSupport_localPlanarKernel : HasCompactSupport localPlanarKernel :=
  HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0 : R2) 1)
    support_localPlanarKernel_subset

lemma contDiffAt_kernelK_infty {x : R2} (hx : x ≠ 0) : ContDiffAt ℝ ∞ kernelK x := by
  have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hn : ContDiffAt ℝ ∞ (fun y : R2 => 2 * Real.pi * ‖y‖ ^ 2) x :=
    contDiffAt_const.mul (contDiff_norm_sq ℝ).contDiffAt
  exact (hn.inv (by positivity)).smul perpJL.contDiff.contDiffAt

lemma contDiffAt_cutoffKernelK {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ)
    {x : R2} (hx : x ≠ 0) : ContDiffAt ℝ ∞ (cutoffKernelK χ) x := by
  have hc : ContDiff ℝ ∞ (radialKernelCutoff χ) := hχ.comp (contDiff_norm_sq ℝ)
  exact hc.contDiffAt.smul (contDiffAt_kernelK_infty hx)

lemma contDiffAt_localPlanarKernel {x : R2} (hx : x ≠ 0) :
    ContDiffAt ℝ ∞ localPlanarKernel x := contDiffAt_cutoffKernelK contDiff_planarCutoff hx

end Euler2D

end
