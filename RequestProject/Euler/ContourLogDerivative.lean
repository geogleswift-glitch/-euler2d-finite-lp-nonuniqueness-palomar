module

public import RequestProject.Euler.ContourLogRatio

/-! True real derivatives of the actual logarithmic kernel off its pole.
The local logarithm is taken after normalizing the chord to one, so no
global branch condition is imposed on the original chord. -/

@[expose] public section

noncomputable section

open Complex Set Filter Topology

namespace Euler2D

theorem hasDerivAt_log_norm_complex {f : ℝ → ℂ} {df : ℂ} {x : ℝ}
    (hf : HasDerivAt f df x) (hf0 : f x ≠ 0) :
    HasDerivAt (fun t => Real.log ‖f t‖) (df / f x).re x := by
  have hmul := hf.mul_const (f x)⁻¹
  have hslit : f x * (f x)⁻¹ ∈ Complex.slitPlane := by
    rw [mul_inv_cancel₀ hf0]
    exact Complex.mem_slitPlane_iff.mpr (Or.inl (by norm_num))
  have hlog := hmul.clog_real hslit
  have hre := Complex.reCLM.hasFDerivAt.comp_hasDerivAt x hlog
  have hreal : HasDerivAt (fun t => (Complex.log (f t * (f x)⁻¹)).re)
      (df / f x).re x := by
    simpa only [Function.comp_def, Complex.reCLM_apply, mul_inv_cancel₀ hf0,
      div_one, div_eq_mul_inv, inv_one, mul_one] using hre
  apply (hreal.add_const (Real.log ‖f x‖)).congr_of_eventuallyEq
  have hne : ∀ᶠ t in 𝓝 x, f t ≠ 0 := hf.continuousAt.eventually_ne hf0
  filter_upwards [hne] with t ht
  rw [Complex.log_re, norm_mul, norm_inv,
    Real.log_mul (norm_ne_zero_iff.mpr ht) (inv_ne_zero (norm_ne_zero_iff.mpr hf0)),
    Real.log_inv]
  ring

theorem hasDerivAt_log_contourChord_left {z : ℝ → ℂ} {dz : ℂ} {θ φ : ℝ}
    (hz : HasDerivAt z dz θ) (hchord : z θ - z φ ≠ 0) :
    HasDerivAt (fun t => Real.log ‖z t - z φ‖) (dz / (z θ - z φ)).re θ := by
  have hh : HasDerivAt (fun t => z t - z φ) dz θ := by
    simpa only [sub_zero] using hz.sub_const (z φ)
  exact hasDerivAt_log_norm_complex hh hchord

theorem hasDerivAt_log_contourChord_right {z : ℝ → ℂ} {dz : ℂ} {θ φ : ℝ}
    (hz : HasDerivAt z dz φ) (hchord : z θ - z φ ≠ 0) :
    HasDerivAt (fun t => Real.log ‖z θ - z t‖) (-dz / (z θ - z φ)).re φ := by
  have hh : HasDerivAt (fun t => z θ - z t) (-dz) φ := by
    simpa only [Pi.sub_def, zero_sub] using (hasDerivAt_const φ (z θ)).sub hz
  exact hasDerivAt_log_norm_complex hh hchord

end Euler2D

end
