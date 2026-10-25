module

public import RequestProject.Euler.ContourLogFTC
public import RequestProject.Euler.ContourSmoothEmbedding

/-! The genuine Cauchy principal value for an actual periodic curve close
to the reference circle. The proof integrates the true logarithmic chord
ratio on each cutoff component and uses its common two-sided limit. -/

@[expose] public section

noncomputable section

open Set MeasureTheory Filter Topology Complex

namespace Euler2D

theorem integrableOn_contourKernel_of_chord {z dz : ℝ → ℂ} {c r δ : ℝ}
    (hz : Continuous z) (hdz : Continuous dz) (hc : 0 < c) (hδ : 0 < δ)
    (hchord : ∀ θ τ : ℝ, |τ| ≤ r → c * |τ| ≤ ‖z θ - z (θ + τ)‖) (θ : ℝ) :
    IntegrableOn (fun τ => dz (θ + τ) / (z θ - z (θ + τ)))
      (symmetricContourTruncation r δ) := by
  have hcont : ContinuousOn (fun τ => dz (θ + τ) / (z θ - z (θ + τ)))
      (symmetricContourTruncation r δ) := by
    apply ((hdz.comp (continuous_const.add continuous_id)).continuousOn).div
      ((continuous_const.sub (hz.comp (continuous_const.add continuous_id))).continuousOn)
    intro τ hτ
    have hτpos : 0 < |τ| := hδ.trans_le hτ.2
    exact norm_pos_iff.mp ((mul_pos hc hτpos).trans_le
      (hchord θ τ (abs_le.mpr hτ.1)))
  exact hcont.integrableOn_compact (isCompact_symmetricContourTruncation r δ)

theorem nearCircle_chord_lower {z : ℝ → ℂ} {r ε : ℝ}
    (hr : 0 < r) (hε : 0 ≤ ε)
    (hp : ContDiff ℝ 1 (fun t => z t - refCircle r t))
    (hd : ∀ t, ‖deriv (fun s => z s - refCircle r s) t‖ ≤ ε) :
    ∀ θ τ : ℝ, |τ| ≤ Real.pi →
      (2 * r / Real.pi - ε) * |τ| ≤ ‖z θ - z (θ + τ)‖ := by
  intro θ τ hτ
  have he : θ - (θ + τ) = -τ := by ring
  have hb := contour_lift_chordArc_lower z hr.le hε hp hd
    (show |θ - (θ + τ)| ≤ Real.pi by simpa only [he, abs_neg] using hτ)
  simpa only [he, abs_neg] using hb

theorem integral_nearCircleKernelDifference {z : ℝ → ℂ} {r ε δ θ : ℝ}
    (hr : 0 < r) (hε : 0 ≤ ε) (hsmall : ε < 2 * r / Real.pi)
    (hz : ContDiff ℝ 1 z) (hp : ContDiff ℝ 1 (fun t => z t - refCircle r t))
    (hd : ∀ t, ‖deriv (fun s => z s - refCircle r s) t‖ ≤ ε)
    (hδ : 0 < δ) (hδπ : δ ≤ Real.pi) :
    contourCauchyTruncated (refCircle r) (deriv (refCircle r)) θ Real.pi δ -
        contourCauchyTruncated z (deriv z) θ Real.pi δ =
      Complex.log (contourChordRatio z r θ (θ + -δ)) -
        Complex.log (contourChordRatio z r θ (θ + -Real.pi)) +
          (Complex.log (contourChordRatio z r θ (θ + Real.pi)) -
            Complex.log (contourChordRatio z r θ (θ + δ))) := by
  have hi₁ := integrableOn_contourKernel_of_chord (continuous_refCircle_actual r)
    (continuous_deriv_refCircle_actual r) (by positivity : 0 < 2 * r / Real.pi) hδ
    (fun θ τ hτ => refCircle_short_chord hr.le θ hτ) θ
  have hi₂ := integrableOn_contourKernel_of_chord hz.continuous hz.continuous_deriv_one
    (sub_pos.mpr hsmall) hδ (nearCircle_chord_lower hr hε hp hd) θ
  have hFTC := integral_symmetricContourTruncation_of_hasDerivAt
    (F := fun t => Complex.log (contourChordRatio z r θ (θ + t)))
    hδ hδπ (hi₁.sub hi₂) (fun τ hτ =>
      hasDerivAt_nearCircleLog hr hε hsmall hz hp hd (abs_le.mpr hτ.1)
        (by intro he; have hb : δ ≤ |τ| := hτ.2; rw [he, abs_zero] at hb; linarith))
  change (∫ τ in symmetricContourTruncation Real.pi δ,
    deriv (refCircle r) (θ + τ) / (refCircle r θ - refCircle r (θ + τ))) -
    (∫ τ in symmetricContourTruncation Real.pi δ,
    deriv z (θ + τ) / (z θ - z (θ + τ))) = _
  rw [← integral_sub hi₁ hi₂]
  exact hFTC

theorem log_contourChordRatio_endpoints {z : ℝ → ℂ} {r θ : ℝ}
    (hper : Function.Periodic z (2 * Real.pi)) :
    Complex.log (contourChordRatio z r θ (θ + Real.pi)) =
      Complex.log (contourChordRatio z r θ (θ + -Real.pi)) := by
  have he : θ + -Real.pi + 2 * Real.pi = θ + Real.pi := by ring
  have hz := hper (θ + -Real.pi)
  have hr := periodic_refCircle r (θ + -Real.pi)
  rw [he] at hz hr
  unfold contourChordRatio
  rw [hz, hr]

theorem tendsto_nearCircleKernelDifference {z : ℝ → ℂ} {r ε θ : ℝ}
    (hr : 0 < r) (hε : 0 ≤ ε) (hsmall : ε < 2 * r / Real.pi)
    (hz : ContDiff ℝ 1 z) (hp : ContDiff ℝ 1 (fun t => z t - refCircle r t))
    (hd : ∀ t, ‖deriv (fun s => z s - refCircle r s) t‖ ≤ ε)
    (hper : Function.Periodic z (2 * Real.pi)) :
    Tendsto (fun δ =>
      contourCauchyTruncated (refCircle r) (deriv (refCircle r)) θ Real.pi δ -
        contourCauchyTruncated z (deriv z) θ Real.pi δ)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  let F : ℝ → ℂ := fun t => Complex.log (contourChordRatio z r θ (θ + t))
  have hL : Tendsto F (𝓝[≠] 0)
      (𝓝 (Complex.log (deriv z θ / deriv (refCircle r) θ))) :=
    tendsto_log_contourChordRatio_zero hr hε hsmall hp hd
      (hz.differentiable one_ne_zero θ).hasDerivAt
  have hpos : ∀ᶠ δ : ℝ in 𝓝[>] (0 : ℝ), 0 < δ := self_mem_nhdsWithin
  have hid : Tendsto (fun δ : ℝ => δ) (𝓝[>] (0 : ℝ)) (𝓝[≠] 0) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      nhdsWithin_le_nhds (hpos.mono fun _ h => ne_of_gt h)
  have hn : Tendsto (fun δ : ℝ => -δ) (𝓝[>] (0 : ℝ)) (𝓝[≠] 0) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      (by simpa only [neg_zero] using (show Tendsto (fun δ : ℝ => δ)
        (𝓝[>] (0 : ℝ)) (𝓝 0) from nhdsWithin_le_nhds).neg)
      (hpos.mono fun _ h => neg_ne_zero.mpr (ne_of_gt h))
  have hlim := ((hL.comp hn).sub (tendsto_const_nhds (x := F (-Real.pi)))).add
    ((tendsto_const_nhds (x := F Real.pi)).sub (hL.comp hid))
  have hend : F Real.pi = F (-Real.pi) := log_contourChordRatio_endpoints hper
  have he0 : Complex.log (deriv z θ / deriv (refCircle r) θ) - F (-Real.pi) +
      (F Real.pi - Complex.log (deriv z θ / deriv (refCircle r) θ)) = 0 := by rw [hend]; ring
  rw [he0] at hlim
  apply hlim.congr'
  have hlt : ∀ᶠ δ : ℝ in 𝓝[>] (0 : ℝ), δ < Real.pi :=
    Filter.Eventually.filter_mono nhdsWithin_le_nhds (eventually_lt_nhds Real.pi_pos)
  filter_upwards [hpos, hlt] with δ hδ hδπ
  exact (integral_nearCircleKernelDifference hr hε hsmall hz hp hd hδ hδπ.le).symm

theorem tendsto_nearCircleCauchyTruncated {z : ℝ → ℂ} {r ε θ : ℝ}
    (hr : 0 < r) (hε : 0 ≤ ε) (hsmall : ε < 2 * r / Real.pi)
    (hz : ContDiff ℝ 1 z) (hp : ContDiff ℝ 1 (fun t => z t - refCircle r t))
    (hd : ∀ t, ‖deriv (fun s => z s - refCircle r s) t‖ ≤ ε)
    (hper : Function.Periodic z (2 * Real.pi)) :
    Tendsto (contourCauchyTruncated z (deriv z) θ Real.pi) (𝓝[>] (0 : ℝ))
      (𝓝 (-Complex.I * (Real.pi : ℂ))) := by
  have h := (tendsto_referenceCauchyTruncated hr θ).sub
    (tendsto_nearCircleKernelDifference (θ := θ) hr hε hsmall hz hp hd hper)
  simpa only [sub_sub_cancel, sub_zero] using h

end Euler2D

end
