module

public import RequestProject.Euler.ContourLogRatio

/-!
# The actual two-sided limit of the near-circle chord logarithm

The limit follows from genuine derivatives. The uniform chord-ratio
bound keeps the limiting ratio in the slit plane as well, so the same
complex logarithm has one limit from both sides of the pole.
-/

@[expose] public section

noncomputable section

open Complex Set Filter Topology

namespace Euler2D

theorem tendsto_chordRatio_of_hasDerivAt {z g : ℝ → ℂ} {θ : ℝ} {dz dg : ℂ}
    (hz : HasDerivAt z dz θ) (hg : HasDerivAt g dg θ) (hdg : dg ≠ 0) :
    Tendsto (fun τ : ℝ => (z θ - z (θ + τ)) / (g θ - g (θ + τ)))
      (𝓝[≠] 0) (𝓝 (dz / dg)) := by
  have hq := hz.tendsto_slope_zero.div hg.tendsto_slope_zero hdg
  apply hq.congr'
  filter_upwards [self_mem_nhdsWithin] with τ hτ
  have ht : τ ≠ 0 := hτ
  have htc : ((τ⁻¹ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast inv_ne_zero ht
  change (τ⁻¹ • (z (θ + τ) - z θ)) / (τ⁻¹ • (g (θ + τ) - g θ)) = _
  rw [Complex.real_smul, Complex.real_smul, mul_div_mul_left _ _ htc,
    ← neg_sub (z θ) (z (θ + τ)), ← neg_sub (g θ) (g (θ + τ))]
  exact neg_div_neg_eq _ _

lemma deriv_refCircle_ne_zero {r : ℝ} (hr : 0 < r) (θ : ℝ) :
    deriv (refCircle r) θ ≠ 0 := by
  rw [deriv_refCircle]
  exact mul_ne_zero (by exact_mod_cast hr.ne') (mul_ne_zero Complex.I_ne_zero (Complex.exp_ne_zero _))

theorem tendsto_contourChordRatio_zero {z : ℝ → ℂ} {r θ : ℝ} {dz : ℂ}
    (hr : 0 < r) (hz : HasDerivAt z dz θ) :
    Tendsto (fun τ : ℝ => contourChordRatio z r θ (θ + τ)) (𝓝[≠] 0)
      (𝓝 (dz / deriv (refCircle r) θ)) :=
  tendsto_chordRatio_of_hasDerivAt hz
    (hasDerivAt_refCircle r θ).differentiableAt.hasDerivAt (deriv_refCircle_ne_zero hr θ)

theorem contourChordRatio_derivative_mem_slitPlane {z : ℝ → ℂ} {r ε θ : ℝ} {dz : ℂ}
    (hr : 0 < r) (hε : 0 ≤ ε) (hsmall : ε < 2 * r / Real.pi)
    (hp : ContDiff ℝ 1 (fun t => z t - refCircle r t))
    (hd : ∀ t, ‖deriv (fun s => z s - refCircle r s) t‖ ≤ ε)
    (hz : HasDerivAt z dz θ) :
    dz / deriv (refCircle r) θ ∈ Complex.slitPlane := by
  have hq := tendsto_contourChordRatio_zero hr hz
  have hnb : Ioo (-Real.pi) Real.pi ∈ 𝓝 (0 : ℝ) :=
    Ioo_mem_nhds (by linarith [Real.pi_pos]) Real.pi_pos
  have hbound : ∀ᶠ τ : ℝ in 𝓝[≠] 0,
      contourChordRatio z r θ (θ + τ) ∈ Metric.closedBall 1 (ε / (2 * r / Real.pi)) := by
    filter_upwards [self_mem_nhdsWithin, Filter.Eventually.filter_mono nhdsWithin_le_nhds hnb] with τ hτ hI
    have ht : τ ≠ 0 := hτ
    have hangle : |θ - (θ + τ)| ≤ Real.pi := by
      have he : θ - (θ + τ) = -τ := by ring
      rw [he, abs_neg]
      exact abs_le.mpr ⟨hI.1.le, hI.2.le⟩
    have hne : θ ≠ θ + τ := by
      intro he
      exact ht (by linarith)
    have hb := norm_contourChordRatio_sub_one hr hε hp hd hangle hne
    simpa only [Metric.mem_closedBall, dist_eq_norm] using hb
  have hmem := Metric.isClosed_closedBall.mem_of_tendsto hq hbound
  have hb : ‖dz / deriv (refCircle r) θ - 1‖ ≤ ε / (2 * r / Real.pi) := by
    simpa only [Metric.mem_closedBall, dist_eq_norm] using hmem
  have hh : ‖dz / deriv (refCircle r) θ - 1‖ < 1 :=
    hb.trans_lt ((div_lt_one (by positivity : 0 < 2 * r / Real.pi)).mpr hsmall)
  have hs := Complex.mem_slitPlane_of_norm_lt_one hh
  have he : 1 + (dz / deriv (refCircle r) θ - 1) = dz / deriv (refCircle r) θ := by ring
  simpa only [he] using hs

theorem tendsto_log_contourChordRatio_zero {z : ℝ → ℂ} {r ε θ : ℝ} {dz : ℂ}
    (hr : 0 < r) (hε : 0 ≤ ε) (hsmall : ε < 2 * r / Real.pi)
    (hp : ContDiff ℝ 1 (fun t => z t - refCircle r t))
    (hd : ∀ t, ‖deriv (fun s => z s - refCircle r s) t‖ ≤ ε)
    (hz : HasDerivAt z dz θ) :
    Tendsto (fun τ : ℝ => Complex.log (contourChordRatio z r θ (θ + τ))) (𝓝[≠] 0)
      (𝓝 (Complex.log (dz / deriv (refCircle r) θ))) :=
  (tendsto_contourChordRatio_zero hr hz).clog
    (contourChordRatio_derivative_mem_slitPlane hr hε hsmall hp hd hz)

end Euler2D

end
