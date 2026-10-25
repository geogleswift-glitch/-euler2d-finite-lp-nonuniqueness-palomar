module

public import RequestProject.Euler.ContourLogKernel
public import RequestProject.Euler.ContourBoundaryIntegralCoordinates

/-! Actual dominated convergence of regularized logarithms on the
boundary, including the genuine self-interaction singularity. -/

@[expose] public section

noncomputable section

open Complex Set Filter Topology MeasureTheory intervalIntegral

namespace Euler2D

theorem abs_half_log_sq_add_sq_le {δ v c u M : ℝ}
    (hδ : |δ| ≤ 1) (hv0 : 0 ≤ v) (hM : 0 ≤ M) (hc : 0 < c) (hu : 0 < u)
    (hl : c * u ≤ v) (hv : v ≤ 2 * M) :
    |(1 / 2 : ℝ) * Real.log (δ ^ 2 + v ^ 2)| ≤
      |Real.log c| + |Real.log (2 * M + 1)| + |Real.log u| := by
  have hδsq : δ ^ 2 ≤ 1 := by
    have h := pow_le_pow_left₀ (abs_nonneg δ) hδ 2
    simpa only [sq_abs, one_pow] using h
  have hvl : 0 < v := (mul_pos hc hu).trans_le hl
  have hden : 0 < δ ^ 2 + v ^ 2 := by positivity
  have hlsq := pow_le_pow_left₀ (mul_pos hc hu).le hl 2
  have husq := pow_le_pow_left₀ hv0 hv 2
  have hC : 0 < 2 * M + 1 := by linarith
  have hlow := Real.log_le_log (sq_pos_of_pos (mul_pos hc hu))
    (show (c * u) ^ 2 ≤ δ ^ 2 + v ^ 2 by nlinarith [sq_nonneg δ])
  have hupp := Real.log_le_log hden
    (show δ ^ 2 + v ^ 2 ≤ (2 * M + 1) ^ 2 by nlinarith)
  rw [Real.log_pow, Real.log_mul hc.ne' hu.ne'] at hlow
  rw [Real.log_pow] at hupp
  norm_num at hlow hupp
  apply abs_le.mpr
  constructor <;> nlinarith [neg_abs_le (Real.log c), neg_abs_le (Real.log u),
    le_abs_self (Real.log (2 * M + 1)), abs_nonneg (Real.log c),
    abs_nonneg (Real.log u), abs_nonneg (Real.log (2 * M + 1))]

def contourRegularizedSelfIntegrand (z dz : ℝ → ℂ) (δ θ τ : ℝ) : ℂ :=
  ((1 / 2 : ℝ) * Real.log (δ ^ 2 + ‖z θ - z (θ + τ)‖ ^ 2)) • dz (θ + τ)

def contourRegularizedSelfIntegral (z dz : ℝ → ℂ) (δ θ : ℝ) : ℂ :=
  ∫ τ in (-Real.pi : ℝ)..Real.pi, contourRegularizedSelfIntegrand z dz δ θ τ

theorem norm_contourRegularizedSelfIntegrand_le {z dz : ℝ → ℂ} {c M D δ θ τ : ℝ}
    (hδ : |δ| ≤ 1) (hc : 0 < c) (hM : ∀ t, ‖z t‖ ≤ M) (hD : ∀ t, ‖dz t‖ ≤ D)
    (hca : ∀ θ τ : ℝ, |τ| ≤ Real.pi → c * |τ| ≤ ‖z θ - z (θ + τ)‖)
    (hτ : |τ| ≤ Real.pi) (hτ0 : τ ≠ 0) :
    ‖contourRegularizedSelfIntegrand z dz δ θ τ‖ ≤ D * contourLogMajorant c M τ := by
  have hM0 : 0 ≤ M := (norm_nonneg (z 0)).trans (hM 0)
  have huv : ‖z θ - z (θ + τ)‖ ≤ 2 * M :=
    (norm_sub_le _ _).trans (by linarith [hM θ, hM (θ + τ)])
  have hb := abs_half_log_sq_add_sq_le hδ (norm_nonneg _) hM0 hc (abs_pos.mpr hτ0)
    (hca θ τ hτ) huv
  rw [Real.log_abs] at hb
  rw [contourRegularizedSelfIntegrand, norm_smul, Real.norm_eq_abs]
  exact (mul_le_mul hb (hD (θ + τ)) (norm_nonneg _)
    (contourLogMajorant_nonneg c M τ)).trans_eq (mul_comm _ _)

theorem tendsto_contourRegularizedSelfIntegral {z dz : ℝ → ℂ} {c M D : ℝ}
    (hzc : Continuous z) (hdzc : Continuous dz) (hc : 0 < c)
    (hM : ∀ t, ‖z t‖ ≤ M) (hD : ∀ t, ‖dz t‖ ≤ D)
    (hca : ∀ θ τ : ℝ, |τ| ≤ Real.pi → c * |τ| ≤ ‖z θ - z (θ + τ)‖) (θ : ℝ) :
    Tendsto (fun δ : ℝ => contourRegularizedSelfIntegral z dz δ θ) (𝓝 0)
      (𝓝 (contourSelfIntegral z dz θ)) := by
  have hab : (-Real.pi : ℝ) ≤ Real.pi := by linarith [Real.pi_pos]
  have hB : IntegrableOn (fun τ => D * contourLogMajorant c M τ) (Ioc (-Real.pi) Real.pi) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mp
      ((intervalIntegrable_contourLogMajorant c M).const_mul D)
  have hm (δ : ℝ) : AEStronglyMeasurable (contourRegularizedSelfIntegrand z dz δ θ)
      (volume.restrict (Ioc (-Real.pi) Real.pi)) := by
    have hn : Continuous (fun τ : ℝ => ‖z θ - z (θ + τ)‖) := by fun_prop
    exact (((Real.measurable_log.comp
      (measurable_const.add (hn.measurable.pow_const 2))).const_mul (1 / 2 : ℝ)).smul
        (hdzc.comp (continuous_const.add continuous_id)).measurable).aestronglyMeasurable
  have hb : ∀ᶠ δ : ℝ in 𝓝 0, ∀ᵐ τ ∂volume.restrict (Ioc (-Real.pi) Real.pi),
      ‖contourRegularizedSelfIntegrand z dz δ θ τ‖ ≤ D * contourLogMajorant c M τ := by
    filter_upwards [show ∀ᶠ δ : ℝ in 𝓝 0, |δ| ≤ 1 from by
      filter_upwards [Metric.ball_mem_nhds (0 : ℝ) (by norm_num : (0 : ℝ) < 1)] with δ hδ
      have hh : |δ| < 1 := by simpa only [Metric.mem_ball, Real.dist_eq, sub_zero] using hδ
      exact hh.le] with δ hδ
    filter_upwards [ae_restrict_mem measurableSet_Ioc, ae_restrict_of_ae (volume.ae_ne (0 : ℝ))]
      with τ hτ hτ0
    exact norm_contourRegularizedSelfIntegrand_le hδ hc hM hD hca
      (abs_le.mpr ⟨hτ.1.le, hτ.2⟩) hτ0
  have hlim : ∀ᵐ τ ∂volume.restrict (Ioc (-Real.pi) Real.pi),
      Tendsto (fun δ : ℝ => contourRegularizedSelfIntegrand z dz δ θ τ) (𝓝 0)
        (𝓝 (contourSelfIntegrand z dz θ τ)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc, ae_restrict_of_ae (volume.ae_ne (0 : ℝ))]
      with τ hτ hτ0
    have hv : 0 < ‖z θ - z (θ + τ)‖ := (mul_pos hc (abs_pos.mpr hτ0)).trans_le
      (hca θ τ (abs_le.mpr ⟨hτ.1.le, hτ.2⟩))
    have ht : Tendsto (fun δ : ℝ => δ ^ 2 + ‖z θ - z (θ + τ)‖ ^ 2) (𝓝 0)
        (𝓝 (‖z θ - z (θ + τ)‖ ^ 2)) := by
      simpa using ((tendsto_id : Tendsto (fun δ : ℝ => δ) (𝓝 0) (𝓝 0)).pow 2).add_const
        (‖z θ - z (θ + τ)‖ ^ 2)
    have hl := ((Real.continuousAt_log (sq_pos_of_pos hv).ne').tendsto.comp ht).const_mul (1 / 2 : ℝ)
    have hs := hl.smul_const (dz (θ + τ))
    simpa only [contourRegularizedSelfIntegrand, contourSelfIntegrand, contourLogIntegrand,
      Function.comp_def, Real.log_pow, Nat.cast_ofNat, show (1 / 2 : ℝ) * (2 * Real.log ‖z θ - z (θ + τ)‖) =
        Real.log ‖z θ - z (θ + τ)‖ by ring] using hs
  have hDCT := tendsto_integral_filter_of_dominated_convergence
    (μ := volume.restrict (Ioc (-Real.pi) Real.pi))
    (fun τ => D * contourLogMajorant c M τ) (Eventually.of_forall hm) hb hB hlim
  simpa only [contourRegularizedSelfIntegral, contourSelfIntegral,
    intervalIntegral.integral_of_le hab] using hDCT

def contourRegularizedLogBoundaryIntegral (z dz : ℝ → ℂ) (δ : ℝ) (x : ℂ) : ℂ :=
  ∫ φ in (0 : ℝ)..2 * Real.pi,
    ((1 / 2 : ℝ) * Real.log (δ ^ 2 + ‖x - z φ‖ ^ 2)) • dz φ

theorem contourRegularizedSelfIntegral_eq_boundaryIntegral (z dz : ℝ → ℂ)
    (hz : Function.Periodic z (2 * Real.pi))
    (hdz : Function.Periodic dz (2 * Real.pi)) (δ θ : ℝ) :
    contourRegularizedSelfIntegral z dz δ θ =
      contourRegularizedLogBoundaryIntegral z dz δ (z θ) := by
  let f : ℝ → ℂ := fun φ =>
    ((1 / 2 : ℝ) * Real.log (δ ^ 2 + ‖z θ - z φ‖ ^ 2)) • dz φ
  have hp : Function.Periodic f (2 * Real.pi) := by
    intro φ
    dsimp only [f]
    rw [hz φ, hdz φ]
  change (∫ τ in (-Real.pi)..Real.pi, f (θ + τ)) = ∫ φ in (0 : ℝ)..2 * Real.pi, f φ
  rw [intervalIntegral.integral_comp_add_left]
  have he := hp.intervalIntegral_add_eq (θ - Real.pi) 0
  convert he using 1 <;> congr 1 <;> ring

theorem tendsto_contourRegularizedLogBoundaryIntegral_at_contour
    {z dz : ℝ → ℂ} {c M D : ℝ}
    (hzc : Continuous z) (hdzc : Continuous dz) (hc : 0 < c)
    (hM : ∀ t, ‖z t‖ ≤ M) (hD : ∀ t, ‖dz t‖ ≤ D)
    (hca : ∀ θ τ : ℝ, |τ| ≤ Real.pi → c * |τ| ≤ ‖z θ - z (θ + τ)‖)
    (hz : Function.Periodic z (2 * Real.pi))
    (hdz : Function.Periodic dz (2 * Real.pi)) (θ : ℝ) :
    Tendsto (fun δ : ℝ => contourRegularizedLogBoundaryIntegral z dz δ (z θ)) (𝓝 0)
      (𝓝 (contourLogBoundaryIntegral z dz (z θ))) := by
  simpa only [contourRegularizedSelfIntegral_eq_boundaryIntegral z dz hz hdz,
    contourSelfIntegral_eq_boundaryIntegral z dz hz hdz] using
    tendsto_contourRegularizedSelfIntegral hzc hdzc hc hM hD hca θ

end Euler2D
