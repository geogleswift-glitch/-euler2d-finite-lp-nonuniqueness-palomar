module

public import RequestProject.Euler.ContourLogBoundaryRegularization

/-! Boundary regularization at every target point. Off the curve,
compactness supplies a genuine positive distance; on the curve, the
already proved logarithmic self-interaction majorant supplies DCT. -/

@[expose] public section

noncomputable section

open Complex Set Filter Topology MeasureTheory intervalIntegral

namespace Euler2D

theorem tendsto_contourRegularizedLogBoundaryIntegral_of_separated
    {z dz : ℝ → ℂ} {x : ℂ} {ρ M D : ℝ}
    (hzc : Continuous z) (hdzc : Continuous dz) (hρ : 0 < ρ)
    (hM : ∀ t, ‖z t‖ ≤ M) (hD : ∀ t, ‖dz t‖ ≤ D)
    (hsep : ∀ φ ∈ Icc (0 : ℝ) (2 * Real.pi), ρ ≤ ‖x - z φ‖) :
    Tendsto (fun δ : ℝ => contourRegularizedLogBoundaryIntegral z dz δ x) (𝓝 0)
      (𝓝 (contourLogBoundaryIntegral z dz x)) := by
  let M' : ℝ := (‖x‖ + M) / 2
  let C : ℝ := |Real.log ρ| + |Real.log (2 * M' + 1)|
  have hM0 : 0 ≤ M := (norm_nonneg (z 0)).trans (hM 0)
  have hM' : 0 ≤ M' := by dsimp [M']; positivity
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  have hab : (0 : ℝ) ≤ 2 * Real.pi := by positivity
  have hm (δ : ℝ) : AEStronglyMeasurable (fun φ =>
      ((1 / 2 : ℝ) * Real.log (δ ^ 2 + ‖x - z φ‖ ^ 2)) • dz φ)
      (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))) := by
    have hn : Continuous (fun φ : ℝ => ‖x - z φ‖) := by fun_prop
    exact (((Real.measurable_log.comp
      (measurable_const.add (hn.measurable.pow_const 2))).const_mul (1 / 2 : ℝ)).smul
      hdzc.measurable).aestronglyMeasurable
  have hB : IntegrableOn (fun _ : ℝ => D * C) (Ioc (0 : ℝ) (2 * Real.pi)) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mp intervalIntegral.intervalIntegrable_const
  have hb : ∀ᶠ δ : ℝ in 𝓝 0, ∀ᵐ φ ∂volume.restrict (Ioc (0 : ℝ) (2 * Real.pi)),
      ‖((1 / 2 : ℝ) * Real.log (δ ^ 2 + ‖x - z φ‖ ^ 2)) • dz φ‖ ≤ D * C := by
    filter_upwards [show ∀ᶠ δ : ℝ in 𝓝 0, |δ| ≤ 1 from by
      filter_upwards [Metric.ball_mem_nhds (0 : ℝ) (by norm_num : (0 : ℝ) < 1)] with δ hδ
      have hh : |δ| < 1 := by simpa only [Metric.mem_ball, Real.dist_eq, sub_zero] using hδ
      exact hh.le] with δ hδ
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with φ hφ
    have huv : ‖x - z φ‖ ≤ 2 * M' := (norm_sub_le _ _).trans (by
      dsimp only [M']
      linarith [hM φ])
    have hh := abs_half_log_sq_add_sq_le hδ (norm_nonneg _) hM' hρ
      (show (0 : ℝ) < 1 by norm_num)
      (by simpa only [mul_one] using hsep φ (Ioc_subset_Icc_self hφ)) huv
    have hlog : |(1 / 2 : ℝ) * Real.log (δ ^ 2 + ‖x - z φ‖ ^ 2)| ≤ C := by
      simpa only [Real.log_one, abs_zero, add_zero, C] using hh
    rw [norm_smul, Real.norm_eq_abs]
    exact (mul_le_mul hlog (hD φ) (norm_nonneg _) hC).trans_eq (mul_comm _ _)
  have hlim : ∀ᵐ φ ∂volume.restrict (Ioc (0 : ℝ) (2 * Real.pi)),
      Tendsto (fun δ : ℝ => ((1 / 2 : ℝ) * Real.log (δ ^ 2 + ‖x - z φ‖ ^ 2)) • dz φ)
        (𝓝 0) (𝓝 (Real.log ‖x - z φ‖ • dz φ)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with φ hφ
    have hv : 0 < ‖x - z φ‖ := hρ.trans_le (hsep φ (Ioc_subset_Icc_self hφ))
    have ht : Tendsto (fun δ : ℝ => δ ^ 2 + ‖x - z φ‖ ^ 2) (𝓝 0)
        (𝓝 (‖x - z φ‖ ^ 2)) := by
      simpa using ((tendsto_id : Tendsto (fun δ : ℝ => δ) (𝓝 0) (𝓝 0)).pow 2).add_const
        (‖x - z φ‖ ^ 2)
    have hl := ((Real.continuousAt_log (sq_pos_of_pos hv).ne').tendsto.comp ht).const_mul (1 / 2 : ℝ)
    have hs := hl.smul_const (dz φ)
    simpa only [Real.log_pow, Nat.cast_ofNat,
      show (1 / 2 : ℝ) * (2 * Real.log ‖x - z φ‖) = Real.log ‖x - z φ‖ by ring] using hs
  have hDCT := tendsto_integral_filter_of_dominated_convergence
    (μ := volume.restrict (Ioc (0 : ℝ) (2 * Real.pi)))
    (fun _ => D * C) (Eventually.of_forall hm) hb hB hlim
  simpa only [contourRegularizedLogBoundaryIntegral, contourLogBoundaryIntegral,
    intervalIntegral.integral_of_le hab] using hDCT

theorem tendsto_contourRegularizedLogBoundaryIntegral
    {z dz : ℝ → ℂ} {c M D : ℝ}
    (hzc : Continuous z) (hdzc : Continuous dz) (hc : 0 < c)
    (hM : ∀ t, ‖z t‖ ≤ M) (hD : ∀ t, ‖dz t‖ ≤ D)
    (hca : ∀ θ τ : ℝ, |τ| ≤ Real.pi → c * |τ| ≤ ‖z θ - z (θ + τ)‖)
    (hz : Function.Periodic z (2 * Real.pi))
    (hdz : Function.Periodic dz (2 * Real.pi)) (x : ℂ) :
    Tendsto (fun δ : ℝ => contourRegularizedLogBoundaryIntegral z dz δ x) (𝓝 0)
      (𝓝 (contourLogBoundaryIntegral z dz x)) := by
  by_cases hx : x ∈ Set.range z
  · obtain ⟨θ, rfl⟩ := hx
    exact tendsto_contourRegularizedLogBoundaryIntegral_at_contour
      hzc hdzc hc hM hD hca hz hdz θ
  · have hn : Continuous (fun φ : ℝ => ‖x - z φ‖) := by fun_prop
    obtain ⟨ρ, hρ, hsep⟩ := isCompact_Icc.exists_forall_le' hn.continuousOn
      (a := (0 : ℝ)) (fun φ _ => norm_pos_iff.mpr (sub_ne_zero.mpr (by
        intro he
        exact hx ⟨φ, he.symm⟩)))
    exact tendsto_contourRegularizedLogBoundaryIntegral_of_separated hzc hdzc hρ hM hD hsep

end Euler2D
