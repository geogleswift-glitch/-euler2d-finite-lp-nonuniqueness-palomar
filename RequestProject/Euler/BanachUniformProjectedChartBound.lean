module

public import RequestProject.Euler.BanachUniformLinearBoundOfQuadratic

/-! A common linear displacement estimate transports a local chart
and its fixed projection into one common small neighborhood. -/

@[expose] public section

noncomputable section

open Set Filter Topology Metric

namespace Euler2D

variable {E B : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup B] [NormedSpace ℝ B]

theorem exists_uniform_projected_chart_bound
    {Φ : E → B} {c : B} (hΦ : ContinuousAt Φ 0) (hΦ0 : Φ 0 = c)
    (Q : B →L[ℝ] E) {r K δ Cf R d : ℝ}
    (hr : 0 < r) (hK : 0 < K) (hδ : 0 < δ) (hCf : 0 < Cf) (hR : 0 < R) (hd : 0 < d)
    (hchart : ∀ v : E, ‖v‖ ≤ r → ‖Φ v - c‖ ≤ K * ‖v‖)
    {ι : Type*} (Y : ι → B → B)
    (hflow : ∀ i W, ‖W - c‖ ≤ δ → ‖Y i W - c‖ ≤ Cf * ‖W - c‖) :
    ∃ η > 0, ∃ C > 0, ∀ v : E, ‖v‖ < η →
      Φ v ∈ ball c R ∧ ‖v‖ < r ∧ ∀ i,
        Y i (Φ v) ∈ ball c d ∧ ‖Q (Y i (Φ v) - c)‖ ≤ C * ‖v‖ := by
  let s := min R (min δ (d / (Cf + 1)))
  have hs : 0 < s := lt_min hR (lt_min hδ (div_pos hd (by positivity)))
  have hnear : ∀ᶠ v in 𝓝 (0 : E), Φ v ∈ ball c s :=
    hΦ.eventually (by rw [hΦ0]; exact isOpen_ball.mem_nhds (mem_ball_self hs))
  have hnorm : ∀ᶠ v in 𝓝 (0 : E), ‖v‖ < r :=
    (continuous_norm.tendsto _).eventually (eventually_lt_nhds (by simpa only [norm_zero] using hr))
  obtain ⟨η, hη, hspec⟩ := Metric.eventually_nhds_iff.mp (hnear.and hnorm)
  refine ⟨η, hη, (‖Q‖ + 1) * Cf * K, by positivity, ?_⟩
  intro v hv
  obtain ⟨hvs, hvr⟩ := hspec (by simpa only [dist_zero_right] using hv)
  have hvnorm : ‖Φ v - c‖ < s := by simpa only [mem_ball, dist_eq_norm] using hvs
  have hvR : Φ v ∈ ball c R := ball_subset_ball (min_le_left _ _) hvs
  have hvδ : ‖Φ v - c‖ ≤ δ := hvnorm.le.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hvsmall : ‖Φ v - c‖ < d / (Cf + 1) :=
    hvnorm.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  refine ⟨hvR, hvr, ?_⟩
  intro i
  have hYbound := hflow i (Φ v) hvδ
  have hYsmall : ‖Y i (Φ v) - c‖ < d := by
    have hh := (lt_div_iff₀ (by positivity : 0 < Cf + 1)).mp hvsmall
    nlinarith [norm_nonneg (Φ v - c)]
  refine ⟨by simpa only [mem_ball, dist_eq_norm] using hYsmall, ?_⟩
  calc
    _ ≤ ‖Q‖ * ‖Y i (Φ v) - c‖ := Q.le_opNorm _
    _ ≤ ‖Q‖ * (Cf * ‖Φ v - c‖) := mul_le_mul_of_nonneg_left hYbound (norm_nonneg Q)
    _ ≤ ‖Q‖ * (Cf * (K * ‖v‖)) := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left (hchart v hvr.le) hCf.le) (norm_nonneg Q)
    _ ≤ _ := by nlinarith [mul_nonneg hCf.le (mul_nonneg hK.le (norm_nonneg v))]

end Euler2D

end
