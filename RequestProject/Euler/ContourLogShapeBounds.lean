module

public import RequestProject.Euler.ContourLogBoundary

/-! Actual shape estimates for the logarithmic kernel. A common chord
bound cancels the parameter singularity in a difference of logarithms. -/

@[expose] public section

noncomputable section

open Set Filter Topology MeasureTheory

namespace Euler2D

theorem abs_contourLogIntegrand_sub_le {z w : ℝ → ℂ} {ε c θ τ : ℝ}
    (hc : 0 < c) (hε : 0 ≤ ε) (hp : ContDiff ℝ 1 (fun t => z t - w t))
    (hd : ∀ t, ‖deriv (fun s => z s - w s) t‖ ≤ ε)
    (hZ : c * |τ| ≤ ‖z θ - z (θ + τ)‖)
    (hW : c * |τ| ≤ ‖w θ - w (θ + τ)‖) :
    |contourLogIntegrand z θ τ - contourLogIntegrand w θ τ| ≤ ε / c := by
  by_cases ht : τ = 0
  · subst τ
    simp only [contourLogIntegrand, add_zero, sub_self, norm_zero, Real.log_zero, abs_zero]
    exact div_nonneg hε hc.le
  have htpos : 0 < |τ| := abs_pos.mpr ht
  have hb := norm_sub_le_of_contDiff_deriv_bound hp hε hd θ (θ + τ)
  have hgap : |θ - (θ + τ)| = |τ| := by rw [show θ - (θ + τ) = -τ by ring, abs_neg]
  rw [hgap] at hb
  have he : (z θ - z (θ + τ)) - (w θ - w (θ + τ)) =
      (z θ - w θ) - (z (θ + τ) - w (θ + τ)) := by abel
  have hnorm : |‖z θ - z (θ + τ)‖ - ‖w θ - w (θ + τ)‖| ≤ ε * |τ| :=
    (abs_norm_sub_norm_le _ _).trans (by simpa only [he] using hb)
  calc
    _ ≤ |‖z θ - z (θ + τ)‖ - ‖w θ - w (θ + τ)‖| / (c * |τ|) :=
      abs_log_sub_log_le_of_lower (mul_pos hc htpos) hZ hW
    _ ≤ (ε * |τ|) / (c * |τ|) := div_le_div_of_nonneg_right hnorm (mul_nonneg hc.le htpos.le)
    _ = _ := by field_simp

theorem norm_contourSelfIntegrand_sub_le {z dz w dw : ℝ → ℂ} {ε c M D θ τ : ℝ}
    (hc : 0 < c) (hε : 0 ≤ ε) (hD : 0 ≤ D)
    (hp : ContDiff ℝ 1 (fun t => z t - w t))
    (hd : ∀ t, ‖deriv (fun s => z s - w s) t‖ ≤ ε)
    (hM : ∀ t, ‖z t‖ ≤ M)
    (hdiff : ∀ t, ‖dz t - dw t‖ ≤ ε) (hdw : ∀ t, ‖dw t‖ ≤ D)
    (hZ : ∀ θ τ : ℝ, |τ| ≤ Real.pi → c * |τ| ≤ ‖z θ - z (θ + τ)‖)
    (hW : ∀ θ τ : ℝ, |τ| ≤ Real.pi → c * |τ| ≤ ‖w θ - w (θ + τ)‖)
    (hτ : |τ| ≤ Real.pi) :
    ‖contourSelfIntegrand z dz θ τ - contourSelfIntegrand w dw θ τ‖ ≤
      ε * (contourLogMajorant c M τ + D / c) := by
  have hlog := abs_contourLogIntegrand_sub_le hc hε hp hd (hZ θ τ hτ) (hW θ τ hτ)
  have hlogz := contourLogIntegrand_abs_le hc hM hZ θ τ hτ
  have he : contourSelfIntegrand z dz θ τ - contourSelfIntegrand w dw θ τ =
      contourLogIntegrand z θ τ • (dz (θ + τ) - dw (θ + τ)) +
        (contourLogIntegrand z θ τ - contourLogIntegrand w θ τ) • dw (θ + τ) := by
    simp only [contourSelfIntegrand, smul_sub, sub_smul]
    abel
  rw [he]
  calc
    _ ≤ ‖contourLogIntegrand z θ τ • (dz (θ + τ) - dw (θ + τ))‖ +
        ‖(contourLogIntegrand z θ τ - contourLogIntegrand w θ τ) • dw (θ + τ)‖ := norm_add_le _ _
    _ = |contourLogIntegrand z θ τ| * ‖dz (θ + τ) - dw (θ + τ)‖ +
        |contourLogIntegrand z θ τ - contourLogIntegrand w θ τ| * ‖dw (θ + τ)‖ := by
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
    _ ≤ contourLogMajorant c M τ * ε + (ε / c) * D :=
      add_le_add (mul_le_mul hlogz (hdiff _) (norm_nonneg _) (contourLogMajorant_nonneg _ _ _))
        (mul_le_mul hlog (hdw _) (norm_nonneg _) (div_nonneg hε hc.le))
    _ = _ := by ring

end Euler2D

end
