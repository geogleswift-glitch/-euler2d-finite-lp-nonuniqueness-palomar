module

public import RequestProject.Euler.AreaChart

/-!
# Genuine integrability of the logarithmic self-contour kernel

The relative parameter keeps the singularity at zero. A true chord lower
bound compares its logarithm with the integrable scalar logarithm, before
the actual contour integral is used.
-/

@[expose] public section

noncomputable section

open MeasureTheory Complex Set Filter Topology

namespace Euler2D

def contourLogIntegrand (z : ℝ → ℂ) (θ τ : ℝ) : ℝ :=
  Real.log ‖z θ - z (θ + τ)‖

def contourLogMajorant (c M τ : ℝ) : ℝ :=
  |Real.log c| + |Real.log (2 * M + 1)| + |Real.log τ|

def contourSelfIntegrand (z dz : ℝ → ℂ) (θ τ : ℝ) : ℂ :=
  contourLogIntegrand z θ τ • dz (θ + τ)

def contourSelfIntegral (z dz : ℝ → ℂ) (θ : ℝ) : ℂ :=
  ∫ τ in (-Real.pi : ℝ)..Real.pi, contourSelfIntegrand z dz θ τ

lemma contourLogMajorant_nonneg (c M τ : ℝ) : 0 ≤ contourLogMajorant c M τ := by
  unfold contourLogMajorant
  positivity

lemma abs_log_le_of_mul_lower {c u v C : ℝ} (hc : 0 < c) (hu : 0 < u)
    (hlower : c * u ≤ v) (hupper : v ≤ C) :
    |Real.log v| ≤ |Real.log c| + |Real.log u| + |Real.log C| := by
  have hv : 0 < v := (mul_pos hc hu).trans_le hlower
  have hl : Real.log c + Real.log u ≤ Real.log v := by
    rw [← Real.log_mul hc.ne' hu.ne']
    exact Real.log_le_log (mul_pos hc hu) hlower
  have hh : Real.log v ≤ Real.log C := Real.log_le_log hv hupper
  apply abs_le.mpr
  constructor <;> linarith [neg_abs_le (Real.log c), neg_abs_le (Real.log u),
    le_abs_self (Real.log C), abs_nonneg (Real.log c), abs_nonneg (Real.log u),
    abs_nonneg (Real.log C)]

lemma contourLogIntegrand_abs_le {z : ℝ → ℂ} {c M : ℝ}
    (hc : 0 < c) (hM : ∀ t, ‖z t‖ ≤ M)
    (hca : ∀ θ τ : ℝ, |τ| ≤ Real.pi → c * |τ| ≤ ‖z θ - z (θ + τ)‖)
    (θ τ : ℝ) (hτ : |τ| ≤ Real.pi) :
    |contourLogIntegrand z θ τ| ≤ contourLogMajorant c M τ := by
  by_cases hzero : τ = 0
  · subst τ
    simpa only [contourLogIntegrand, add_zero, sub_self, norm_zero, Real.log_zero, abs_zero]
      using contourLogMajorant_nonneg c M 0
  have hupper : ‖z θ - z (θ + τ)‖ ≤ 2 * M + 1 := by
    have hn := norm_sub_le (z θ) (z (θ + τ))
    linarith [hM θ, hM (θ + τ)]
  have hb := abs_log_le_of_mul_lower hc (abs_pos.mpr hzero) (hca θ τ hτ) hupper
  rw [Real.log_abs] at hb
  change |Real.log ‖z θ - z (θ + τ)‖| ≤
    |Real.log c| + |Real.log (2 * M + 1)| + |Real.log τ|
  linarith

lemma intervalIntegrable_contourLogMajorant (c M : ℝ) :
    IntervalIntegrable (contourLogMajorant c M) volume (-Real.pi) Real.pi := by
  unfold contourLogMajorant
  have hlog : IntervalIntegrable (fun τ : ℝ => |Real.log τ|) volume
      (-Real.pi) Real.pi := (intervalIntegral.intervalIntegrable_log').abs
  exact (intervalIntegrable_const).add hlog

theorem intervalIntegrable_contourLogIntegrand {z : ℝ → ℂ} {c M : ℝ}
    (hz : Continuous z) (hc : 0 < c) (hM : ∀ t, ‖z t‖ ≤ M)
    (hca : ∀ θ τ : ℝ, |τ| ≤ Real.pi → c * |τ| ≤ ‖z θ - z (θ + τ)‖) (θ : ℝ) :
    IntervalIntegrable (contourLogIntegrand z θ) volume (-Real.pi) Real.pi := by
  have hab : (-Real.pi : ℝ) ≤ Real.pi := by linarith [Real.pi_pos]
  apply (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mpr
  have hd := (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mp
    (intervalIntegrable_contourLogMajorant c M)
  refine hd.mono' ?_ ?_
  · have hn : Continuous (fun τ : ℝ => ‖z θ - z (θ + τ)‖) :=
      (continuous_const.sub (hz.comp (continuous_const.add continuous_id))).norm
    exact (Real.measurable_log.comp hn.measurable).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with τ hτ
    rw [Real.norm_eq_abs]
    exact contourLogIntegrand_abs_le hc hM hca θ τ (abs_le.mpr ⟨hτ.1.le, hτ.2⟩)

lemma norm_contourSelfIntegrand_le {z dz : ℝ → ℂ} {c M D : ℝ}
    (hc : 0 < c) (hM : ∀ t, ‖z t‖ ≤ M) (hD : ∀ t, ‖dz t‖ ≤ D)
    (hca : ∀ θ τ : ℝ, |τ| ≤ Real.pi → c * |τ| ≤ ‖z θ - z (θ + τ)‖)
    (θ τ : ℝ) (hτ : |τ| ≤ Real.pi) :
    ‖contourSelfIntegrand z dz θ τ‖ ≤ D * contourLogMajorant c M τ := by
  rw [contourSelfIntegrand, norm_smul, Real.norm_eq_abs]
  exact (mul_le_mul (contourLogIntegrand_abs_le hc hM hca θ τ hτ) (hD (θ + τ))
    (norm_nonneg _) (contourLogMajorant_nonneg c M τ)).trans_eq (mul_comm _ _)

theorem intervalIntegrable_contourSelfIntegrand {z dz : ℝ → ℂ} {c M D : ℝ}
    (hz : Continuous z) (hdz : Continuous dz) (hc : 0 < c)
    (hM : ∀ t, ‖z t‖ ≤ M) (hD : ∀ t, ‖dz t‖ ≤ D)
    (hca : ∀ θ τ : ℝ, |τ| ≤ Real.pi → c * |τ| ≤ ‖z θ - z (θ + τ)‖) (θ : ℝ) :
    IntervalIntegrable (contourSelfIntegrand z dz θ) volume (-Real.pi) Real.pi := by
  have hab : (-Real.pi : ℝ) ≤ Real.pi := by linarith [Real.pi_pos]
  apply (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mpr
  have hd := (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mp
    ((intervalIntegrable_contourLogMajorant c M).const_mul D)
  refine hd.mono' ?_ ?_
  · have hn : Continuous (fun τ : ℝ => ‖z θ - z (θ + τ)‖) :=
      (continuous_const.sub (hz.comp (continuous_const.add continuous_id))).norm
    exact (Real.measurable_log.comp hn.measurable).aestronglyMeasurable.smul
      (hdz.comp (continuous_const.add continuous_id)).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with τ hτ
    exact norm_contourSelfIntegrand_le hc hM hD hca θ τ (abs_le.mpr ⟨hτ.1.le, hτ.2⟩)

theorem norm_contourSelfIntegral_le {z dz : ℝ → ℂ} {c M D : ℝ}
    (hc : 0 < c) (hM : ∀ t, ‖z t‖ ≤ M) (hD : ∀ t, ‖dz t‖ ≤ D)
    (hca : ∀ θ τ : ℝ, |τ| ≤ Real.pi → c * |τ| ≤ ‖z θ - z (θ + τ)‖) (θ : ℝ) :
    ‖contourSelfIntegral z dz θ‖ ≤
      ∫ τ in (-Real.pi : ℝ)..Real.pi, D * contourLogMajorant c M τ := by
  have hab : (-Real.pi : ℝ) ≤ Real.pi := by linarith [Real.pi_pos]
  rw [contourSelfIntegral, intervalIntegral.integral_of_le hab,
    intervalIntegral.integral_of_le hab]
  apply norm_integral_le_of_norm_le
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mp
      ((intervalIntegrable_contourLogMajorant c M).const_mul D))
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with τ hτ
  exact norm_contourSelfIntegrand_le hc hM hD hca θ τ (abs_le.mpr ⟨hτ.1.le, hτ.2⟩)

end Euler2D

end
