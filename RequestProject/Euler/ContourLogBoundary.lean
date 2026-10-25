module

public import RequestProject.Euler.ContourLogTruncation

/-!
# Genuine cancellation of the logarithmic cutoff boundary

The two opposite chords have almost the same norm, by the actual Hölder
Taylor remainder.  A real logarithm mean-value estimate gives a uniform
bound for their logarithmic difference, without a complex branch choice.
-/

@[expose] public section

noncomputable section

open Set MeasureTheory Filter Topology
open scoped NNReal

namespace Euler2D

theorem abs_log_sub_log_le_of_lower {a b m : ℝ} (hm : 0 < m) (ha : m ≤ a) (hb : m ≤ b) :
    |Real.log a - Real.log b| ≤ |a - b| / m := by
  have hderiv (t : ℝ) (ht : t ∈ uIcc a b) :
      HasDerivWithinAt Real.log t⁻¹ (uIcc a b) t := by
    have htm : m ≤ t := (le_min ha hb).trans ht.1
    exact (Real.hasDerivAt_log (ne_of_gt (hm.trans_le htm))).hasDerivWithinAt
  have hbound (t : ℝ) (ht : t ∈ uIcc a b) : ‖t⁻¹‖ ≤ 1 / m := by
    have htm : m ≤ t := (le_min ha hb).trans ht.1
    rw [norm_inv, Real.norm_eq_abs, abs_of_pos (hm.trans_le htm)]
    simpa only [one_div] using one_div_le_one_div_of_le hm htm
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hderiv hbound
    (convex_uIcc a b) left_mem_uIcc right_mem_uIcc
  calc
    _ = ‖Real.log b - Real.log a‖ := by rw [Real.norm_eq_abs, abs_sub_comm]
    _ ≤ (1 / m) * ‖b - a‖ := h
    _ = _ := by rw [Real.norm_eq_abs, abs_sub_comm]; ring

/-- True opposite curve chords agree in norm to order `δ^(γ+1)`. -/
theorem abs_norm_contour_opposite_chords_sub_le {z dz : ℝ → ℂ} {γ H : ℝ}
    (hγ : 0 ≤ γ) (hH : 0 ≤ H) (hz : ∀ s, HasDerivAt z (dz s) s)
    (hd : ∀ s t, ‖dz s - dz t‖ ≤ H * |s - t| ^ γ)
    (θ : ℝ) {δ : ℝ} (hδ : 0 ≤ δ) :
    |‖z θ - z (θ + -δ)‖ - ‖z θ - z (θ + δ)‖| ≤ 2 * H * δ ^ γ * δ := by
  have hp := norm_holder_derivative_taylor hγ hH hz hd θ δ
  have hm := norm_holder_derivative_taylor hγ hH hz hd θ (-δ)
  simp only [abs_neg, abs_of_nonneg hδ] at hp hm
  have heq : (z θ - z (θ + -δ)) + (z θ - z (θ + δ)) =
      -((z (θ + -δ) - z θ - (-δ) • dz θ) + (z (θ + δ) - z θ - δ • dz θ)) := by
    rw [neg_smul]
    abel_nf
  have hs : ‖(z θ - z (θ + -δ)) + (z θ - z (θ + δ))‖ ≤ 2 * H * δ ^ γ * δ := by
    rw [heq, norm_neg]
    exact (norm_add_le _ _).trans ((add_le_add hm hp).trans_eq (by ring))
  have hn := abs_norm_sub_norm_le (z θ - z (θ + -δ)) (-(z θ - z (θ + δ)))
  rw [norm_neg, sub_neg_eq_add] at hn
  exact hn.trans hs

/-- Uniform genuine logarithmic cancellation of the two opposite chords. -/
theorem abs_contourLogIntegrand_opposite_sub_le {z dz : ℝ → ℂ} {γ H c δ : ℝ}
    (hγ : 0 ≤ γ) (hH : 0 ≤ H) (hc : 0 < c) (hδ : 0 < δ)
    (hz : ∀ s, HasDerivAt z (dz s) s)
    (hd : ∀ s t, ‖dz s - dz t‖ ≤ H * |s - t| ^ γ) (θ : ℝ)
    (hminus : c * δ ≤ ‖z θ - z (θ + -δ)‖)
    (hplus : c * δ ≤ ‖z θ - z (θ + δ)‖) :
    |contourLogIntegrand z θ (-δ) - contourLogIntegrand z θ δ| ≤ (2 * H / c) * δ ^ γ := by
  have h := abs_log_sub_log_le_of_lower (mul_pos hc hδ) hminus hplus
  calc
    _ ≤ |‖z θ - z (θ + -δ)‖ - ‖z θ - z (θ + δ)‖| / (c * δ) := h
    _ ≤ (2 * H * δ ^ γ * δ) / (c * δ) := div_le_div_of_nonneg_right
      (abs_norm_contour_opposite_chords_sub_le hγ hH hz hd θ hδ.le) (mul_nonneg hc.le hδ.le)
    _ = _ := by field_simp

/-- The actual cutoff boundary term in the relative-angle logarithmic integral. -/
def contourSelfCutoffBoundary (z dz : ℝ → ℂ) (δ θ : ℝ) : ℂ :=
  contourSelfIntegrand z dz θ (-δ) - contourSelfIntegrand z dz θ δ

def contourSelfBoundaryMajorant (γ H c M D δ : ℝ) : ℝ :=
  contourLogMajorant c M δ * (H * (2 * δ) ^ γ) + (2 * H / c) * δ ^ γ * D

/-- A true common boundary bound, retaining the cancellation of the two logarithms. -/
theorem norm_contourSelfCutoffBoundary_le {z dz : ℝ → ℂ} {γ H c M D δ : ℝ}
    (hγ : 0 ≤ γ) (hH : 0 ≤ H) (hc : 0 < c) (hδ : 0 < δ) (hsmall : δ ≤ Real.pi)
    (hM : ∀ s, ‖z s‖ ≤ M) (hD : ∀ s, ‖dz s‖ ≤ D)
    (hz : ∀ s, HasDerivAt z (dz s) s)
    (hd : ∀ s t, ‖dz s - dz t‖ ≤ H * |s - t| ^ γ)
    (hchord : ∀ θ τ : ℝ, |τ| ≤ Real.pi → c * |τ| ≤ ‖z θ - z (θ + τ)‖) (θ : ℝ) :
    ‖contourSelfCutoffBoundary z dz δ θ‖ ≤ contourSelfBoundaryMajorant γ H c M D δ := by
  have hminus : c * δ ≤ ‖z θ - z (θ + -δ)‖ := by
    simpa only [abs_neg, abs_of_pos hδ] using
      hchord θ (-δ) (by simpa only [abs_neg, abs_of_pos hδ] using hsmall)
  have hplus : c * δ ≤ ‖z θ - z (θ + δ)‖ := by
    simpa only [abs_of_pos hδ] using hchord θ δ (by simpa only [abs_of_pos hδ] using hsmall)
  have hlogdiff := abs_contourLogIntegrand_opposite_sub_le hγ hH hc hδ hz hd θ hminus hplus
  have hlogminus : |contourLogIntegrand z θ (-δ)| ≤ contourLogMajorant c M δ := by
    have h := contourLogIntegrand_abs_le hc hM hchord θ (-δ)
      (by simpa only [abs_neg, abs_of_pos hδ] using hsmall)
    simpa only [contourLogMajorant, Real.log_neg_eq_log] using h
  have hdz : ‖dz (θ + -δ) - dz (θ + δ)‖ ≤ H * (2 * δ) ^ γ := by
    have h := hd (θ + -δ) (θ + δ)
    have heq : |(θ + -δ) - (θ + δ)| = 2 * δ := by
      rw [show (θ + -δ) - (θ + δ) = -(2 * δ) by ring, abs_neg,
        abs_of_nonneg (by positivity : 0 ≤ 2 * δ)]
    rwa [heq] at h
  have heq : contourSelfCutoffBoundary z dz δ θ =
      contourLogIntegrand z θ (-δ) • (dz (θ + -δ) - dz (θ + δ)) +
        (contourLogIntegrand z θ (-δ) - contourLogIntegrand z θ δ) • dz (θ + δ) := by
    simp only [contourSelfCutoffBoundary, contourSelfIntegrand, smul_sub, sub_smul]
    abel_nf
  rw [heq]
  calc
    _ ≤ |contourLogIntegrand z θ (-δ)| * ‖dz (θ + -δ) - dz (θ + δ)‖ +
        |contourLogIntegrand z θ (-δ) - contourLogIntegrand z θ δ| * ‖dz (θ + δ)‖ := by
      simpa only [norm_smul, Real.norm_eq_abs] using norm_add_le
        (contourLogIntegrand z θ (-δ) • (dz (θ + -δ) - dz (θ + δ)))
        ((contourLogIntegrand z θ (-δ) - contourLogIntegrand z θ δ) • dz (θ + δ))
    _ ≤ _ := by
      unfold contourSelfBoundaryMajorant
      apply add_le_add
      · exact mul_le_mul hlogminus hdz (norm_nonneg _) (contourLogMajorant_nonneg c M δ)
      · exact mul_le_mul hlogdiff (hD _) (norm_nonneg _)
          (mul_nonneg (div_nonneg (mul_nonneg (by norm_num) hH) hc.le)
            (Real.rpow_nonneg hδ.le γ))

/-- The common genuine boundary majorant tends to zero at the actual positive cutoff limit. -/
theorem tendsto_contourSelfBoundaryMajorant {γ : ℝ} (hγ : 0 < γ) (H c M D : ℝ) :
    Tendsto (contourSelfBoundaryMajorant γ H c M D) (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
  have hp : Tendsto (fun δ : ℝ => δ ^ γ) (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
    simpa only [Real.zero_rpow hγ.ne'] using
      ((Real.continuous_rpow_const hγ.le).tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
  have hl : Tendsto (fun δ : ℝ => |Real.log δ| * δ ^ γ)
      (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
    have h := (tendsto_log_mul_rpow_nhdsGT_zero hγ).abs
    simp only [abs_zero] at h
    apply h.congr'
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg hδ.le _)]
  have hbase := (hp.const_mul (|Real.log c| + |Real.log (2 * M + 1)|)).add hl
  have hsum := (hbase.const_mul (H * (2 : ℝ) ^ γ)).add (hp.const_mul ((2 * H / c) * D))
  simp only [mul_zero, zero_add] at hsum
  apply hsum.congr'
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  unfold contourSelfBoundaryMajorant contourLogMajorant
  rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hδ.le]
  ring

/-- Actual logarithmic cutoff boundary cancellation is uniform in every evaluation angle. -/
theorem tendstoUniformly_contourSelfCutoffBoundary {z dz : ℝ → ℂ} {γ H c M D : ℝ}
    (hγ : 0 < γ) (hH : 0 ≤ H) (hc : 0 < c)
    (hM : ∀ s, ‖z s‖ ≤ M) (hD : ∀ s, ‖dz s‖ ≤ D)
    (hz : ∀ s, HasDerivAt z (dz s) s)
    (hd : ∀ s t, ‖dz s - dz t‖ ≤ H * |s - t| ^ γ)
    (hchord : ∀ θ τ : ℝ, |τ| ≤ Real.pi → c * |τ| ≤ ‖z θ - z (θ + τ)‖) :
    TendstoUniformly (contourSelfCutoffBoundary z dz) (fun _ : ℝ => (0 : ℂ))
      (𝓝[>] (0 : ℝ)) := by
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  have hsmall : ∀ᶠ δ : ℝ in 𝓝[>] (0 : ℝ), δ < Real.pi :=
    (eventually_lt_nhds Real.pi_pos).filter_mono nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin, hsmall,
    (tendsto_contourSelfBoundaryMajorant hγ H c M D).eventually (eventually_lt_nhds hε)]
    with δ hδ hδsmall hnear θ
  rw [dist_eq_norm, zero_sub, norm_neg]
  exact (norm_contourSelfCutoffBoundary_le hγ.le hH hc hδ hδsmall.le hM hD hz hd hchord θ).trans_lt hnear

theorem tendstoUniformly_contourSelfCutoffBoundary_filter
    {ι : Type*} {l : Filter ι} {δ : ι → ℝ} {z dz : ℝ → ℂ} {γ H c M D : ℝ}
    (hδ : Tendsto δ l (𝓝 (0 : ℝ))) (hpos : ∀ᶠ i in l, 0 < δ i)
    (hγ : 0 < γ) (hH : 0 ≤ H) (hc : 0 < c)
    (hM : ∀ s, ‖z s‖ ≤ M) (hD : ∀ s, ‖dz s‖ ≤ D)
    (hz : ∀ s, HasDerivAt z (dz s) s)
    (hd : ∀ s t, ‖dz s - dz t‖ ≤ H * |s - t| ^ γ)
    (hchord : ∀ θ τ : ℝ, |τ| ≤ Real.pi → c * |τ| ≤ ‖z θ - z (θ + τ)‖) :
    TendstoUniformly (fun i => contourSelfCutoffBoundary z dz (δ i))
      (fun _ : ℝ => (0 : ℂ)) l := by
  have hu := tendstoUniformly_contourSelfCutoffBoundary hγ hH hc hM hD hz hd hchord
  rw [Metric.tendstoUniformly_iff] at hu ⊢
  intro ε hε
  exact (tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within δ hδ hpos).eventually (hu ε hε)

/-- In particular, every genuine C¹ Hölder contour with a true chord bound has uniform boundary cancellation. -/
theorem tendstoUniformly_contourC1SelfCutoffBoundary {γ : ℝ≥0} (Z : ContourC1Space γ)
    {c : ℝ} (hγ : 0 < (γ : ℝ)) (hc : 0 < c)
    (hchord : ∀ θ τ : ℝ, |τ| ≤ Real.pi → c * |τ| ≤
      ‖ContourC1Space.lift γ Z θ - ContourC1Space.lift γ Z (θ + τ)‖) :
    TendstoUniformly (contourSelfCutoffBoundary (ContourC1Space.lift γ Z)
      (deriv (ContourC1Space.lift γ Z))) (fun _ : ℝ => (0 : ℂ)) (𝓝[>] (0 : ℝ)) :=
  tendstoUniformly_contourSelfCutoffBoundary hγ (norm_nonneg Z) hc
    (fun s => ContourC1Space.norm_eval_le Z (s : ContourCircle))
    (ContourC1Space.norm_deriv_lift_le Z)
    (fun s => (ContourC1Space.hasDerivAt_lift Z s).differentiableAt.hasDerivAt)
    (norm_contourC1_deriv_lift_sub_le Z) hchord

end Euler2D
