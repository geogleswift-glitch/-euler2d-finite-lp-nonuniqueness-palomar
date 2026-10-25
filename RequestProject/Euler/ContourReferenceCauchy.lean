module

public import RequestProject.Euler.ContourCauchyPrincipalValue

/-!
# The genuine Cauchy principal value on a reference circle

The value is calculated by reflecting the actual integrable pole
remainder.  Its values at opposite nonzero parameters add to `-I`.
No Cauchy integral theorem or principal-value identity is assumed.
-/

@[expose] public section

noncomputable section

open Set MeasureTheory Filter Topology Complex
open scoped NNReal

namespace Euler2D

lemma deriv_refCircle_eq_I_mul (d θ : ℝ) :
    deriv (refCircle d) θ = I * refCircle d θ := by
  rw [deriv_refCircle]
  dsimp only [refCircle]
  ring

lemma continuous_refCircle_actual (d : ℝ) : Continuous (refCircle d) :=
  continuous_iff_continuousAt.mpr (fun θ => (hasDerivAt_refCircle d θ).continuousAt)

lemma continuous_deriv_refCircle_actual (d : ℝ) : Continuous (deriv (refCircle d)) := by
  have heq : deriv (refCircle d) = fun θ => I * refCircle d θ :=
    funext (deriv_refCircle_eq_I_mul d)
  rw [heq]
  exact continuous_const.mul (continuous_refCircle_actual d)

lemma norm_deriv_refCircle {d : ℝ} (hd : 0 ≤ d) (θ : ℝ) :
    ‖deriv (refCircle d) θ‖ = d := by
  rw [deriv_refCircle]
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_I,
    norm_exp_ofReal_mul_I, mul_one, abs_of_nonneg hd]

lemma norm_refCircle_sub_le {d : ℝ} (hd : 0 ≤ d) (s t : ℝ) :
    ‖refCircle d s - refCircle d t‖ ≤ d * |s - t| := by
  have hdiff : Differentiable ℝ (refCircle d) :=
    fun θ => (hasDerivAt_refCircle d θ).differentiableAt
  have hbound (θ : ℝ) : ‖deriv (refCircle d) θ‖₊ ≤ NNReal.mk d hd := by
    exact_mod_cast (norm_deriv_refCircle hd θ).le
  simpa only [NNReal.coe_mk, Real.norm_eq_abs] using
    (lipschitzWith_of_nnnorm_deriv_le hdiff hbound).norm_sub_le s t

lemma norm_deriv_refCircle_sub_le {d : ℝ} (hd : 0 ≤ d) (s t : ℝ) :
    ‖deriv (refCircle d) s - deriv (refCircle d) t‖ ≤ d * |s - t| := by
  rw [deriv_refCircle_eq_I_mul, deriv_refCircle_eq_I_mul, ← mul_sub, norm_mul, norm_I, one_mul]
  exact norm_refCircle_sub_le hd s t

lemma refCircle_short_chord {d : ℝ} (hd : 0 ≤ d) (θ : ℝ) {τ : ℝ}
    (hτ : |τ| ≤ Real.pi) :
    (2 * d / Real.pi) * |τ| ≤ ‖refCircle d θ - refCircle d (θ + τ)‖ := by
  have hgap : |θ - (θ + τ)| = |τ| := by
    rw [show θ - (θ + τ) = -τ by ring, abs_neg]
  simpa only [hgap] using
    (refCircle_chord_lower hd (θ := θ) (φ := θ + τ) (by simpa only [hgap] using hτ))

lemma refCircle_sub_shift_ne_zero {d : ℝ} (hd : 0 < d) (θ : ℝ) {τ : ℝ}
    (hτ0 : τ ≠ 0) (hτ : |τ| ≤ Real.pi) :
    refCircle d θ - refCircle d (θ + τ) ≠ 0 := by
  apply norm_pos_iff.mp
  exact (mul_pos (by positivity : 0 < 2 * d / Real.pi) (abs_pos.mpr hτ0)).trans_le
    (refCircle_short_chord hd.le θ hτ)

lemma refCircle_mul_opposite_shifts (d θ τ : ℝ) :
    refCircle d (θ + τ) * refCircle d (θ + -τ) = refCircle d θ * refCircle d θ := by
  dsimp only [refCircle]
  calc
    _ = ((d : ℂ) * d) * (exp (((θ + τ : ℝ) : ℂ) * I) *
        exp (((θ + -τ : ℝ) : ℂ) * I)) := by ring
    _ = ((d : ℂ) * d) * (exp ((θ : ℂ) * I) * exp ((θ : ℂ) * I)) := by
      congr 1
      rw [← exp_add, ← exp_add]
      congr 1
      push_cast
      ring
    _ = _ := by ring

/-- The actual circle Cauchy kernels at opposite parameters add to `-I`. -/
theorem referenceCauchyKernel_opposite_add {d : ℝ} (hd : 0 < d) (θ : ℝ) {τ : ℝ}
    (hτ0 : τ ≠ 0) (hτ : |τ| ≤ Real.pi) :
    deriv (refCircle d) (θ + τ) / (refCircle d θ - refCircle d (θ + τ)) +
      deriv (refCircle d) (θ + -τ) / (refCircle d θ - refCircle d (θ + -τ)) = -I := by
  have hp := refCircle_sub_shift_ne_zero hd θ hτ0 hτ
  have hm := refCircle_sub_shift_ne_zero hd θ (neg_ne_zero.mpr hτ0)
    (by simpa only [abs_neg] using hτ)
  rw [deriv_refCircle_eq_I_mul, deriv_refCircle_eq_I_mul]
  rw [div_add_div _ _ hp hm]
  apply (div_eq_iff (mul_ne_zero hp hm)).mpr
  linear_combination -I * (refCircle_mul_opposite_shifts d θ τ)

/-- The inverse poles also cancel, so the actual remainder has the same reflection identity. -/
theorem referenceCauchyPoleIntegrand_opposite_add {d : ℝ} (hd : 0 < d) (θ : ℝ) {τ : ℝ}
    (hτ0 : τ ≠ 0) (hτ : |τ| ≤ Real.pi) :
    contourCauchyPoleIntegrand (refCircle d) (deriv (refCircle d)) θ τ +
      contourCauchyPoleIntegrand (refCircle d) (deriv (refCircle d)) θ (-τ) = -I := by
  have h := referenceCauchyKernel_opposite_add hd θ hτ0 hτ
  dsimp only [contourCauchyPoleIntegrand]
  rw [Complex.ofReal_neg, inv_neg]
  linear_combination h

/-- The genuine reference remainder is integrable, with the true circle derivative Lipschitz bound. -/
theorem integrableOn_referenceCauchyPoleIntegrand {d : ℝ} (hd : 0 < d) (θ : ℝ) :
    IntegrableOn (contourCauchyPoleIntegrand (refCircle d) (deriv (refCircle d)) θ)
      (Icc (-Real.pi) Real.pi) := by
  apply integrableOn_contourCauchyPoleIntegrand (continuous_refCircle_actual d)
    (continuous_deriv_refCircle_actual d) (γ := 1) (H := d) (c := 2 * d / Real.pi)
    (by norm_num) hd.le (by positivity) Real.pi_pos.le
  · intro s
    exact (hasDerivAt_refCircle d s).differentiableAt.hasDerivAt
  · intro s t
    simpa only [Real.rpow_one] using norm_deriv_refCircle_sub_le hd.le s t
  · intro s τ hτ
    exact refCircle_short_chord hd.le s hτ

private lemma neg_preimage_centered_Icc (r : ℝ) :
    (fun τ : ℝ => -τ) ⁻¹' Icc (-r) r = Icc (-r) r := by
  ext τ
  simp only [mem_preimage, mem_Icc]
  constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith

/-- Reflection computes the actual integrable remainder, giving the reference PV constant. -/
theorem integral_referenceCauchyPoleIntegrand {d : ℝ} (hd : 0 < d) (θ : ℝ) :
    (∫ τ in Icc (-Real.pi) Real.pi,
      contourCauchyPoleIntegrand (refCircle d) (deriv (refCircle d)) θ τ) =
      -I * (Real.pi : ℂ) := by
  let R := contourCauchyPoleIntegrand (refCircle d) (deriv (refCircle d)) θ
  have hi : IntegrableOn R (Icc (-Real.pi) Real.pi) := integrableOn_referenceCauchyPoleIntegrand hd θ
  have hn : IntegrableOn (fun τ => R (-τ)) (Icc (-Real.pi) Real.pi) := by
    have h := ((Measure.measurePreserving_neg (volume : Measure ℝ)).integrableOn_comp_preimage
      (Homeomorph.neg ℝ).measurableEmbedding).mpr hi
    simpa only [neg_preimage_centered_Icc, Function.comp_def] using h
  have hrefl := (Measure.measurePreserving_neg (volume : Measure ℝ)).setIntegral_preimage_emb
    (Homeomorph.neg ℝ).measurableEmbedding R (Icc (-Real.pi) Real.pi)
  rw [neg_preimage_centered_Icc] at hrefl
  have hsum : (∫ τ in Icc (-Real.pi) Real.pi, R τ) +
      (∫ τ in Icc (-Real.pi) Real.pi, R (-τ)) =
      ∫ _τ in Icc (-Real.pi) Real.pi, (-I : ℂ) := by
    rw [← integral_add hi hn]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Icc,
      ae_restrict_of_ae (volume.ae_ne (0 : ℝ))] with τ hτ hτ0
    exact referenceCauchyPoleIntegrand_opposite_add hd θ hτ0 (abs_le.mpr hτ)
  rw [hrefl, setIntegral_const, Real.volume_real_Icc_of_le (by linarith [Real.pi_pos] :
    -Real.pi ≤ Real.pi), Complex.real_smul] at hsum
  push_cast at hsum
  change (∫ τ in Icc (-Real.pi) Real.pi, R τ) = -I * (Real.pi : ℂ)
  linear_combination (1 / 2 : ℂ) * hsum

/-- The actual symmetric truncated reference-circle integrals converge to `-Iπ`. -/
theorem tendsto_referenceCauchyTruncated {d : ℝ} (hd : 0 < d) (θ : ℝ) :
    Tendsto (contourCauchyTruncated (refCircle d) (deriv (refCircle d)) θ Real.pi)
      (𝓝[>] (0 : ℝ)) (𝓝 (-I * (Real.pi : ℂ))) := by
  have h := tendsto_principalValue_of_integrable_remainder
    (integrableOn_referenceCauchyPoleIntegrand hd θ)
  change Tendsto (contourCauchyTruncated (refCircle d) (deriv (refCircle d)) θ Real.pi)
    (𝓝[>] (0 : ℝ)) (𝓝 (∫ τ in Icc (-Real.pi) Real.pi,
      contourCauchyPoleIntegrand (refCircle d) (deriv (refCircle d)) θ τ)) at h
  rwa [integral_referenceCauchyPoleIntegrand hd θ] at h

theorem tendsto_referenceCauchyTruncated_filter {ι : Type*} {l : Filter ι} {ε : ι → ℝ}
    {d : ℝ} (hd : 0 < d) (θ : ℝ)
    (hε : Tendsto ε l (𝓝 (0 : ℝ))) (hpos : ∀ᶠ i in l, 0 < ε i) :
    Tendsto (fun i => contourCauchyTruncated (refCircle d) (deriv (refCircle d)) θ Real.pi (ε i))
      l (𝓝 (-I * (Real.pi : ℂ))) :=
  (tendsto_referenceCauchyTruncated hd θ).comp
    (tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within ε hε hpos)

end Euler2D
