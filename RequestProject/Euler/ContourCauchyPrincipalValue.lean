module

public import RequestProject.Euler.ContourCauchyPole

/-!
# Actual symmetric truncations of the contour Cauchy pole

Every inverse-pole integral used here is over a genuine compact set away
from the origin, and is proved integrable there.  Reflection cancels that
pole on each symmetric truncation.  Dominated convergence is applied only
to the genuinely integrable remainder.
-/

@[expose] public section

noncomputable section

open Set MeasureTheory Filter Topology
open scoped NNReal

namespace Euler2D

/-- The genuine symmetric truncated parameter domain. -/
def symmetricContourTruncation (r ε : ℝ) : Set ℝ :=
  Icc (-r) r ∩ {τ | ε ≤ |τ|}

theorem measurableSet_symmetricContourTruncation (r ε : ℝ) :
    MeasurableSet (symmetricContourTruncation r ε) :=
  measurableSet_Icc.inter (isClosed_le continuous_const continuous_abs).measurableSet

theorem isCompact_symmetricContourTruncation (r ε : ℝ) :
    IsCompact (symmetricContourTruncation r ε) :=
  isCompact_Icc.inter_right (isClosed_le continuous_const continuous_abs)

theorem symmetricContourTruncation_subset (r ε : ℝ) :
    symmetricContourTruncation r ε ⊆ Icc (-r) r := inter_subset_left

theorem neg_preimage_symmetricContourTruncation (r ε : ℝ) :
    (fun τ : ℝ => -τ) ⁻¹' symmetricContourTruncation r ε =
      symmetricContourTruncation r ε := by
  ext τ
  simp only [symmetricContourTruncation, mem_preimage, mem_inter_iff, mem_Icc,
    mem_setOf_eq, abs_neg]
  constructor <;> rintro ⟨⟨h₁, h₂⟩, h₃⟩ <;> exact ⟨⟨by linarith, by linarith⟩, h₃⟩

/-- The pole is truly integrable on every positive symmetric truncation. -/
theorem integrableOn_complex_inv_symmetricContourTruncation {r ε : ℝ} (hε : 0 < ε) :
    IntegrableOn (fun τ : ℝ => (τ : ℂ)⁻¹) (symmetricContourTruncation r ε) := by
  apply ContinuousOn.integrableOn_compact (isCompact_symmetricContourTruncation r ε)
  apply Complex.continuous_ofReal.continuousOn.inv₀
  intro τ hτ
  have hτ0 : τ ≠ 0 := by
    intro hτ0
    have : ε ≤ |τ| := hτ.2
    simp only [hτ0, abs_zero] at this
    linarith
  exact_mod_cast hτ0

/-- Actual reflection of the truncated domain makes the inverse-pole integral zero. -/
theorem integral_complex_inv_symmetricContourTruncation {r ε : ℝ} (_hε : 0 < ε) :
    (∫ τ in symmetricContourTruncation r ε, (τ : ℂ)⁻¹) = 0 := by
  have hreflection := (Measure.measurePreserving_neg (volume : Measure ℝ)).setIntegral_preimage_emb
    (Homeomorph.neg ℝ).measurableEmbedding (fun τ : ℝ => (τ : ℂ)⁻¹)
    (symmetricContourTruncation r ε)
  rw [neg_preimage_symmetricContourTruncation] at hreflection
  simp only [Complex.ofReal_neg, inv_neg, integral_neg] at hreflection
  apply Complex.ext
  · have h := congrArg Complex.re hreflection
    simp only [Complex.neg_re, Complex.zero_re] at h ⊢
    linarith
  · have h := congrArg Complex.im hreflection
    simp only [Complex.neg_im, Complex.zero_im] at h ⊢
    linarith

/-- The singular part is integrable after truncation because its remainder is integrable. -/
theorem integrableOn_symmetricContourTruncation_of_integrable_remainder
    {g : ℝ → ℂ} {r ε : ℝ} (hε : 0 < ε)
    (hR : IntegrableOn (fun τ => g τ + (τ : ℂ)⁻¹) (Icc (-r) r)) :
    IntegrableOn g (symmetricContourTruncation r ε) := by
  have h := (hR.mono_set (symmetricContourTruncation_subset r ε)).sub
    (integrableOn_complex_inv_symmetricContourTruncation hε)
  have heq : (fun τ => g τ + (τ : ℂ)⁻¹) - (fun τ : ℝ => (τ : ℂ)⁻¹) = g := by
    ext τ
    exact add_sub_cancel_right (g τ) (τ : ℂ)⁻¹
  rw [heq] at h
  exact h

/-- Each genuinely defined truncated singular integral equals its truncated remainder. -/
theorem integral_symmetricContourTruncation_eq_remainder
    {g : ℝ → ℂ} {r ε : ℝ} (hε : 0 < ε)
    (hR : IntegrableOn (fun τ => g τ + (τ : ℂ)⁻¹) (Icc (-r) r)) :
    (∫ τ in symmetricContourTruncation r ε, g τ) =
      ∫ τ in symmetricContourTruncation r ε, g τ + (τ : ℂ)⁻¹ := by
  rw [integral_add
    (integrableOn_symmetricContourTruncation_of_integrable_remainder hε hR)
    (integrableOn_complex_inv_symmetricContourTruncation hε),
    integral_complex_inv_symmetricContourTruncation hε, add_zero]

/-- Actual dominated convergence for the truncated integrable remainder. -/
theorem tendsto_integral_symmetricContourTruncation {R : ℝ → ℂ} {r : ℝ}
    (hR : IntegrableOn R (Icc (-r) r)) :
    Tendsto (fun ε : ℝ => ∫ τ in symmetricContourTruncation r ε, R τ)
      (𝓝[>] (0 : ℝ)) (𝓝 (∫ τ in Icc (-r) r, R τ)) := by
  let F : ℝ → ℝ → ℂ := fun ε => {τ : ℝ | ε ≤ |τ|}.indicator R
  have hmeas (ε : ℝ) : MeasurableSet {τ : ℝ | ε ≤ |τ|} :=
    (isClosed_le continuous_const continuous_abs).measurableSet
  have hlim : ∀ᵐ τ ∂volume.restrict (Icc (-r) r),
      Tendsto (fun ε => F ε τ) (𝓝[>] (0 : ℝ)) (𝓝 (R τ)) := by
    filter_upwards [ae_restrict_of_ae (volume.ae_ne (0 : ℝ))] with τ hτ
    have hev : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ), ε < |τ| :=
      (eventually_lt_nhds (abs_pos.mpr hτ)).filter_mono nhdsWithin_le_nhds
    apply tendsto_const_nhds.congr'
    filter_upwards [hev] with ε hε
    simp only [F, indicator_of_mem (show τ ∈ {τ : ℝ | ε ≤ |τ|} from hε.le)]
  have hDCT := tendsto_integral_filter_of_dominated_convergence (μ := volume.restrict (Icc (-r) r))
    (fun τ => ‖R τ‖)
    (Eventually.of_forall fun ε => hR.aestronglyMeasurable.indicator (hmeas ε))
    (Eventually.of_forall fun ε => ae_of_all _ fun τ => norm_indicator_le_norm_self _ _) hR.norm hlim
  simpa only [F, setIntegral_indicator (hmeas _), symmetricContourTruncation] using hDCT

/-- Genuine symmetric principal value, obtained by cancelling a truly integrable pole remainder. -/
theorem tendsto_principalValue_of_integrable_remainder {g : ℝ → ℂ} {r : ℝ}
    (hR : IntegrableOn (fun τ => g τ + (τ : ℂ)⁻¹) (Icc (-r) r)) :
    Tendsto (fun ε : ℝ => ∫ τ in symmetricContourTruncation r ε, g τ)
      (𝓝[>] (0 : ℝ)) (𝓝 (∫ τ in Icc (-r) r, g τ + (τ : ℂ)⁻¹)) := by
  apply (tendsto_integral_symmetricContourTruncation hR).congr'
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact (integral_symmetricContourTruncation_eq_remainder hε hR).symm

/-- Arbitrary positive cutoff families tending to zero give that same actual principal value. -/
theorem tendsto_principalValue_of_integrable_remainder_filter
    {ι : Type*} {l : Filter ι} {ε : ι → ℝ} {g : ℝ → ℂ} {r : ℝ}
    (hε : Tendsto ε l (𝓝 (0 : ℝ))) (hpos : ∀ᶠ i in l, 0 < ε i)
    (hR : IntegrableOn (fun τ => g τ + (τ : ℂ)⁻¹) (Icc (-r) r)) :
    Tendsto (fun i => ∫ τ in symmetricContourTruncation r (ε i), g τ)
      l (𝓝 (∫ τ in Icc (-r) r, g τ + (τ : ℂ)⁻¹)) :=
  (tendsto_principalValue_of_integrable_remainder hR).comp
    (tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within ε hε hpos)

/-- The literal symmetric truncation of the genuine contour Cauchy kernel. -/
def contourCauchyTruncated (z dz : ℝ → ℂ) (θ r ε : ℝ) : ℂ :=
  ∫ τ in symmetricContourTruncation r ε, dz (θ + τ) / (z θ - z (θ + τ))

/-- Each actual contour-kernel truncation is genuinely integrable. -/
theorem integrableOn_contourCauchyTruncatedKernel {z dz : ℝ → ℂ} {γ H c r ε : ℝ}
    (hzc : Continuous z) (hdzc : Continuous dz) (hγ : 0 < γ) (hH : 0 ≤ H)
    (hc : 0 < c) (hr : 0 ≤ r) (hε : 0 < ε) (hz : ∀ s, HasDerivAt z (dz s) s)
    (hd : ∀ s t, ‖dz s - dz t‖ ≤ H * |s - t| ^ γ)
    (hchord : ∀ θ τ : ℝ, |τ| ≤ r → c * |τ| ≤ ‖z θ - z (θ + τ)‖) (θ : ℝ) :
    IntegrableOn (fun τ => dz (θ + τ) / (z θ - z (θ + τ)))
      (symmetricContourTruncation r ε) :=
  integrableOn_symmetricContourTruncation_of_integrable_remainder hε
    (integrableOn_contourCauchyPoleIntegrand hzc hdzc hγ hH hc hr hz hd hchord θ)

/-- The genuine Cauchy principal value exists by actual Taylor-pole cancellation. -/
theorem tendsto_contourCauchyTruncated {z dz : ℝ → ℂ} {γ H c r : ℝ}
    (hzc : Continuous z) (hdzc : Continuous dz) (hγ : 0 < γ) (hH : 0 ≤ H)
    (hc : 0 < c) (hr : 0 ≤ r) (hz : ∀ s, HasDerivAt z (dz s) s)
    (hd : ∀ s t, ‖dz s - dz t‖ ≤ H * |s - t| ^ γ)
    (hchord : ∀ θ τ : ℝ, |τ| ≤ r → c * |τ| ≤ ‖z θ - z (θ + τ)‖) (θ : ℝ) :
    Tendsto (contourCauchyTruncated z dz θ r) (𝓝[>] (0 : ℝ))
      (𝓝 (∫ τ in Icc (-r) r, contourCauchyPoleIntegrand z dz θ τ)) :=
  tendsto_principalValue_of_integrable_remainder
    (integrableOn_contourCauchyPoleIntegrand hzc hdzc hγ hH hc hr hz hd hchord θ)

/-- The same actual contour principal value along every positive vanishing cutoff family. -/
theorem tendsto_contourCauchyTruncated_filter
    {ι : Type*} {l : Filter ι} {ε : ι → ℝ}
    {z dz : ℝ → ℂ} {γ H c r : ℝ}
    (hε : Tendsto ε l (𝓝 (0 : ℝ))) (hpos : ∀ᶠ i in l, 0 < ε i)
    (hzc : Continuous z) (hdzc : Continuous dz) (hγ : 0 < γ) (hH : 0 ≤ H)
    (hc : 0 < c) (hr : 0 ≤ r) (hz : ∀ s, HasDerivAt z (dz s) s)
    (hd : ∀ s t, ‖dz s - dz t‖ ≤ H * |s - t| ^ γ)
    (hchord : ∀ θ τ : ℝ, |τ| ≤ r → c * |τ| ≤ ‖z θ - z (θ + τ)‖) (θ : ℝ) :
    Tendsto (fun i => contourCauchyTruncated z dz θ r (ε i)) l
      (𝓝 (∫ τ in Icc (-r) r, contourCauchyPoleIntegrand z dz θ τ)) :=
  tendsto_principalValue_of_integrable_remainder_filter hε hpos
    (integrableOn_contourCauchyPoleIntegrand hzc hdzc hγ hH hc hr hz hd hchord θ)

/-- The true C¹ Hölder norm controls differences of the actual lifted derivative. -/
theorem norm_contourC1_deriv_lift_sub_le {γ : ℝ≥0} (Z : ContourC1Space γ) (s t : ℝ) :
    ‖deriv (ContourC1Space.lift γ Z) s - deriv (ContourC1Space.lift γ Z) t‖ ≤
      ‖Z‖ * |s - t| ^ (γ : ℝ) := by
  rw [ContourC1Space.deriv_lift, ContourC1Space.deriv_lift]
  have hh := norm_contourHolder_lift_sub_le (ContourC1Space.derivative γ Z) t (s - t)
  have ht : t + (s - t) = s := by ring
  rw [ht] at hh
  exact hh.trans (mul_le_mul_of_nonneg_right (ContourC1Space.norm_derivative_le Z)
    (Real.rpow_nonneg (abs_nonneg _) _))

/-- The actual C¹ Hölder contour space has a genuine symmetric principal value. -/
theorem tendsto_contourC1CauchyTruncated {γ : ℝ≥0} (Z : ContourC1Space γ)
    {c r : ℝ} (hγ : 0 < (γ : ℝ)) (hc : 0 < c) (hr : 0 ≤ r)
    (hchord : ∀ θ τ : ℝ, |τ| ≤ r → c * |τ| ≤
      ‖ContourC1Space.lift γ Z θ - ContourC1Space.lift γ Z (θ + τ)‖) (θ : ℝ) :
    Tendsto (contourCauchyTruncated (ContourC1Space.lift γ Z)
      (deriv (ContourC1Space.lift γ Z)) θ r) (𝓝[>] (0 : ℝ))
      (𝓝 (∫ τ in Icc (-r) r, contourCauchyPoleIntegrand (ContourC1Space.lift γ Z)
        (deriv (ContourC1Space.lift γ Z)) θ τ)) := by
  have hdzc : Continuous (deriv (ContourC1Space.lift γ Z)) := by
    have heq : deriv (ContourC1Space.lift γ Z) =
        fun t : ℝ => ContourC1Space.derivative γ Z (t : ContourCircle) :=
      funext (ContourC1Space.deriv_lift Z)
    rw [heq]
    exact (HolderFunctionSpace.toBCF γ (ContourC1Space.derivative γ Z)).continuous.comp
      (AddCircle.continuous_mk' (2 * Real.pi))
  apply tendsto_contourCauchyTruncated (ContourC1Space.contDiff_lift Z).continuous hdzc
    hγ (norm_nonneg Z) hc hr
  · intro s
    exact (ContourC1Space.hasDerivAt_lift Z s).differentiableAt.hasDerivAt
  · exact norm_contourC1_deriv_lift_sub_le Z
  · exact hchord

end Euler2D
