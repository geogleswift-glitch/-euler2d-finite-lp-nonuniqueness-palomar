module

public import RequestProject.Euler.ContourCauchyPrincipalValue
public import RequestProject.Euler.ContourLogKernel

/-!
# Uniform approximation of the actual logarithmic contour integral

A common genuine integrable majorant controls the omitted interval
uniformly in every external parameter.  The tail majorant tends to zero
by dominated convergence.  No compactness of the parameter set is used.
-/

@[expose] public section

noncomputable section

open Set MeasureTheory Filter Topology

namespace Euler2D

/-- The actual common norm-majorant integral on the omitted symmetric tail. -/
def contourTruncationTail (B : ℝ → ℝ) (r ε : ℝ) : ℝ :=
  ∫ τ in Icc (-r) r, {τ : ℝ | |τ| < ε}.indicator (fun τ => ‖B τ‖) τ

theorem tendsto_contourTruncationTail {B : ℝ → ℝ} {r : ℝ}
    (hB : IntegrableOn B (Icc (-r) r)) :
    Tendsto (contourTruncationTail B r) (𝓝 (0 : ℝ)) (𝓝 (0 : ℝ)) := by
  let F : ℝ → ℝ → ℝ := fun ε => {τ : ℝ | |τ| < ε}.indicator (fun τ => ‖B τ‖)
  have hmeas (ε : ℝ) : MeasurableSet {τ : ℝ | |τ| < ε} :=
    (isOpen_lt continuous_abs continuous_const).measurableSet
  have hlim : ∀ᵐ τ ∂volume.restrict (Icc (-r) r),
      Tendsto (fun ε => F ε τ) (𝓝 (0 : ℝ)) (𝓝 (0 : ℝ)) := by
    filter_upwards [ae_restrict_of_ae (volume.ae_ne (0 : ℝ))] with τ hτ
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_lt_nhds (abs_pos.mpr hτ)] with ε hε
    simp only [F, indicator_of_notMem (show τ ∉ {τ : ℝ | |τ| < ε} from not_lt.mpr hε.le)]
  have hDCT := tendsto_integral_filter_of_dominated_convergence
    (μ := volume.restrict (Icc (-r) r)) (fun τ => ‖B τ‖)
    (Eventually.of_forall fun ε => hB.norm.aestronglyMeasurable.indicator (hmeas ε))
    (Eventually.of_forall fun ε => ae_of_all _ fun τ => by
      simpa only [norm_norm] using
        (norm_indicator_le_norm_self (s := {τ : ℝ | |τ| < ε}) (fun τ => ‖B τ‖) τ))
    hB.norm hlim
  unfold contourTruncationTail
  simpa only [F, integral_zero] using hDCT

/-- Every actual cutoff error is bounded by the same omitted-tail integral. -/
theorem norm_integral_symmetricContourTruncation_sub_le_tail
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {F : ℝ → E} {B : ℝ → ℝ} {r ε : ℝ}
    (hF : AEStronglyMeasurable F (volume.restrict (Icc (-r) r)))
    (hB : IntegrableOn B (Icc (-r) r))
    (hbound : ∀ᵐ τ ∂volume.restrict (Icc (-r) r), ‖F τ‖ ≤ B τ) :
    ‖(∫ τ in symmetricContourTruncation r ε, F τ) - (∫ τ in Icc (-r) r, F τ)‖ ≤
      contourTruncationTail B r ε := by
  have hS : MeasurableSet {τ : ℝ | ε ≤ |τ|} :=
    (isClosed_le continuous_const continuous_abs).measurableSet
  have hT : MeasurableSet {τ : ℝ | |τ| < ε} :=
    (isOpen_lt continuous_abs continuous_const).measurableSet
  have hi := hB.mono' hF hbound
  change ‖(∫ τ in Icc (-r) r ∩ {τ : ℝ | ε ≤ |τ|}, F τ) -
    (∫ τ in Icc (-r) r, F τ)‖ ≤ _
  rw [← setIntegral_indicator hS, ← integral_sub (hi.indicator hS) hi]
  apply norm_integral_le_of_norm_le (hB.norm.indicator hT)
  filter_upwards [hbound] with τ hb
  by_cases hτ : ε ≤ |τ|
  · have hn : ¬ |τ| < ε := not_lt.mpr hτ
    simp only [indicator_of_mem (show τ ∈ {τ : ℝ | ε ≤ |τ|} from hτ), sub_self,
      norm_zero, indicator_of_notMem (show τ ∉ {τ : ℝ | |τ| < ε} from hn), le_refl]
  · have ht : |τ| < ε := lt_of_not_ge hτ
    simp only [indicator_of_notMem (show τ ∉ {τ : ℝ | ε ≤ |τ|} from hτ), zero_sub,
      norm_neg, indicator_of_mem (show τ ∈ {τ : ℝ | |τ| < ε} from ht)]
    exact hb.trans (by simpa only [Real.norm_eq_abs] using le_abs_self (B τ))

/-- A common integrable majorant gives uniform convergence on an arbitrary parameter set. -/
theorem tendstoUniformly_integral_symmetricContourTruncation
    {A E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {F : A → ℝ → E} {B : ℝ → ℝ} {r : ℝ}
    (hF : ∀ a, AEStronglyMeasurable (F a) (volume.restrict (Icc (-r) r)))
    (hB : IntegrableOn B (Icc (-r) r))
    (hbound : ∀ a, ∀ᵐ τ ∂volume.restrict (Icc (-r) r), ‖F a τ‖ ≤ B τ) :
    TendstoUniformly (fun ε a => ∫ τ in symmetricContourTruncation r ε, F a τ)
      (fun a => ∫ τ in Icc (-r) r, F a τ) (𝓝 (0 : ℝ)) := by
  rw [Metric.tendstoUniformly_iff]
  intro δ hδ
  filter_upwards [(tendsto_contourTruncationTail hB).eventually (eventually_lt_nhds hδ)] with ε hε a
  rw [dist_eq_norm, norm_sub_rev]
  exact (norm_integral_symmetricContourTruncation_sub_le_tail (hF a) hB (hbound a)).trans_lt hε

theorem tendstoUniformly_integral_symmetricContourTruncation_filter
    {A E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {l : Filter ι} {ε : ι → ℝ} {F : A → ℝ → E} {B : ℝ → ℝ} {r : ℝ}
    (hε : Tendsto ε l (𝓝 (0 : ℝ)))
    (hF : ∀ a, AEStronglyMeasurable (F a) (volume.restrict (Icc (-r) r)))
    (hB : IntegrableOn B (Icc (-r) r))
    (hbound : ∀ a, ∀ᵐ τ ∂volume.restrict (Icc (-r) r), ‖F a τ‖ ≤ B τ) :
    TendstoUniformly (fun i a => ∫ τ in symmetricContourTruncation r (ε i), F a τ)
      (fun a => ∫ τ in Icc (-r) r, F a τ) l := by
  have hu := tendstoUniformly_integral_symmetricContourTruncation hF hB hbound
  rw [Metric.tendstoUniformly_iff] at hu ⊢
  intro δ hδ
  exact hε.eventually (hu δ hδ)

/-- The literal symmetric cutoff of the actual logarithmic self-contour integral. -/
def contourSelfIntegralTruncated (z dz : ℝ → ℂ) (ε θ : ℝ) : ℂ :=
  ∫ τ in symmetricContourTruncation Real.pi ε, contourSelfIntegrand z dz θ τ

/-- Genuine logarithmic self integrals are uniformly approximated in the entire angle variable. -/
theorem tendstoUniformly_contourSelfIntegralTruncated {z dz : ℝ → ℂ} {c M D : ℝ}
    (hzc : Continuous z) (hdzc : Continuous dz) (hc : 0 < c)
    (hM : ∀ t, ‖z t‖ ≤ M) (hD : ∀ t, ‖dz t‖ ≤ D)
    (hchord : ∀ θ τ : ℝ, |τ| ≤ Real.pi → c * |τ| ≤ ‖z θ - z (θ + τ)‖) :
    TendstoUniformly (contourSelfIntegralTruncated z dz) (contourSelfIntegral z dz) (𝓝 (0 : ℝ)) := by
  have hab : -Real.pi ≤ Real.pi := by linarith [Real.pi_pos]
  have hmeas (θ : ℝ) : AEStronglyMeasurable (contourSelfIntegrand z dz θ)
      (volume.restrict (Icc (-Real.pi) Real.pi)) := by
    have hn : Continuous (fun τ : ℝ => ‖z θ - z (θ + τ)‖) :=
      (continuous_const.sub (hzc.comp (continuous_const.add continuous_id))).norm
    exact ((Real.measurable_log.comp hn.measurable).smul
      (hdzc.comp (continuous_const.add continuous_id)).measurable).aestronglyMeasurable
  have hB : IntegrableOn (fun τ => D * contourLogMajorant c M τ) (Icc (-Real.pi) Real.pi) :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mp
      ((intervalIntegrable_contourLogMajorant c M).const_mul D)
  have hb (θ : ℝ) : ∀ᵐ τ ∂volume.restrict (Icc (-Real.pi) Real.pi),
      ‖contourSelfIntegrand z dz θ τ‖ ≤ D * contourLogMajorant c M τ := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with τ hτ
    exact norm_contourSelfIntegrand_le hc hM hD hchord θ τ (abs_le.mpr hτ)
  have hu := tendstoUniformly_integral_symmetricContourTruncation hmeas hB hb
  have heq : (fun θ => ∫ τ in Icc (-Real.pi) Real.pi, contourSelfIntegrand z dz θ τ) =
      contourSelfIntegral z dz := by
    ext θ
    rw [contourSelfIntegral, intervalIntegral.integral_of_le hab, integral_Icc_eq_integral_Ioc]
  unfold contourSelfIntegralTruncated
  simpa only [heq] using hu

theorem tendstoUniformly_contourSelfIntegralTruncated_filter
    {ι : Type*} {l : Filter ι} {ε : ι → ℝ} {z dz : ℝ → ℂ} {c M D : ℝ}
    (hε : Tendsto ε l (𝓝 (0 : ℝ)))
    (hzc : Continuous z) (hdzc : Continuous dz) (hc : 0 < c)
    (hM : ∀ t, ‖z t‖ ≤ M) (hD : ∀ t, ‖dz t‖ ≤ D)
    (hchord : ∀ θ τ : ℝ, |τ| ≤ Real.pi → c * |τ| ≤ ‖z θ - z (θ + τ)‖) :
    TendstoUniformly (fun i => contourSelfIntegralTruncated z dz (ε i))
      (contourSelfIntegral z dz) l := by
  have hu := tendstoUniformly_contourSelfIntegralTruncated hzc hdzc hc hM hD hchord
  rw [Metric.tendstoUniformly_iff] at hu ⊢
  intro δ hδ
  exact hε.eventually (hu δ hδ)

end Euler2D
