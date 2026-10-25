module

public import RequestProject.Euler.ContourLogTruncation
public import RequestProject.Euler.ContourCauchyWeightedPrincipalValue
public import RequestProject.Euler.ContourCauchyRemainderHolder
public import RequestProject.Euler.ContourC1PrincipalValue

/-! Uniform convergence of the genuinely defined Cauchy truncations,
using the actual common power majorants for the remainder and increment. -/

@[expose] public section

noncomputable section

open Set MeasureTheory Filter Topology
open scoped NNReal

namespace Euler2D

theorem tendstoUniformly_contourCauchyTruncated {z dz : ℝ → ℂ} {γ H c r : ℝ}
    (hzc : Continuous z) (hdzc : Continuous dz) (hγ : 0 < γ) (hH : 0 ≤ H)
    (hc : 0 < c) (hr : 0 ≤ r) (hz : ∀ s, HasDerivAt z (dz s) s)
    (hd : ∀ s t, ‖dz s - dz t‖ ≤ H * |s - t| ^ γ)
    (hchord : ∀ θ τ : ℝ, |τ| ≤ r → c * |τ| ≤ ‖z θ - z (θ + τ)‖) :
    TendstoUniformly (fun ε θ => contourCauchyTruncated z dz θ r ε)
      (fun θ => ∫ τ in Icc (-r) r, contourCauchyPoleIntegrand z dz θ τ) (𝓝[>] (0 : ℝ)) := by
  have hB := (integrableOn_abs_rpow_sub_one hγ hr).const_mul (2 * H / c)
  have hm (θ : ℝ) : AEStronglyMeasurable (contourCauchyPoleIntegrand z dz θ)
      (volume.restrict (Icc (-r) r)) :=
    (measurable_contourCauchyPoleIntegrand hzc.measurable hdzc.measurable θ).aestronglyMeasurable
  have hb (θ : ℝ) : ∀ᵐ τ ∂volume.restrict (Icc (-r) r),
      ‖contourCauchyPoleIntegrand z dz θ τ‖ ≤ (2 * H / c) * |τ| ^ (γ - 1) := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with τ hτ
    exact norm_contourCauchyPoleIntegrand_le hγ.le hH hc hz hd (hchord θ τ (abs_le.mpr hτ))
  have hu := tendstoUniformly_integral_symmetricContourTruncation hm hB hb
  rw [Metric.tendstoUniformly_iff] at hu ⊢
  intro δ hδ
  filter_upwards [self_mem_nhdsWithin, (hu δ hδ).filter_mono nhdsWithin_le_nhds] with ε hε hnear θ
  have hi := integrableOn_contourCauchyPoleIntegrand hzc hdzc hγ hH hc hr hz hd hchord θ
  simpa only [contourCauchyTruncated, integral_symmetricContourTruncation_eq_remainder hε hi,
    contourCauchyPoleIntegrand] using hnear θ

theorem tendstoUniformly_contourCauchyWeightedTruncated
    {z dz f : ℝ → ℂ} {γ H L Hf Mf c r : ℝ}
    (hzc : Continuous z) (hdzc : Continuous dz) (hfm : Measurable f)
    (hγ : 0 < γ) (hH : 0 ≤ H) (hL : 0 ≤ L) (hHf : 0 ≤ Hf) (hc : 0 < c) (hr : 0 ≤ r)
    (hz : ∀ s, HasDerivAt z (dz s) s)
    (hd : ∀ s t, ‖dz s - dz t‖ ≤ H * |s - t| ^ γ) (hdL : ∀ s, ‖dz s‖ ≤ L)
    (hf : ∀ s t, ‖f s - f t‖ ≤ Hf * |s - t| ^ γ) (hfM : ∀ s, ‖f s‖ ≤ Mf)
    (hchord : ∀ θ τ : ℝ, |τ| ≤ r → c * |τ| ≤ ‖z θ - z (θ + τ)‖) :
    TendstoUniformly (fun ε θ => contourCauchyWeightedTruncated z dz f θ r ε)
      (fun θ => (∫ τ in Icc (-r) r, contourCauchyPoleIntegrand z dz θ τ) * f θ +
        ∫ τ in Icc (-r) r, contourCauchyIncrementIntegrand z dz f θ τ) (𝓝[>] (0 : ℝ)) := by
  have hB := (integrableOn_abs_rpow_sub_one hγ hr).const_mul (L * Hf / c)
  have hm (θ : ℝ) : AEStronglyMeasurable (contourCauchyIncrementIntegrand z dz f θ)
      (volume.restrict (Icc (-r) r)) :=
    (measurable_contourCauchyIncrementIntegrand hzc.measurable hdzc.measurable hfm θ).aestronglyMeasurable
  have hb (θ : ℝ) : ∀ᵐ τ ∂volume.restrict (Icc (-r) r),
      ‖contourCauchyIncrementIntegrand z dz f θ τ‖ ≤ (L * Hf / c) * |τ| ^ (γ - 1) := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with τ hτ
    apply norm_contourCauchyIncrementIntegrand_le hc hL hHf (hchord θ τ (abs_le.mpr hτ)) (hdL _)
    simpa only [add_sub_cancel_left] using hf (θ + τ) θ
  have hI := tendstoUniformly_integral_symmetricContourTruncation hm hB hb
  have hK := tendstoUniformly_contourCauchyTruncated hzc hdzc hγ hH hc hr hz hd hchord
  let C : ℝ := max 1 Mf
  have hC : 0 < C := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hfC (θ : ℝ) : ‖f θ‖ ≤ C := (hfM θ).trans (le_max_right _ _)
  rw [Metric.tendstoUniformly_iff] at hI hK ⊢
  intro δ hδ
  filter_upwards [self_mem_nhdsWithin,
    hK (δ / (2 * C)) (div_pos hδ (mul_pos (by norm_num) hC)),
    (hI (δ / 2) (by linarith)).filter_mono nhdsWithin_le_nhds]
    with ε hε hKnear hInear θ
  have hiR := integrableOn_contourCauchyPoleIntegrand hzc hdzc hγ hH hc hr hz hd hchord θ
  have hiI : IntegrableOn (contourCauchyIncrementIntegrand z dz f θ) (Icc (-r) r) :=
    hB.mono' (hm θ) (hb θ)
  have heq := symmetricWeightedTruncated_eq hε hiR hiI
  change contourCauchyWeightedTruncated z dz f θ r ε = _ at heq
  rw [dist_eq_norm, heq]
  have hnorm :
      ‖((∫ τ in Icc (-r) r, contourCauchyPoleIntegrand z dz θ τ) * f θ +
          ∫ τ in Icc (-r) r, contourCauchyIncrementIntegrand z dz f θ τ) -
        ((∫ τ in symmetricContourTruncation r ε, dz (θ + τ) / (z θ - z (θ + τ))) * f θ +
          ∫ τ in symmetricContourTruncation r ε, contourCauchyIncrementIntegrand z dz f θ τ)‖ ≤
      ‖(∫ τ in Icc (-r) r, contourCauchyPoleIntegrand z dz θ τ) -
          contourCauchyTruncated z dz θ r ε‖ * C +
        ‖(∫ τ in Icc (-r) r, contourCauchyIncrementIntegrand z dz f θ τ) -
          ∫ τ in symmetricContourTruncation r ε, contourCauchyIncrementIntegrand z dz f θ τ‖ := by
    have halg (a b d e v : ℂ) : (a * v + b) - (d * v + e) = (a - d) * v + (b - e) := by ring
    rw [halg]
    exact (norm_add_le _ _).trans (add_le_add
      (by rw [norm_mul]; exact mul_le_mul_of_nonneg_left (hfC θ) (norm_nonneg _)) le_rfl)
  have hker := hKnear θ
  have hinc := hInear θ
  rw [dist_eq_norm] at hker hinc
  have hprod : ‖(∫ τ in Icc (-r) r, contourCauchyPoleIntegrand z dz θ τ) -
      contourCauchyTruncated z dz θ r ε‖ * C < δ / 2 := by
    calc
      _ < (δ / (2 * C)) * C := mul_lt_mul_of_pos_right hker hC
      _ = _ := by field_simp
  exact hnorm.trans_lt ((add_lt_add hprod hinc).trans_eq (by ring))

theorem tendstoUniformly_contourC1CauchyTruncated {γ : ℝ≥0} (Z : ContourC1Space γ)
    {c : ℝ} (hγ : 0 < (γ : ℝ)) (hc : 0 < c)
    (hchord : ∀ θ τ : ℝ, |τ| ≤ Real.pi → c * |τ| ≤
      ‖ContourC1Space.lift γ Z θ - ContourC1Space.lift γ Z (θ + τ)‖) :
    TendstoUniformly (fun ε θ => contourCauchyTruncated (ContourC1Space.lift γ Z)
      (deriv (ContourC1Space.lift γ Z)) θ Real.pi ε)
      (fun θ => ∫ τ in Icc (-Real.pi) Real.pi,
        contourCauchyPoleIntegrand (ContourC1Space.lift γ Z)
          (deriv (ContourC1Space.lift γ Z)) θ τ) (𝓝[>] (0 : ℝ)) :=
  tendstoUniformly_contourCauchyTruncated (ContourC1Space.contDiff_lift Z).continuous
    (ContourC1Space.contDiff_lift Z).continuous_deriv_one hγ (norm_nonneg Z) hc Real.pi_pos.le
    (fun s => (ContourC1Space.hasDerivAt_lift Z s).differentiableAt.hasDerivAt)
    (norm_contourC1_deriv_lift_sub_le Z) hchord

theorem tendstoUniformly_contourC1CauchyWeightedTruncated {γ : ℝ≥0}
    (Z : ContourC1Space γ) (f : ContourHolderSpace γ) {c : ℝ}
    (hγ : 0 < (γ : ℝ)) (hc : 0 < c)
    (hchord : ∀ θ τ : ℝ, |τ| ≤ Real.pi → c * |τ| ≤
      ‖ContourC1Space.lift γ Z θ - ContourC1Space.lift γ Z (θ + τ)‖) :
    TendstoUniformly (fun ε θ => contourCauchyWeightedTruncated (ContourC1Space.lift γ Z)
      (deriv (ContourC1Space.lift γ Z)) (fun t : ℝ => f (t : ContourCircle)) θ Real.pi ε)
      (fun θ => (∫ τ in Icc (-Real.pi) Real.pi,
        contourCauchyPoleIntegrand (ContourC1Space.lift γ Z)
          (deriv (ContourC1Space.lift γ Z)) θ τ) * f (θ : ContourCircle) +
            contourC1CauchyIncrement Z f θ) (𝓝[>] (0 : ℝ)) :=
  tendstoUniformly_contourCauchyWeightedTruncated (ContourC1Space.contDiff_lift Z).continuous
    (ContourC1Space.contDiff_lift Z).continuous_deriv_one
    (((HolderFunctionSpace.toBCF γ f).continuous.comp (AddCircle.continuous_mk' (2 * Real.pi))).measurable)
    hγ (norm_nonneg Z) (norm_nonneg Z) (norm_nonneg f) hc Real.pi_pos.le
    (fun s => (ContourC1Space.hasDerivAt_lift Z s).differentiableAt.hasDerivAt)
    (norm_contourC1_deriv_lift_sub_le Z) (ContourC1Space.norm_deriv_lift_le Z)
    (norm_contourHolder_lift_sub_global_le f) (fun s => HolderFunctionSpace.norm_eval_le f _)
    hchord

/-- The genuine near-circle constant-density PV converges uniformly in the entire angle. -/
theorem tendstoUniformly_contourC1CauchyTruncated_near_circle {γ : ℝ≥0}
    (Z Z₀ : ContourC1Space γ) {r : ℝ} (hγ : 0 < (γ : ℝ)) (hr : 0 < r)
    (href : ContourC1Space.lift γ Z₀ = refCircle r)
    (hsmall : ‖Z - Z₀‖ < 2 * r / Real.pi) :
    TendstoUniformly (fun ε θ => contourCauchyTruncated (ContourC1Space.lift γ Z)
      (deriv (ContourC1Space.lift γ Z)) θ Real.pi ε)
      (fun _ : ℝ => -Complex.I * (Real.pi : ℂ)) (𝓝[>] (0 : ℝ)) := by
  have hchord : ∀ θ τ : ℝ, |τ| ≤ Real.pi → (2 * r / Real.pi - ‖Z - Z₀‖) * |τ| ≤
      ‖ContourC1Space.lift γ Z θ - ContourC1Space.lift γ Z (θ + τ)‖ :=
    fun θ τ hτ => contourC1_chord_lower_of_norm_sub Z Z₀ hr.le href θ (abs_le.mp hτ)
  have hu := tendstoUniformly_contourC1CauchyTruncated Z hγ (sub_pos.mpr hsmall) hchord
  have heq : (fun θ => ∫ τ in Icc (-Real.pi) Real.pi,
      contourCauchyPoleIntegrand (ContourC1Space.lift γ Z)
        (deriv (ContourC1Space.lift γ Z)) θ τ) = fun _ : ℝ => -Complex.I * (Real.pi : ℂ) :=
    funext (integral_contourC1PoleIntegrand_near_circle Z Z₀ hγ hr href hsmall)
  simpa only [heq] using hu

/-- The genuine near-circle weighted PV also converges uniformly in the entire angle. -/
theorem tendstoUniformly_contourC1CauchyWeightedTruncated_near_circle {γ : ℝ≥0}
    (Z Z₀ : ContourC1Space γ) (f : ContourHolderSpace γ) {r : ℝ}
    (hγ : 0 < (γ : ℝ)) (hr : 0 < r)
    (href : ContourC1Space.lift γ Z₀ = refCircle r)
    (hsmall : ‖Z - Z₀‖ < 2 * r / Real.pi) :
    TendstoUniformly (fun ε θ => contourCauchyWeightedTruncated (ContourC1Space.lift γ Z)
      (deriv (ContourC1Space.lift γ Z)) (fun t : ℝ => f (t : ContourCircle)) θ Real.pi ε)
      (fun θ => (-Complex.I * (Real.pi : ℂ)) * f (θ : ContourCircle) +
        contourC1CauchyIncrement Z f θ) (𝓝[>] (0 : ℝ)) := by
  have hchord : ∀ θ τ : ℝ, |τ| ≤ Real.pi → (2 * r / Real.pi - ‖Z - Z₀‖) * |τ| ≤
      ‖ContourC1Space.lift γ Z θ - ContourC1Space.lift γ Z (θ + τ)‖ :=
    fun θ τ hτ => contourC1_chord_lower_of_norm_sub Z Z₀ hr.le href θ (abs_le.mp hτ)
  have hu := tendstoUniformly_contourC1CauchyWeightedTruncated Z f hγ (sub_pos.mpr hsmall) hchord
  have heq : (fun θ : ℝ => (∫ τ in Icc (-Real.pi) Real.pi,
      contourCauchyPoleIntegrand (ContourC1Space.lift γ Z)
        (deriv (ContourC1Space.lift γ Z)) θ τ) * f (θ : ContourCircle) +
        contourC1CauchyIncrement Z f θ) =
      fun θ : ℝ => (-Complex.I * (Real.pi : ℂ)) * f (θ : ContourCircle) + contourC1CauchyIncrement Z f θ := by
    ext θ
    rw [integral_contourC1PoleIntegrand_near_circle Z Z₀ hγ hr href hsmall θ]
  simpa only [heq] using hu

theorem tendstoUniformly_contourC1CauchyWeightedTruncated_near_circle_filter
    {ι : Type*} {l : Filter ι} {ε : ι → ℝ} {γ : ℝ≥0}
    (Z Z₀ : ContourC1Space γ) (f : ContourHolderSpace γ) {r : ℝ}
    (hε : Tendsto ε l (𝓝 (0 : ℝ))) (hpos : ∀ᶠ i in l, 0 < ε i)
    (hγ : 0 < (γ : ℝ)) (hr : 0 < r)
    (href : ContourC1Space.lift γ Z₀ = refCircle r)
    (hsmall : ‖Z - Z₀‖ < 2 * r / Real.pi) :
    TendstoUniformly (fun i θ => contourCauchyWeightedTruncated (ContourC1Space.lift γ Z)
      (deriv (ContourC1Space.lift γ Z)) (fun t : ℝ => f (t : ContourCircle)) θ Real.pi (ε i))
      (fun θ => (-Complex.I * (Real.pi : ℂ)) * f (θ : ContourCircle) +
        contourC1CauchyIncrement Z f θ) l := by
  have hu := tendstoUniformly_contourC1CauchyWeightedTruncated_near_circle Z Z₀ f hγ hr href hsmall
  rw [Metric.tendstoUniformly_iff] at hu ⊢
  intro δ hδ
  exact (tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within ε hε hpos).eventually (hu δ hδ)

end Euler2D
