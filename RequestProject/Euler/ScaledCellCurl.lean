module

public import RequestProject.Euler.CellCurl
public import RequestProject.Euler.ScaledRadialSobolev

/-!
# The exact curl of the physical circular datum series

The actual scaled blocks have their prescribed scaled two-interface
vorticities. The infinite velocity and vorticity series retain this
identity under their strong Lebesgue-space limits.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology Metric
open scoped ENNReal ContDiff

namespace Euler2D

def scaledCellW (A r : ℝ) (x : R2) : ℝ :=
  A * cellW (r⁻¹ • (x - torusCenter))

def scaledApproxCellCurl (A r : ℝ) (n : ℕ) (x : R2) : ℝ :=
  pd 0 (scaledRadialAverage A r (radialApproxScale n)) x 1 -
    pd 1 (scaledRadialAverage A r (radialApproxScale n)) x 0

lemma scaledApproxCellCurl_eq {r : ℝ} (hr : 0 < r) (A : ℝ) (n : ℕ) (x : R2) :
    scaledApproxCellCurl A r n x =
      A * (2 * profileAverage cellOmegaSq (radialApproxScale n)
        (‖r⁻¹ • (x - torusCenter)‖ ^ 2) +
        2 * ‖r⁻¹ • (x - torusCenter)‖ ^ 2 *
          deriv (profileAverage cellOmegaSq (radialApproxScale n))
            (‖r⁻¹ • (x - torusCenter)‖ ^ 2)) := by
  unfold scaledApproxCellCurl
  rw [pd_scaledRadialAverage hr, pd_scaledRadialAverage hr]
  change A * pd 0 (radialVelocity _ 0) _ 1 - A * pd 1 (radialVelocity _ 0) _ 0 = _
  rw [← mul_sub, radialVelocity_curl
    ((contDiff_profileAverage continuous_cellOmegaSq _).differentiable one_ne_zero)]
  simp only [sub_zero]

lemma ae_scaled_sq_radius_ne_interfaces {r : ℝ} (hr : 0 < r) :
    ∀ᵐ x ∂μT, ‖r⁻¹ • (x - torusCenter)‖ ^ 2 ≠ (3 / 5 : ℝ) ∧
      ‖r⁻¹ • (x - torusCenter)‖ ^ 2 ≠ 1 := by
  have ha : ∀ᵐ x ∂volume, x ∉ sphere torusCenter (r * cellA) :=
    measure_eq_zero_iff_ae_notMem.mp (Measure.addHaar_sphere volume torusCenter (r * cellA))
  have h1 : ∀ᵐ x ∂volume, x ∉ sphere torusCenter r :=
    measure_eq_zero_iff_ae_notMem.mp (Measure.addHaar_sphere volume torusCenter r)
  filter_upwards [ae_restrict_of_ae ha, ae_restrict_of_ae h1] with x hxa hx1
  have hn := norm_nonneg (r⁻¹ • (x - torusCenter))
  have hscale : ‖r⁻¹ • (x - torusCenter)‖ = r⁻¹ * ‖x - torusCenter‖ := by
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hr.le)]
  have hna : ‖x - torusCenter‖ ≠ r * cellA := by
    simpa only [mem_sphere_iff_norm] using hxa
  have hn1 : ‖x - torusCenter‖ ≠ r := by
    simpa only [mem_sphere_iff_norm] using hx1
  constructor
  · intro he
    have he' : ‖r⁻¹ • (x - torusCenter)‖ = cellA := by
      nlinarith [cellA_sq, cellA_pos]
    rw [hscale] at he'
    have hm := congrArg (fun z : ℝ => r * z) he'
    change r * (r⁻¹ * ‖x - torusCenter‖) = r * cellA at hm
    rw [← mul_assoc, mul_inv_cancel₀ hr.ne', one_mul] at hm
    exact hna hm
  · intro he
    have he' : ‖r⁻¹ • (x - torusCenter)‖ = 1 := by nlinarith
    rw [hscale] at he'
    have hm := congrArg (fun z : ℝ => r * z) he'
    change r * (r⁻¹ * ‖x - torusCenter‖) = r * 1 at hm
    rw [← mul_assoc, mul_inv_cancel₀ hr.ne', one_mul, mul_one] at hm
    exact hn1 hm

lemma tendsto_scaledApproxCellCurl_ae {r : ℝ} (hr : 0 < r) (A : ℝ) :
    ∀ᵐ x ∂μT, Tendsto (fun n => scaledApproxCellCurl A r n x) atTop
      (𝓝 (scaledCellW A r x)) := by
  filter_upwards [ae_scaled_sq_radius_ne_interfaces hr] with x hx
  have hd := tendsto_deriv_profileAverage_of_hasDerivAt continuous_cellOmegaSq
    (hasDerivAt_cellOmegaSq hx.1 hx.2)
  have hv := (tendsto_profileAverage continuous_cellOmegaSq
    (‖r⁻¹ • (x - torusCenter)‖ ^ 2)).const_mul 2
  have hlim := (hv.add (hd.const_mul (2 * ‖r⁻¹ • (x - torusCenter)‖ ^ 2))).const_mul A
  simpa only [scaledApproxCellCurl_eq hr, cellOmegaSq_curl_identity,
    scaledCellW, cellW_eq_cellCurlProfile] using hlim

lemma continuous_scaledApproxCellCurl (A r : ℝ) (n : ℕ) :
    Continuous (scaledApproxCellCurl A r n) := by
  exact ((EuclideanSpace.proj 1 : R2 →L[ℝ] ℝ).continuous.comp
    (continuous_pd_of_contDiff_one _ (contDiff_scaledRadialAverage A r _) 0)).sub
      ((EuclideanSpace.proj 0 : R2 →L[ℝ] ℝ).continuous.comp
        (continuous_pd_of_contDiff_one _ (contDiff_scaledRadialAverage A r _) 1))

lemma norm_scaledApproxCellCurl_le {r : ℝ} (hr : 0 < r) (A : ℝ) (n : ℕ) (x : R2) :
    ‖scaledApproxCellCurl A r n x‖ ≤ 14 * |A| := by
  have h0 := (abs_coord_le (pd 0 (scaledRadialAverage A r (radialApproxScale n)) x) 1).trans
    (norm_pd_scaledRadialAverage_le (radialApproxScale_pos n) hr A x 0)
  have h1 := (abs_coord_le (pd 1 (scaledRadialAverage A r (radialApproxScale n)) x) 0).trans
    (norm_pd_scaledRadialAverage_le (radialApproxScale_pos n) hr A x 1)
  exact (norm_sub_le _ _).trans (by
    simpa only [Real.norm_eq_abs] using (show
      |pd 0 (scaledRadialAverage A r (radialApproxScale n)) x 1| +
        |pd 1 (scaledRadialAverage A r (radialApproxScale n)) x 0| ≤ 14 * |A| by linarith))

lemma isCurl_scaledRadialAverageLp {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) (A : ℝ) (n : ℕ) :
    IsCurl (scaledRadialAverageLp A r n) (scaledApproxCellCurl A r n) := by
  have hc := isCurl_of_C1_matching_faces (contDiff_scaledRadialAverage A r (radialApproxScale n))
    (scaledRadialAverage_matchesTorusFaces hr hr1 (radialApproxScale_pos n) A)
  exact hc.congr_ae (scaledRadialAverageLp_ae A r n).symm (EventuallyEq.refl _ _)

lemma tendsto_integral_scaledApproxCellCurl {r : ℝ} (hr : 0 < r) (A : ℝ)
    {ψ : R2 → ℝ} (hψ : Continuous ψ) :
    Tendsto (fun n => ∫ x in torusBox, scaledApproxCellCurl A r n x * ψ x) atTop
      (𝓝 (∫ x in torusBox, scaledCellW A r x * ψ x)) := by
  apply tendsto_integral_of_dominated_convergence (μ := μT) (fun x => (14 * |A|) * ‖ψ x‖)
  · intro n
    exact ((continuous_scaledApproxCellCurl A r n).mul hψ).aestronglyMeasurable
  · exact (integrable_torusBox_of_continuous hψ.norm).const_mul _
  · intro n
    exact Eventually.of_forall (fun x => by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (norm_scaledApproxCellCurl_le hr A n x) (norm_nonneg _))
  · filter_upwards [tendsto_scaledApproxCellCurl_ae hr A] with x hx
    exact hx.mul_const (ψ x)

/-- Strong velocity convergence and convergence against the actual scalar
tests preserve a specified curl, rather than only an unknown curl bound. -/
lemma isCurl_of_tendsto_integrals {v : ℕ → L2T} {u : L2T} {w : ℕ → R2 → ℝ} {ω₀ : R2 → ℝ}
    (hv : Tendsto v atTop (𝓝 u)) (hc : ∀ n, IsCurl (v n) (w n))
    (hw : ∀ ψ, IsScalarTest ψ → Tendsto (fun n => ∫ x in torusBox, w n x * ψ x) atTop
      (𝓝 (∫ x in torusBox, ω₀ x * ψ x))) : IsCurl u ω₀ := by
  intro ψ hψ
  have hpd (i : Fin 2) : Continuous (pd i ψ) :=
    (hψ.1.continuous_fderiv (by simp)).clm_apply continuous_const
  have hsplit (v : L2T) :
      (∫ x in torusBox, v x 0 * pd 1 ψ x - v x 1 * pd 0 ψ x) =
        (∫ x in torusBox, v x 0 * pd 1 ψ x) - ∫ x in torusBox, v x 1 * pd 0 ψ x := by
    have hint (i j : Fin 2) : Integrable (fun x => v x i * pd j ψ x) μT := by
      obtain ⟨C, hC⟩ := bound_on_box (hpd j)
      exact integrable_lin v i (hpd j).aestronglyMeasurable hC
    exact integral_sub (hint 0 1) (hint 1 0)
  have hright : Tendsto
      (fun n => ∫ x in torusBox, v n x 0 * pd 1 ψ x - v n x 1 * pd 0 ψ x) atTop
      (𝓝 (∫ x in torusBox, u x 0 * pd 1 ψ x - u x 1 * pd 0 ψ x)) := by
    simp_rw [hsplit]
    exact (tendsto_fixed_lin hv (hpd 1) 0).sub (tendsto_fixed_lin hv (hpd 0) 1)
  exact tendsto_nhds_unique (hw ψ hψ)
    (hright.congr' (Eventually.of_forall fun n => (hc n ψ hψ).symm))

/-- Exact physical amplitude and radius scaling of the circular curl. -/
theorem isCurl_scaledCellVelocity {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) (A : ℝ) {v : L2T}
    (hveq : (v : R2 → R2) =ᵐ[μT]
      (fun x => (A * r) • cellVelocity (r⁻¹ • (x - torusCenter)))) :
    IsCurl v (scaledCellW A r) :=
  isCurl_of_tendsto_integrals (tendsto_scaledRadialAverageLp hr A hveq)
    (isCurl_scaledRadialAverageLp hr hr1 A)
    (fun _ hψ => tendsto_integral_scaledApproxCellCurl hr A hψ.1.continuous)

theorem isCurl_velocityDatumTermLp {A₀ b R ρ : ℝ} (hR : 0 < R) (hR1 : R ≤ 1)
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (j : ℕ) :
    IsCurl (velocityDatumTermLp (A₀ := A₀) (b := b) hR hρ 2 j)
      (fun x => datumTerm A₀ b R ρ j (x - torusCenter)) :=
  isCurl_scaledCellVelocity (radScale_pos hR hρ j) (radScale_le_one hR hR1 hρ hρ1 j)
    (ampScale A₀ b j) (coeFn_velocityDatumTermLp hR hρ 2 j)

end Euler2D

end
