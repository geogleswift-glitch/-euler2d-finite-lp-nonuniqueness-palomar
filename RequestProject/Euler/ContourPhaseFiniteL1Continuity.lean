module

public import RequestProject.Euler.ContourPhasePatchL1Continuity

/-! Actual finite signed patch densities are continuous in L1 under
contour convergence in a common phase chart. Parameter origins are
fixed in the argument and disappear from the resulting density. -/

@[expose] public section

set_option maxHeartbeats 8000000
set_option maxRecDepth 6000

noncomputable section

open Complex Set Filter Topology MeasureTheory Metric
open scoped NNReal ENNReal

namespace Euler2D

theorem integrable_phaseContourPatchVorticity_of_shift {γ : ℝ≥0}
    (Z Z₀ : ContourC1Space γ) {r : ℝ} (hr : 0 < r)
    (href : ContourC1Space.lift γ Z₀ = refCircle r) (b : ℝ)
    (hsmall : ‖contourParameterShiftC1 b Z - Z₀‖ ≤ r / 4) :
    Integrable (phaseContourPatchVorticity Z) := by
  rw [← phaseContourPatchVorticity_parameterShift b Z]
  unfold phaseContourPatchVorticity
  rw [← contourC1EnclosedDomain_eq_radialFill (contourParameterShiftC1 b Z) Z₀ hr href hsmall]
  exact integrable_contourC1PatchVorticity (contourParameterShiftC1 b Z) Z₀ hr href hsmall

theorem integral_abs_phaseFiniteContourPatchVorticity_sub_le
    {γ : ℝ≥0} {ι : Type*} [Fintype ι]
    (g : ι → ℝ) (Z W : ι → ContourC1Space γ)
    (hZ : ∀ i, Integrable (phaseContourPatchVorticity (Z i)))
    (hW : ∀ i, Integrable (phaseContourPatchVorticity (W i))) :
    (∫ x : ℂ, |phaseFiniteContourPatchVorticity g Z x - phaseFiniteContourPatchVorticity g W x|) ≤
      ∑ i, |g i| * (∫ x : ℂ, |phaseContourPatchVorticity (Z i) x - phaseContourPatchVorticity (W i) x|) := by
  classical
  have hZI : Integrable (phaseFiniteContourPatchVorticity g Z) :=
    integrable_finset_sum _ (fun i _ => (hZ i).const_mul (g i))
  have hWI : Integrable (phaseFiniteContourPatchVorticity g W) :=
    integrable_finset_sum _ (fun i _ => (hW i).const_mul (g i))
  have hI : Integrable (fun x : ℂ => ∑ i, |g i| *
      |phaseContourPatchVorticity (Z i) x - phaseContourPatchVorticity (W i) x|) :=
    integrable_finset_sum _ (fun i _ => ((hZ i).sub (hW i)).abs.const_mul _)
  calc
    _ ≤ ∫ x : ℂ, ∑ i, |g i| *
        |phaseContourPatchVorticity (Z i) x - phaseContourPatchVorticity (W i) x| := by
      apply integral_mono (hZI.sub hWI).abs hI
      intro x
      change |phaseFiniteContourPatchVorticity g Z x - phaseFiniteContourPatchVorticity g W x| ≤ _
      have he : phaseFiniteContourPatchVorticity g Z x - phaseFiniteContourPatchVorticity g W x =
          ∑ i, g i * (phaseContourPatchVorticity (Z i) x - phaseContourPatchVorticity (W i) x) := by
        simp only [phaseFiniteContourPatchVorticity, mul_sub, Finset.sum_sub_distrib]
      rw [he]
      simpa only [abs_mul] using Finset.abs_sum_le_sum_abs
        (fun i => g i * (phaseContourPatchVorticity (Z i) x - phaseContourPatchVorticity (W i) x))
        Finset.univ
    _ = _ := by
      calc
        _ = ∑ i, ∫ x : ℂ, |g i| *
            |phaseContourPatchVorticity (Z i) x - phaseContourPatchVorticity (W i) x| :=
          integral_finset_sum Finset.univ (fun i _ => ((hZ i).sub (hW i)).abs.const_mul |g i|)
        _ = _ := by simp only [integral_const_mul]

theorem tendsto_phaseFiniteContourPatchVorticity_L1_of_tendsto
    {κ : Type*} {l : Filter κ} [l.IsCountablyGenerated]
    {γ : ℝ≥0} {ι : Type*} [Fintype ι]
    (g : ι → ℝ) (Z : κ → ι → ContourC1Space γ) (W Z₀ : ι → ContourC1Space γ)
    (r b : ι → ℝ) (hr : ∀ i, 0 < r i)
    (href : ∀ i, ContourC1Space.lift γ (Z₀ i) = refCircle (r i))
    (hW : ∀ i, ‖contourParameterShiftC1 (b i) (W i) - Z₀ i‖ ≤ r i / 4)
    (hZ : ∀ n i, ‖contourParameterShiftC1 (b i) (Z n i) - Z₀ i‖ ≤ r i / 4)
    (hlim : ∀ i, Tendsto (fun n => Z n i) l (𝓝 (W i))) :
    Tendsto (fun n => ∫ x : ℂ,
      |phaseFiniteContourPatchVorticity g (Z n) x - phaseFiniteContourPatchVorticity g W x|) l (𝓝 0) := by
  classical
  have hL (i : ι) : Tendsto (fun n => ∫ x : ℂ,
      |phaseContourPatchVorticity (Z n i) x - phaseContourPatchVorticity (W i) x|) l (𝓝 0) := by
    have hh := tendsto_phaseContourPatchVorticity_L1_of_tendsto
      (fun n => contourParameterShiftC1 (b i) (Z n i))
      (contourParameterShiftC1 (b i) (W i)) (Z₀ i) (hr i) (href i) (hW i) (fun n => hZ n i)
      (((contourParameterShiftC1CLM γ (b i)).continuous.tendsto (W i)).comp (hlim i))
    simpa only [phaseContourPatchVorticity_parameterShift] using hh
  have hSum : Tendsto (fun n => ∑ i, |g i| * (∫ x : ℂ,
      |phaseContourPatchVorticity (Z n i) x - phaseContourPatchVorticity (W i) x|)) l (𝓝 0) := by
    simpa only [mul_zero, Finset.sum_const_zero] using
      tendsto_finset_sum Finset.univ (fun i _ => (hL i).const_mul |g i|)
  apply squeeze_zero (fun n => integral_nonneg (fun x => abs_nonneg _)) ?_ hSum
  intro n
  exact integral_abs_phaseFiniteContourPatchVorticity_sub_le g (Z n) W
    (fun i => integrable_phaseContourPatchVorticity_of_shift (Z n i) (Z₀ i) (hr i) (href i) (b i) (hZ n i))
    (fun i => integrable_phaseContourPatchVorticity_of_shift (W i) (Z₀ i) (hr i) (href i) (b i) (hW i))

theorem exists_phaseFiniteContourPatchVorticity_L1_neighborhood
    {γ : ℝ≥0} {ι : Type*} [Fintype ι]
    (g : ι → ℝ) (W Z₀ : ι → ContourC1Space γ) (r b : ι → ℝ)
    (hr : ∀ i, 0 < r i)
    (href : ∀ i, ContourC1Space.lift γ (Z₀ i) = refCircle (r i))
    (hW : ∀ i, ‖contourParameterShiftC1 (b i) (W i) - Z₀ i‖ < r i / 4)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ Z : ι → ContourC1Space γ, ‖Z - W‖ < δ →
      (∫ x : ℂ, |phaseFiniteContourPatchVorticity g Z x - phaseFiniteContourPatchVorticity g W x|) < ε := by
  classical
  let U := {Z : ι → ContourC1Space γ | ∀ i,
    ‖contourParameterShiftC1 (b i) (Z i) - Z₀ i‖ ≤ r i / 4}
  let WU : U := ⟨W, fun i => (hW i).le⟩
  have hlim (i : ι) : Tendsto (fun Z : U => Z.val i) (𝓝 WU) (𝓝 (W i)) :=
    ((continuous_apply i).comp continuous_subtype_val).tendsto WU
  have hL := tendsto_phaseFiniteContourPatchVorticity_L1_of_tendsto g
    (fun Z : U => Z.val) W Z₀ r b hr href (fun i => (hW i).le) (fun Z => Z.property) hlim
  obtain ⟨δ, hδ, hδspec⟩ := Metric.eventually_nhds_iff.mp (hL.eventually (eventually_lt_nhds hε))
  have hUnear : ∀ᶠ Z : ι → ContourC1Space γ in 𝓝 W, Z ∈ U := by
    change ∀ᶠ Z : ι → ContourC1Space γ in 𝓝 W, ∀ i,
      ‖contourParameterShiftC1 (b i) (Z i) - Z₀ i‖ ≤ r i / 4
    rw [Filter.eventually_all]
    intro i
    have hc : Continuous (fun Z : ι → ContourC1Space γ =>
        ‖contourParameterShiftC1 (b i) (Z i) - Z₀ i‖) :=
      (((contourParameterShiftC1CLM γ (b i)).continuous.comp (continuous_apply i)).sub continuous_const).norm
    exact ((hc.tendsto W).eventually (eventually_lt_nhds (hW i))).mono (fun Z hZ => hZ.le)
  obtain ⟨η, hη, hηspec⟩ := Metric.eventually_nhds_iff.mp hUnear
  refine ⟨min δ η, lt_min hδ hη, ?_⟩
  intro Z hZW
  have hnear : dist Z W < η := by
    simpa only [dist_eq_norm] using hZW.trans_le (min_le_right _ _)
  have hZU : Z ∈ U := hηspec hnear
  apply hδspec (y := (⟨Z, hZU⟩ : U))
  simpa only [Subtype.dist_eq, dist_eq_norm] using hZW.trans_le (min_le_left _ _)

end Euler2D

end
