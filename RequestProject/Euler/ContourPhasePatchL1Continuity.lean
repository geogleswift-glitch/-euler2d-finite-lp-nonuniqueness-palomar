module

public import RequestProject.Euler.ContourRadialFillPersistence
public import RequestProject.Euler.ContourPhaseVorticity
public import RequestProject.Euler.ContourAreaAnalytic

/-! C1 convergence of actual near-circular contours gives L1 convergence
of their genuine indicator densities. Interior persistence controls the
intersection mass; the original area functional controls total mass. -/

@[expose] public section

set_option maxHeartbeats 8000000
set_option maxRecDepth 6000

noncomputable section

open Complex Set Filter Topology MeasureTheory Metric
open scoped NNReal ENNReal

namespace Euler2D

theorem tendsto_phaseContourPatchVorticity_L1_of_tendsto
    {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated] {γ : ℝ≥0}
    (Z : ι → ContourC1Space γ) (W Z₀ : ContourC1Space γ) {r : ℝ}
    (hr : 0 < r) (href : ContourC1Space.lift γ Z₀ = refCircle r)
    (hW : ‖W - Z₀‖ ≤ r / 4) (hZ : ∀ i, ‖Z i - Z₀‖ ≤ r / 4)
    (hlim : Tendsto Z l (𝓝 W)) :
    Tendsto (fun i => ∫ x : ℂ, |phaseContourPatchVorticity (Z i) x - phaseContourPatchVorticity W x|)
      l (𝓝 0) := by
  have hOpen (U : ContourC1Space γ) (hU : ‖U - Z₀‖ ≤ r / 4) :
      IsOpen (contourRadialFill (ContourC1Space.lift γ U)) := by
    rw [← contourC1EnclosedDomain_eq_radialFill U Z₀ hr href hU]
    exact isOpen_contourC1EnclosedDomain U Z₀ hr href hU
  have hInt (U : ContourC1Space γ) (hU : ‖U - Z₀‖ ≤ r / 4) :
      Integrable (phaseContourPatchVorticity U) := by
    unfold phaseContourPatchVorticity
    rw [← contourC1EnclosedDomain_eq_radialFill U Z₀ hr href hU]
    exact integrable_contourC1PatchVorticity U Z₀ hr href hU
  have hIntegral (U : ContourC1Space γ) (hU : ‖U - Z₀‖ ≤ r / 4) :
      (∫ x : ℂ, phaseContourPatchVorticity U x) = contourArea γ U := by
    unfold phaseContourPatchVorticity
    change (∫ x : ℂ, (contourRadialFill (ContourC1Space.lift γ U)).indicator
      (1 : ℂ → ℝ) x) = contourArea γ U
    rw [integral_indicator_one (hOpen U hU).measurableSet,
      ← contourC1EnclosedDomain_eq_radialFill U Z₀ hr href hU]
    exact area_contourC1EnclosedDomain U Z₀ hr href hU
  let g : ι → ℂ → ℝ := fun i x => phaseContourPatchVorticity (Z i) x * phaseContourPatchVorticity W x
  have hGmeas (i : ι) : AEStronglyMeasurable (g i) volume :=
    (hInt (Z i) (hZ i)).aestronglyMeasurable.mul (hInt W hW).aestronglyMeasurable
  have hGbound (i : ι) : ∀ᵐ x : ℂ ∂volume, ‖g i x‖ ≤ phaseContourPatchVorticity W x := by
    apply ae_of_all
    intro x
    by_cases hz : x ∈ contourRadialFill (ContourC1Space.lift γ (Z i)) <;>
      by_cases hw : x ∈ contourRadialFill (ContourC1Space.lift γ W) <;>
      simp [g, phaseContourPatchVorticity, hz, hw]
  have hGint (i : ι) : Integrable (g i) := (hInt W hW).mono' (hGmeas i) (hGbound i)
  have hGlim : ∀ᵐ x : ℂ ∂volume, Tendsto (fun i => g i x) l (𝓝 (phaseContourPatchVorticity W x)) := by
    apply ae_of_all
    intro x
    have hevent : ∀ᶠ i in l, g i x = phaseContourPatchVorticity W x := by
      by_cases hw : x ∈ contourRadialFill (ContourC1Space.lift γ W)
      · filter_upwards [eventually_mem_contourRadialFill_of_tendsto Z W Z₀ hr href hW hZ hlim hw]
          with i hi
        simp [g, phaseContourPatchVorticity, hw, hi]
      · exact Eventually.of_forall (fun i => by simp [g, phaseContourPatchVorticity, hw])
    exact (tendsto_congr' hevent).mpr tendsto_const_nhds
  have hIG : Tendsto (fun i => ∫ x : ℂ, g i x) l (𝓝 (∫ x : ℂ, phaseContourPatchVorticity W x)) :=
    tendsto_integral_filter_of_dominated_convergence (phaseContourPatchVorticity W)
      (Eventually.of_forall hGmeas) (Eventually.of_forall hGbound) (hInt W hW) hGlim
  have hArea := ((continuous_contourArea γ).tendsto W).comp hlim
  have hFnIntegral : (fun i => ∫ x : ℂ, phaseContourPatchVorticity (Z i) x) =
      fun i => contourArea γ (Z i) := funext (fun i => hIntegral (Z i) (hZ i))
  have hWIntegral := hIntegral W hW
  have hIA : Tendsto (fun i => ∫ x : ℂ, phaseContourPatchVorticity (Z i) x) l
      (𝓝 (∫ x : ℂ, phaseContourPatchVorticity W x)) := by
    rw [hFnIntegral, hWIntegral]
    exact hArea
  have hPoint (i : ι) (x : ℂ) :
      |phaseContourPatchVorticity (Z i) x - phaseContourPatchVorticity W x| =
        phaseContourPatchVorticity (Z i) x + phaseContourPatchVorticity W x - 2 * g i x := by
    by_cases hz : x ∈ contourRadialFill (ContourC1Space.lift γ (Z i)) <;>
      by_cases hw : x ∈ contourRadialFill (ContourC1Space.lift γ W) <;>
      norm_num [g, phaseContourPatchVorticity, hz, hw]
  have hEq (i : ι) :
      (∫ x : ℂ, |phaseContourPatchVorticity (Z i) x - phaseContourPatchVorticity W x|) =
        (∫ x : ℂ, phaseContourPatchVorticity (Z i) x) +
          (∫ x : ℂ, phaseContourPatchVorticity W x) - 2 * (∫ x : ℂ, g i x) := by
    rw [integral_congr_ae (ae_of_all _ (hPoint i))]
    calc
      _ = (∫ x : ℂ, phaseContourPatchVorticity (Z i) x + phaseContourPatchVorticity W x) -
          ∫ x : ℂ, 2 * g i x :=
        integral_sub ((hInt (Z i) (hZ i)).add (hInt W hW)) ((hGint i).const_mul 2)
      _ = _ := by
        rw [integral_add (hInt (Z i) (hZ i)) (hInt W hW), integral_const_mul]
  have hL : Tendsto (fun i => (∫ x : ℂ, phaseContourPatchVorticity (Z i) x) +
      (∫ x : ℂ, phaseContourPatchVorticity W x) - 2 * (∫ x : ℂ, g i x)) l (𝓝 0) := by
    have hh := (hIA.add_const (∫ x : ℂ, phaseContourPatchVorticity W x)).sub (hIG.const_mul 2)
    simpa only [show (∫ x : ℂ, phaseContourPatchVorticity W x) +
      (∫ x : ℂ, phaseContourPatchVorticity W x) - 2 * (∫ x : ℂ, phaseContourPatchVorticity W x) = 0 by ring] using hh
  exact (tendsto_congr' (Eventually.of_forall hEq)).mpr hL

theorem exists_phaseContourPatchVorticity_L1_neighborhood {γ : ℝ≥0}
    (W Z₀ : ContourC1Space γ) {r : ℝ} (hr : 0 < r)
    (href : ContourC1Space.lift γ Z₀ = refCircle r) (hW : ‖W - Z₀‖ < r / 4)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ Z : ContourC1Space γ, ‖Z - W‖ < δ →
      (∫ x : ℂ, |phaseContourPatchVorticity Z x - phaseContourPatchVorticity W x|) < ε := by
  let U := {Z : ContourC1Space γ | ‖Z - Z₀‖ ≤ r / 4}
  let WU : U := ⟨W, hW.le⟩
  have hlim : Tendsto (fun Z : U => Z.val) (𝓝 WU) (𝓝 W) := continuous_subtype_val.tendsto WU
  have hL := tendsto_phaseContourPatchVorticity_L1_of_tendsto
    (fun Z : U => Z.val) W Z₀ hr href hW.le (fun Z => Z.property) hlim
  obtain ⟨δ, hδ, hδspec⟩ := Metric.eventually_nhds_iff.mp (hL.eventually (eventually_lt_nhds hε))
  let η := min δ ((r / 4 - ‖W - Z₀‖) / 2)
  have hη : 0 < η := lt_min hδ (half_pos (sub_pos.mpr hW))
  refine ⟨η, hη, ?_⟩
  intro Z hZW
  have hnear : ‖Z - W‖ < δ := hZW.trans_le (min_le_left _ _)
  have hsmall : ‖Z - Z₀‖ ≤ r / 4 := by
    have hηgap : η ≤ (r / 4 - ‖W - Z₀‖) / 2 := min_le_right _ _
    have htriangle := norm_sub_le_norm_sub_add_norm_sub Z W Z₀
    linarith only [htriangle, hZW, hηgap, hW]
  apply hδspec (y := (⟨Z, hsmall⟩ : U))
  simpa only [Subtype.dist_eq, dist_eq_norm] using hnear

end Euler2D

end
