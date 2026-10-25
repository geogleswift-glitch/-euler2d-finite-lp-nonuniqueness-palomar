module

public import RequestProject.Euler.CircularInnerMomentDetector
public import RequestProject.Euler.ContourAnnularPerturbation
public import RequestProject.Euler.ContourPhaseEnclosedDomain
public import RequestProject.Euler.AnnularVelocityDeparture

/-! Annular test geometry of the genuine enclosed domains of nearby
material contours. No radial-graph representation is required. -/

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 6000

noncomputable section

open Complex Set Filter Topology MeasureTheory Metric
open scoped NNReal symmDiff

namespace Euler2D

attribute [local instance 2000] innerDetectorLittle_group innerDetectorLittle_space
  innerDetectorFamily_tower phaseDomainC1_group phaseDomainC1_space

lemma circular_norm_bounds_symmDiff_of_ball_sandwich {D : Set ℂ} {r ε : ℝ}
    (hε : 0 ≤ ε) (hlo : ball 0 (r - ε) ⊆ D) (hhi : D ⊆ ball 0 (r + ε))
    {z : ℂ} (hz : z ∈ D ∆ ball 0 r) : r - ε ≤ ‖z‖ ∧ ‖z‖ ≤ r + ε := by
  rcases Set.mem_symmDiff.mp hz with ⟨hD, hnot⟩ | ⟨hB, hnot⟩
  · have hnormLo : r ≤ ‖z‖ := by simpa only [mem_ball_zero_iff, not_lt] using hnot
    exact ⟨by linarith only [hnormLo, hε], (mem_ball_zero_iff.mp (hhi hD)).le⟩
  · have hn : z ∉ ball (0 : ℂ) (r - ε) := fun h => hnot (hlo h)
    have hnormLo : r - ε ≤ ‖z‖ := by simpa only [mem_ball_zero_iff, not_lt] using hn
    exact ⟨hnormLo, by have hh := mem_ball_zero_iff.mp hB; linarith only [hh, hε]⟩

theorem circular_near_contour_actual_annular_geometry {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1) {η : ℝ} (hη : 0 < η) (hηa : η ≤ cellA / 16)
    (Z : Fin 2 → LittleContourSpace γ) (hZ : ‖Z - littleCircularReference hγ hγ1‖ ≤ η) :
    let D := contourRadialFill (LittleContourSpace.lift γ (Z 0))
    let E := contourRadialFill (LittleContourSpace.lift γ (Z 1))
    0 < 3 * η ∧ 3 * η < 1 / 5 ∧ MeasurableSet D ∧
      (∀ z ∈ D ∆ ball 0 cellA, |‖z‖ ^ 2 - 3 / 5| ≤ 3 * η) ∧
      (∀ z ∈ E ∆ ball 0 1, 2 * (3 * η) ≤ |‖z‖ ^ 2 - 3 / 5|) ∧
      momentJ D 4 = littlePatchFourthMoment hγ hγ1.le cellA cellA_pos (Z 0) := by
  have hcellUpper : cellA < 4 / 5 := by nlinarith only [cellA_sq, cellA_pos]
  have hηtwenty : η < 1 / 20 := by linarith only [hηa, hcellUpper]
  have hηr : η ≤ cellA := by linarith only [hηa, cellA_pos]
  have hRadiiLower (i : Fin 2) : cellA ≤ circularContourRadii i := by
    fin_cases i
    · exact le_rfl
    · exact cellA_lt_one.le
  have hnorm (i : Fin 2) :
      ‖(Z i).val - (littleReferenceCircle hγ hγ1.le (circularContourRadii i)).val‖ ≤ η :=
    (norm_le_pi_norm (Z - littleCircularReference hγ hγ1) i).trans hZ
  have hsmall (i : Fin 2) :
      ‖(Z i).val - (littleReferenceCircle hγ hγ1.le (circularContourRadii i)).val‖ ≤
        circularContourRadii i / 4 := (hnorm i).trans (by
    have hh := hRadiiLower i
    linarith only [hηa, hh, cellA_pos])
  have hfill (i : Fin 2) : contourRadialFill (LittleContourSpace.lift γ (Z i)) =
      contourC1EnclosedDomain (Z i).val (littleReferenceCircle hγ hγ1.le (circularContourRadii i)).val
        (growingMoment_radius_pos i) (lift_littleReferenceCircle hγ hγ1.le _) (hsmall i) :=
    (contourC1EnclosedDomain_eq_radialFill _ _ _ _ _).symm
  have hlo (i : Fin 2) : ball (0 : ℂ) (circularContourRadii i - η) ⊆
      contourRadialFill (LittleContourSpace.lift γ (Z i)) := by
    rw [hfill i]
    exact (ball_subset_ball (by linarith only [hnorm i])).trans
      (ball_subset_contourC1EnclosedDomain _ _ _ _ _)
  have hhi (i : Fin 2) : contourRadialFill (LittleContourSpace.lift γ (Z i)) ⊆
      ball (0 : ℂ) (circularContourRadii i + η) := by
    rw [hfill i]
    exact (contourC1EnclosedDomain_subset_ball _ _ _ _ _).trans
      (ball_subset_ball (by linarith only [hnorm i]))
  have hD : MeasurableSet (contourRadialFill (LittleContourSpace.lift γ (Z 0))) := by
    rw [hfill 0]
    exact (isOpen_contourC1EnclosedDomain _ _ _ _ _).measurableSet
  dsimp only
  refine ⟨by positivity, by linarith only [hηtwenty], hD, ?_, ?_, ?_⟩
  · intro z hz
    have hb : cellA - η ≤ ‖z‖ ∧ ‖z‖ ≤ cellA + η := by
      simpa only [circularContourRadii] using circular_norm_bounds_symmDiff_of_ball_sandwich hη.le (hlo 0) (hhi 0) hz
    have hsqLo := (sq_le_sq₀ (sub_nonneg.mpr hηr) (norm_nonneg z)).mpr hb.1
    have hsqHi := (sq_le_sq₀ (norm_nonneg z) (by linarith only [cellA_pos, hη])).mpr hb.2
    have hc : (2 * cellA + η) * η ≤ 3 * η :=
      mul_le_mul_of_nonneg_right (by linarith only [cellA_lt_one, hηtwenty]) hη.le
    apply abs_le.mpr
    constructor <;> nlinarith only [hsqLo, hsqHi, cellA_sq, hc, sq_nonneg η]
  · intro z hz
    have hb : 1 - η ≤ ‖z‖ ∧ ‖z‖ ≤ 1 + η := by
      simpa only [circularContourRadii] using circular_norm_bounds_symmDiff_of_ball_sandwich hη.le (hlo 1) (hhi 1) hz
    have hsqLo := (sq_le_sq₀ (by linarith only [hηtwenty]) (norm_nonneg z)).mpr hb.1
    have hh : 2 * (3 * η) ≤ ‖z‖ ^ 2 - 3 / 5 := by
      nlinarith only [hsqLo, hηtwenty.le, sq_nonneg η]
    exact hh.trans (le_abs_self _)
  · have hs0 : ‖(Z 0).val - (littleReferenceCircle hγ hγ1.le cellA).val‖ ≤ cellA / 4 := by
      simpa only [circularContourRadii] using hsmall 0
    rw [littlePatchFourthMoment, dif_pos hs0]
    exact congrArg (fun D : Set ℂ => momentJ D 4) (hfill 0)

end Euler2D

end
