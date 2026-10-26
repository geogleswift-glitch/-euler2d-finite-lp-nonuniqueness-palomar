module

public import RequestProject.Euler.CircularFinitePrefixMaterialTube
public import RequestProject.Euler.CircularAncientAreaTransport

/-! Actual domain transport preserves each original physical area.
The original ancient initial sample is retained at the original cutoff. -/

@[expose] public section

set_option maxHeartbeats 4500000

noncomputable section

open Complex Set Filter Topology MeasureTheory Metric
open scoped NNReal ENNReal

namespace Euler2D

theorem contourArea_real_smul {γ : ℝ≥0} (r : ℝ) (Z : ContourC1Space γ) :
    contourArea γ (r • Z) = r ^ 2 * contourArea γ Z := by
  rw [contourArea_eq_diagonal]
  simp only [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

theorem area_physical_radialFill_of_shift {γ : ℝ≥0} (Z Z₀ : ContourC1Space γ)
    {r : ℝ} (hr : 0 < r) (href : ContourC1Space.lift γ Z₀ = refCircle r)
    (β : ℝ) (hsmall : ‖contourParameterShiftC1 β Z - Z₀‖ ≤ r / 4) :
    volume.real (complexTorusPoint '' contourRadialFill (ContourC1Space.lift γ Z)) =
      contourArea γ Z := by
  have hopen := isOpen_contourRadialFill_of_shift Z Z₀ hr href β hsmall
  have himage : IsOpen (complexTorusPoint '' contourRadialFill (ContourC1Space.lift γ Z)) :=
    centeredComplexHomeomorph.isOpenMap _ hopen
  have hm := measurePreserving_centeredComplexHomeomorph.measure_preimage
    himage.measurableSet.nullMeasurableSet
  change volume (centeredComplexHomeomorph ⁻¹'
    (centeredComplexHomeomorph '' contourRadialFill (ContourC1Space.lift γ Z))) =
      volume (complexTorusPoint '' contourRadialFill (ContourC1Space.lift γ Z)) at hm
  rw [Set.preimage_image_eq _ centeredComplexHomeomorph.injective] at hm
  calc
    _ = volume.real (contourRadialFill (ContourC1Space.lift γ Z)) :=
      congrArg ENNReal.toReal hm.symm
    _ = _ := area_contourRadialFill_of_shift Z Z₀ hr href β hsmall

namespace BoundedEulerParticleSystem

variable {f : Lp ℝ 2 μT} {T : ℝ} (S : BoundedEulerParticleSystem f T)

theorem contourArea_eq_of_material_domain_image {γ : ℝ≥0}
    (Zstart Zend Z₀ : ContourC1Space γ) {r : ℝ} (hr : 0 < r)
    (href : ContourC1Space.lift γ Z₀ = refCircle r) (βstart βend : ℝ)
    (hstart : ‖contourParameterShiftC1 βstart Zstart - Z₀‖ ≤ r / 4)
    (hend : ‖contourParameterShiftC1 βend Zend - Z₀‖ ≤ r / 4)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T)
    (hstartbox : complexTorusPoint '' contourRadialFill (ContourC1Space.lift γ Zstart) ⊆ torusBox)
    (hendbox : complexTorusPoint '' contourRadialFill (ContourC1Space.lift γ Zend) ⊆ torusBox)
    (himages : S.forward t '' (complexTorusPoint '' contourRadialFill (ContourC1Space.lift γ Zstart)) =
      complexTorusPoint '' contourRadialFill (ContourC1Space.lift γ Zend)) :
    contourArea γ Zend = contourArea γ Zstart := by
  have hopen := isOpen_contourRadialFill_of_shift Zstart Z₀ hr href βstart hstart
  have hstartmeas : MeasurableSet
      (complexTorusPoint '' contourRadialFill (ContourC1Space.lift γ Zstart)) :=
    (centeredComplexHomeomorph.isOpenMap _ hopen).measurableSet
  have hm := S.volume_image_patch t ht hstartmeas hstartbox (by rw [himages]; exact hendbox)
  rw [himages] at hm
  calc
    _ = volume.real (complexTorusPoint '' contourRadialFill (ContourC1Space.lift γ Zend)) :=
      (area_physical_radialFill_of_shift Zend Z₀ hr href βend hend).symm
    _ = volume.real (complexTorusPoint '' contourRadialFill (ContourC1Space.lift γ Zstart)) :=
      congrArg ENNReal.toReal hm
    _ = _ := area_physical_radialFill_of_shift Zstart Z₀ hr href βstart hstart

end BoundedEulerParticleSystem

namespace CircularMaterialTransferProfile

variable {γ : ℝ≥0} {hγ : 0 < γ} {hγ1 : (γ : ℝ) < 1}
    (P : CircularMaterialTransferProfile hγ hγ1)

theorem finiteCircularInitial_area {s R ρ : ℝ} (hs : s ≤ 0)
    (N : ℕ) (p : FiniteCircularIndex N) :
    littleContourArea γ (finiteCircularInitialContours hγ hγ1 R ρ (P.ancient s) N p) =
      Real.pi * (circularContourRadii p.2 * radScale R ρ p.1) ^ 2 := by
  unfold finiteCircularInitialContours
  change contourArea γ (radScale R ρ p.1 • _) = _
  rw [contourArea_real_smul]
  split_ifs
  · change radScale R ρ p.1 ^ 2 * littleContourArea γ (P.ancient s p.2) = _
    rw [P.ancient_area s hs]
    ring
  · have hc : littleContourArea γ (littleCircularReference hγ hγ1 p.2) =
        Real.pi * circularContourRadii p.2 ^ 2 := by
      have ha := loopArea_littleAreaChart hγ hγ1.le (circularContourRadii_bounds p.2).1.ne'
        (0 : LittleContourSpace γ) (by simp) (by rw [littleContourArea_zero]; positivity)
      change loopArea (LittleContourSpace.lift γ
        (littleReferenceCircle hγ hγ1.le (circularContourRadii p.2))) = _
      exact (congrArg (fun Z : LittleContourSpace γ => loopArea (LittleContourSpace.lift γ Z))
        (littleAreaChart_zero hγ hγ1.le (circularContourRadii p.2))).symm.trans ha
    change radScale R ρ p.1 ^ 2 * littleContourArea γ (littleCircularReference hγ hγ1 p.2) = _
    rw [hc]
    ring

theorem finiteOuterMaterialTube_area {s R ρ η : ℝ} (hs : s ≤ 0)
    (hR : 0 < R) (hρ : 0 < ρ) (hη : 0 ≤ η) (hηa : η ≤ cellA / 4)
    (hancient : ∀ i, ‖(P.ancient s i).val - circularReferenceC1 hγ hγ1 i‖ ≤ η)
    {N k : ℕ} {f : Lp ℝ 2 μT} {T : ℝ} {S : BoundedEulerParticleSystem f T}
    {t c δ : ℝ} (ht : t ∈ Icc (0 : ℝ) T)
    (G : P.FiniteOuterMaterialTube s R ρ N k S t c δ)
    (j : Fin (N + 1)) (hj : (j : ℕ) ≤ k) (i : Fin 2) :
    contourArea γ (G.contours (j, i)) =
      Real.pi * (circularContourRadii i * radScale R ρ j) ^ 2 := by
  let Zstart := (finiteCircularInitialContours hγ hγ1 R ρ (P.ancient s) N (j, i)).val
  let Z₀ := finiteCircularReferenceC1 hγ hγ1 R ρ (j, i)
  let r := circularContourRadii i * radScale R ρ j
  have hr : 0 < r := mul_pos (circularContourRadii_bounds i).1 (radScale_pos hR hρ j)
  have href : ContourC1Space.lift γ Z₀ = refCircle r := by
    simpa only [Z₀, r, finiteCircularInterfaceRadius, mul_comm] using
      lift_finiteCircularReferenceC1 hγ hγ1 R ρ (j, i)
  have hstart : ‖contourParameterShiftC1 0 Zstart - Z₀‖ ≤ r / 4 := by
    rw [contourParameterShiftC1_zero]
    have hn := finiteCircular_initial_close hγ hγ1 hR hρ hη (P.ancient s) hancient N (j, i)
    have he : η ≤ circularContourRadii i / 4 :=
      hηa.trans (by linarith [(circularContourRadii_bounds i).2.1])
    have hm := mul_le_mul_of_nonneg_right he (radScale_pos hR hρ j).le
    exact hn.trans (by dsimp only [r]; nlinarith only [hm])
  have hZend : ‖contourParameterShiftC1 (G.shifts (j, i)) (G.contours (j, i)) - Z₀‖ ≤ r / 4 := by
    have he : G.reference (j, i) = Z₀ := by
      apply ContourC1Space.ext
      intro x
      obtain ⟨θ, rfl⟩ := QuotientAddGroup.mk_surjective x
      exact congrFun ((G.reference_lift j hj i).trans href.symm) θ
    rw [← he]
    exact G.quarter_tube j hj i
  have ha := S.contourArea_eq_of_material_domain_image Zstart (G.contours (j, i)) Z₀ hr href
    0 (G.shifts (j, i)) hstart hZend ht (G.initial_box j hj i) (G.current_box j hj i) (G.images j hj i)
  exact ha.trans (P.finiteCircularInitial_area hs N (j, i))

end CircularMaterialTransferProfile
end Euler2D

end
