module

public import RequestProject.Euler.ContourLittleLogDerivative

/-! The literal logarithmic self-interaction as an actual C¹ Hölder map
on the genuine open near-circle neighborhood of little contours. -/

@[expose] public section

noncomputable section

open Set Filter Topology MeasureTheory
open scoped NNReal

namespace Euler2D

abbrev NearCircleLittleContour {γ : ℝ≥0} (Z₀ : ContourC1Space γ) (r : ℝ) :=
  {Z : LittleContourSpace γ // ‖Z.val - Z₀‖ < 2 * r / Real.pi}

def nearCirclePositiveContour {γ : ℝ≥0} (Z₀ : ContourC1Space γ) {r : ℝ}
    (hr : 0 < r) (href : ContourC1Space.lift γ Z₀ = refCircle r)
    (Z : NearCircleLittleContour Z₀ r) : PositiveChordContour γ :=
  ⟨Z.val.val, ⟨2 * r / Real.pi - ‖Z.val.val - Z₀‖, sub_pos.mpr Z.property,
    fun θ τ hτ => contourC1_chord_lower_of_norm_sub Z.val.val Z₀ hr.le href θ (abs_le.mp hτ)⟩⟩

theorem continuous_nearCirclePositiveContour {γ : ℝ≥0} (Z₀ : ContourC1Space γ) {r : ℝ}
    (hr : 0 < r) (href : ContourC1Space.lift γ Z₀ = refCircle r) :
    Continuous (nearCirclePositiveContour Z₀ hr href) := by
  have hc : Continuous (fun Z : NearCircleLittleContour Z₀ r => Z.val.val) :=
    (LittleContourSpace.inclusion γ).continuous.comp continuous_subtype_val
  exact hc.subtype_mk _

def nearCircleSelfLogC1 {γ : ℝ≥0} (hγ : 0 < (γ : ℝ)) (hγ1 : (γ : ℝ) < 1)
    (Z₀ : ContourC1Space γ) {r : ℝ} (hr : 0 < r)
    (href : ContourC1Space.lift γ Z₀ = refCircle r)
    (Z : NearCircleLittleContour Z₀ r) : ContourC1Space γ :=
  ContourC1Space.ofHasDerivAt
    (ContourC1Space.selfLogCircleBCF (nearCirclePositiveContour Z₀ hr href Z))
    (positiveContourLogDerivativeHolder hγ hγ1 (nearCirclePositiveContour Z₀ hr href Z))
    (hasDerivAt_contourSelfIntegral_little_near_circle Z.val Z₀ hγ hγ1
      (positiveChordConstant_pos (nearCirclePositiveContour Z₀ hr href Z))
      (hasChordArcLower_positiveChordConstant (nearCirclePositiveContour Z₀ hr href Z))
      hr href Z.property)

@[simp] theorem lift_nearCircleSelfLogC1 {γ : ℝ≥0} (hγ : 0 < (γ : ℝ)) (hγ1 : (γ : ℝ) < 1)
    (Z₀ : ContourC1Space γ) {r : ℝ} (hr : 0 < r)
    (href : ContourC1Space.lift γ Z₀ = refCircle r) (Z : NearCircleLittleContour Z₀ r) :
    ContourC1Space.lift γ (nearCircleSelfLogC1 hγ hγ1 Z₀ hr href Z) =
      ContourC1Space.selfLogIntegral Z.val.val := rfl

@[simp] theorem derivative_nearCircleSelfLogC1 {γ : ℝ≥0} (hγ : 0 < (γ : ℝ)) (hγ1 : (γ : ℝ) < 1)
    (Z₀ : ContourC1Space γ) {r : ℝ} (hr : 0 < r)
    (href : ContourC1Space.lift γ Z₀ = refCircle r) (Z : NearCircleLittleContour Z₀ r) :
    ContourC1Space.derivative γ (nearCircleSelfLogC1 hγ hγ1 Z₀ hr href Z) =
      positiveContourLogDerivativeHolder hγ hγ1 (nearCirclePositiveContour Z₀ hr href Z) := rfl

theorem norm_nearCircleSelfLogC1_le {γ : ℝ≥0} (hγ : 0 < (γ : ℝ)) (hγ1 : (γ : ℝ) < 1)
    (Z₀ : ContourC1Space γ) {r : ℝ} (hr : 0 < r)
    (href : ContourC1Space.lift γ Z₀ = refCircle r) (Z : NearCircleLittleContour Z₀ r) :
    ‖nearCircleSelfLogC1 hγ hγ1 Z₀ hr href Z‖ ≤
      max (∫ τ in (-Real.pi)..Real.pi,
        ‖Z.val.val‖ * contourLogMajorant (positiveChordConstant (nearCirclePositiveContour Z₀ hr href Z))
          ‖Z.val.val‖ τ)
        ‖positiveContourLogDerivativeHolder hγ hγ1 (nearCirclePositiveContour Z₀ hr href Z)‖ := by
  let p := nearCirclePositiveContour Z₀ hr href Z
  let B := ∫ τ in (-Real.pi)..Real.pi,
    ‖Z.val.val‖ * contourLogMajorant (positiveChordConstant p) ‖Z.val.val‖ τ
  have hb (θ : ℝ) : ‖ContourC1Space.selfLogIntegral Z.val.val θ‖ ≤ B :=
    norm_contourSelfIntegral_le (positiveChordConstant_pos p)
      (fun t => ContourC1Space.norm_eval_le Z.val.val (t : ContourCircle))
      (ContourC1Space.norm_deriv_lift_le Z.val.val) (hasChordArcLower_positiveChordConstant p) θ
  have hB : 0 ≤ B := (norm_nonneg _).trans (hb 0)
  have hnorm : ‖ContourC1Space.selfLogCircleBCF p‖ ≤ B := by
    apply (BoundedContinuousFunction.norm_le hB).mpr
    intro x
    obtain ⟨θ, rfl⟩ := QuotientAddGroup.mk_surjective x
    exact hb θ
  change max ‖ContourC1Space.selfLogCircleBCF p‖ ‖positiveContourLogDerivativeHolder hγ hγ1 p‖ ≤
    max B ‖positiveContourLogDerivativeHolder hγ hγ1 p‖
  exact max_le_max_right _ hnorm

end Euler2D

end
