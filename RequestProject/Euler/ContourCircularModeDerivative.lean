module

public import RequestProject.Euler.ContourCircularModeVariation
public import RequestProject.Euler.ContourSelfIntegralFirstVariation
public import RequestProject.Euler.ContourCrossFirstVariation

/-! The computed circular mode integral is the actual Fréchet
derivative of the original contour self/cross integral. -/

@[expose] public section

noncomputable section

open Complex Set MeasureTheory
open scoped NNReal ContDiff

namespace Euler2D

local instance (priority := 2000) circularModeDerivative_group (γ : ℝ≥0) :
    NormedAddCommGroup (ContourC1Space γ) := Submodule.normedAddCommGroup (contourC1GraphSubmodule γ)
local instance (priority := 2000) circularModeDerivative_space (γ : ℝ≥0) :
    NormedSpace ℝ (ContourC1Space γ) := Submodule.normedSpace (contourC1GraphSubmodule γ)

def circularReferenceContourC1 {γ : ℝ≥0} (hγ : 0 < γ) (hγ1 : γ ≤ 1) (r : ℝ) : ContourC1Space γ :=
  (littleReferenceCircle hγ hγ1 r).val

def circularFourierContourC1 {γ : ℝ≥0} (hγ : 0 < γ) (hγ1 : γ ≤ 1) (n : ℤ) (a : ℂ) : ContourC1Space γ :=
  (littleContourFourierMode hγ hγ1 n a).val

@[simp] theorem lift_circularReferenceContourC1 {γ : ℝ≥0} (hγ : 0 < γ) (hγ1 : γ ≤ 1) (r : ℝ) :
    ContourC1Space.lift γ (circularReferenceContourC1 hγ hγ1 r) = refCircle r := rfl

@[simp] theorem lift_circularFourierContourC1 {γ : ℝ≥0} (hγ : 0 < γ) (hγ1 : γ ≤ 1) (n : ℤ) (a : ℂ) :
    ContourC1Space.lift γ (circularFourierContourC1 hγ hγ1 n a) =
      fun θ => a * contourCircleCharacter n θ := rfl

theorem deriv_lift_circularFourierContourC1 {γ : ℝ≥0} (hγ : 0 < γ) (hγ1 : γ ≤ 1)
    (n : ℤ) (a : ℂ) (θ : ℝ) :
    deriv (ContourC1Space.lift γ (circularFourierContourC1 hγ hγ1 n a)) θ =
      a * ((n : ℂ) * I * contourCircleCharacter n θ) :=
  deriv_lift_littleContourFourierMode hγ hγ1 n a θ

theorem hasPositiveChordArc_circularReferenceContourC1 {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : γ ≤ 1) {r : ℝ} (hr : 0 < r) :
    ContourC1Space.HasPositiveChordArc (circularReferenceContourC1 hγ hγ1 r) := by
  refine ⟨2 * r / Real.pi, div_pos (by positivity) Real.pi_pos, ?_⟩
  intro θ τ hτ
  have hh := contourC1_chord_lower_of_norm_sub
    (circularReferenceContourC1 hγ hγ1 r) (circularReferenceContourC1 hγ hγ1 r)
      hr.le rfl θ (abs_le.mp hτ)
  simpa only [sub_self, norm_zero, sub_zero] using hh

theorem separated_circularReferenceContours {γ : ℝ≥0} (hγ : 0 < γ) (hγ1 : γ ≤ 1)
    {r s : ℝ} (hr : 0 < r) (hs : 0 < s) (hrs : r ≠ s) :
    ∃ σ > 0, ContourCrossSeparated (circularReferenceContourC1 hγ hγ1 r)
      (circularReferenceContourC1 hγ hγ1 s) σ := by
  refine ⟨|r - s|, abs_pos.mpr (sub_ne_zero.mpr hrs), ?_⟩
  intro x y
  obtain ⟨θ, rfl⟩ := QuotientAddGroup.mk_surjective x
  obtain ⟨φ, rfl⟩ := QuotientAddGroup.mk_surjective y
  change |r - s| ≤ ‖refCircle r θ - refCircle s φ‖
  have hn (d α : ℝ) (hd : 0 ≤ d) : ‖refCircle d α‖ = d := by
    rw [refCircle, norm_mul, Complex.norm_of_nonneg hd, Complex.norm_exp_ofReal_mul_I, mul_one]
  simpa only [hn r θ hr.le, hn s φ hs.le] using abs_norm_sub_norm_le (refCircle r θ) (refCircle s φ)

set_option maxHeartbeats 600000 in
theorem fderiv_selfLogIntegral_reference_mode_zero {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : γ ≤ 1) {r : ℝ} (hr : 0 < r) (n : ℤ) (a : ℂ) :
    fderiv ℝ (fun W : ContourC1Space γ => ContourC1Space.selfLogIntegral W 0)
      (circularReferenceContourC1 hγ hγ1 r) (circularFourierContourC1 hγ hγ1 n a) =
      circularContourModeVariation r r n a a := by
  rw [fderiv_selfLogIntegral_fixed_apply hγ 0 _ _
    (hasPositiveChordArc_circularReferenceContourC1 hγ hγ1 hr)]
  have hab : (-Real.pi : ℝ) ≤ Real.pi := by linarith [Real.pi_pos]
  rw [circularContourModeVariation, intervalIntegral.integral_of_le hab, ← integral_Icc_eq_integral_Ioc]
  apply integral_congr_ae
  filter_upwards [] with θ
  rw [deriv_lift_circularFourierContourC1]
  simp only [lift_circularReferenceContourC1, lift_circularFourierContourC1,
    deriv_refCircle, zero_add,
    contourCircleCharacter_at_zero, mul_one, refCircle, contourCircleCharacter,
    Int.cast_one, one_mul, Complex.ofReal_zero, zero_mul, Complex.exp_zero, Complex.real_smul]
  ring_nf
  simp only [Complex.exp_zero, mul_one, sub_eq_add_neg, add_comm]

set_option maxHeartbeats 600000 in
theorem fderiv_crossLogIntegral_reference_mode_zero {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : γ ≤ 1) {r s : ℝ}
    (hr : 0 < r) (hs : 0 < s) (hrs : r ≠ s) (n : ℤ) (a b : ℂ) :
    fderiv ℝ (fun p : ContourC1Space γ × ContourC1Space γ => contourC1CrossLogIntegral p.1 p.2 0)
      (circularReferenceContourC1 hγ hγ1 r, circularReferenceContourC1 hγ hγ1 s)
      (circularFourierContourC1 hγ hγ1 n a, circularFourierContourC1 hγ hγ1 n b) =
      circularContourModeVariation r s n a b := by
  have hshape := fderiv_contourC1CrossLogIntegral_fixed_apply hγ hγ1 0
    (circularReferenceContourC1 hγ hγ1 r, circularReferenceContourC1 hγ hγ1 s)
    (circularFourierContourC1 hγ hγ1 n a, circularFourierContourC1 hγ hγ1 n b)
    (separated_circularReferenceContours hγ hγ1 hr hs hrs)
  rw [hshape]
  have hab : (-Real.pi : ℝ) ≤ Real.pi := by linarith [Real.pi_pos]
  rw [circularContourModeVariation, intervalIntegral.integral_of_le hab, ← integral_Icc_eq_integral_Ioc]
  apply integral_congr_ae
  filter_upwards [] with θ
  rw [deriv_lift_circularFourierContourC1]
  simp only [lift_circularReferenceContourC1, lift_circularFourierContourC1,
    deriv_refCircle,
    contourCircleCharacter_at_zero, mul_one, refCircle, contourCircleCharacter,
    Int.cast_one, one_mul, Complex.ofReal_zero, zero_mul, Complex.exp_zero, Complex.real_smul]
  ring_nf
  simp only [Complex.exp_zero, mul_one, sub_eq_add_neg, add_comm]

end Euler2D

end
