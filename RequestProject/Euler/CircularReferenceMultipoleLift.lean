module

public import RequestProject.Euler.CircularFourthMomentReferenceForcing
public import RequestProject.Euler.ComplexFourthMultipoleStability

/-! The mode-five reference forcing is pointwise the actual
fourth-moment exterior velocity evaluated on the original circles. -/

@[expose] public section

set_option maxHeartbeats 6000000
set_option maxRecDepth 5500

noncomputable section

open Complex Set
open scoped NNReal ComplexConjugate

namespace Euler2D

theorem refCircle_eq_radius_character (r θ : ℝ) :
    refCircle r θ = (r : ℂ) * contourCircleCharacter 1 θ := by
  simp only [refCircle, contourCircleCharacter, Int.cast_one, one_mul]

theorem norm_refCircle_eq_abs_radius (r θ : ℝ) : ‖refCircle r θ‖ = |r| := by
  rw [refCircle_eq_radius_character, norm_mul, norm_contourCircleCharacter, mul_one,
    Complex.norm_real, Real.norm_eq_abs]

theorem inv_conj_refCircle_pow_five (r θ : ℝ) :
    (conj (refCircle r θ) ^ 5)⁻¹ = ((r : ℂ) ^ 5)⁻¹ * contourCircleCharacter 5 θ := by
  have hpow : contourCircleCharacter (-1) θ ^ 5 = contourCircleCharacter (-5) θ := by
    simp only [contourCircleCharacter, ← Complex.exp_nat_mul]
    congr 1
    norm_num
    <;> ring
  rw [refCircle_eq_radius_character, map_mul, Complex.conj_ofReal, conj_contourCircleCharacter,
    mul_pow, hpow, mul_inv_rev, inv_contourCircleCharacter]
  norm_num
  <;> ring

theorem lift_circularFourthMomentReferenceForcing_eq_multipole {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : γ ≤ 1) (M : ℂ) (i : Fin 2) (θ : ℝ) :
    LittleContourSpace.lift γ (circularFourthMomentReferenceForcing hγ hγ1 M i) θ =
      fourthMomentVelocityField M (refCircle (circularContourRadii i) θ) := by
  change LittleContourSpace.lift γ (littleContourFourierMode hγ hγ1 5 _) θ = _
  rw [lift_littleContourFourierMode, fourthMomentVelocityField, inv_conj_refCircle_pow_five]
  ring

end Euler2D

end
