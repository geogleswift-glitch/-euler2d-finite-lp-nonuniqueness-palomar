module

public import RequestProject.Euler.CircularPhaseExteriorForcing
public import RequestProject.Euler.ExteriorFieldDerivatives

/-! Actual exterior forcing derivatives for the physical cell,
including the first derivative after evaluation on a target contour.
All quantities are original volume and boundary integrals. -/

@[expose] public section

set_option maxHeartbeats 2500000

noncomputable section

open Complex ComplexConjugate Set MeasureTheory
open scoped NNReal

namespace Euler2D

theorem exteriorFourthRemainder_scaledCircular_eq {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1) {Z : Fin 2 → LittleContourSpace γ}
    (hZ : Z ∈ circularQuarterPhaseDomain hγ hγ1) (A : ℝ) {r : ℝ} (hr : 0 < r) (x : ℂ) :
    exteriorFourthRemainder (scaledComplexDensity A r (circularPhasePatchVorticity Z)) x =
      velocityC (scaledComplexDensity A r (circularPhasePatchVorticity Z)) x -
        I / (2 * Real.pi) * ((A : ℂ) * (r : ℂ) ^ 6 * circularBoundaryFourthMoment Z) *
          (conj x ^ 5)⁻¹ := by
  rw [exteriorFourthRemainder, momentN_scaledComplexDensity A hr,
    momentN_circularPhasePatchVorticity hγ hγ1 hZ]

section ActualCell

variable {γ : ℝ≥0} (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1)
  {Z : Fin 2 → LittleContourSpace γ} (hZ : Z ∈ circularQuarterPhaseDomain hγ hγ1)
  (harea : ∀ i, littleContourArea γ (Z i) = Real.pi * circularContourRadii i ^ 2)
  (hfour : ∀ i, Z i ∈ fourfoldLittleContourSubmodule γ)
  (A : ℝ) {r : ℝ} (hr : 0 < r)

include hγ hγ1 hZ hr

private theorem actualScaledCell_supp :
    ∀ y, r * (5 / 4) < ‖y‖ → scaledComplexDensity A r (circularPhasePatchVorticity Z) y = 0 := by
  apply scaledComplexDensity_support (S := 5 / 4) _ hr A
  intro z hz
  by_contra hn
  exact (not_le.mpr hz) (norm_le_of_circularPhasePatchVorticity_ne_zero hγ hγ1 hZ hn)

include harea in
private theorem actualScaledCell_mass :
    (∫ y, scaledComplexDensity A r (circularPhasePatchVorticity Z) y) = 0 := by
  rw [integral_scaledComplexDensity A hr.le,
    integral_circularPhasePatchVorticity_zero hγ hγ1 hZ harea, mul_zero]

include harea hfour in
theorem norm_iteratedDeriv_circularPhasePatch_scaled_exterior
    {x : ℂ} (hx : 5 * r ≤ ‖x‖) (m : ℕ) :
    ‖iteratedDeriv m
      (exteriorFourthRemainderCauchy (scaledComplexDensity A r (circularPhasePatchVorticity Z))) x‖ ≤
      (m.factorial : ℝ) * (8 / (15 * Real.pi) *
        (|A| * r ^ 10 * (5 / 4 : ℝ) ^ 8 *
          finiteContourPatchMassBound circularContourStrengths circularContourRadii) /
            (‖x‖ / 2) ^ 9) / (‖x‖ / 2) ^ m := by
  have hx0 : x ≠ 0 := norm_pos_iff.mp ((by positivity : (0 : ℝ) < 5 * r).trans_le hx)
  have hb := norm_iteratedDeriv_exteriorFourthRemainderCauchy (S := r * (5 / 4))
    (by positivity) (integrable_scaledComplexDensity
      (integrable_circularPhasePatchVorticity hγ hγ1 hZ) A hr.ne')
    (actualScaledCell_supp hγ hγ1 hZ A hr)
    (actualScaledCell_mass hγ hγ1 hZ harea A hr)
    (scaledComplexDensity_fourfold (circularPhasePatchVorticity_fourfold Z hfour) A r)
    hx0 (by nlinarith) m
  rw [absMoment_scaledComplexDensity A hr] at hb
  norm_num only [Nat.reduceAdd] at hb
  refine hb.trans ?_
  have hm := circularPhasePatch_absMoment_le hγ hγ1 hZ 8
  let C := (m.factorial : ℝ) * (8 / (15 * Real.pi) * (|A| * r ^ 10) /
    (‖x‖ / 2) ^ 9) / (‖x‖ / 2) ^ m
  have hC : 0 ≤ C := by dsimp [C]; positivity
  convert mul_le_mul_of_nonneg_left hm hC using 1 <;> dsimp [C] <;> ring

include harea hfour in
/-- A genuine real spatial derivative of the original velocity remainder. -/
theorem norm_fderiv_circularPhasePatch_scaled_exterior
    {x : ℂ} (hx : 5 * r ≤ ‖x‖) :
    ‖fderiv ℝ
      (exteriorFourthRemainder (scaledComplexDensity A r (circularPhasePatchVorticity Z))) x‖ ≤
      (8 / (15 * Real.pi) *
        (|A| * r ^ 10 * (5 / 4 : ℝ) ^ 8 *
          finiteContourPatchMassBound circularContourStrengths circularContourRadii) /
            (‖x‖ / 2) ^ 9) / (‖x‖ / 2) := by
  have hx0 : x ≠ 0 := norm_pos_iff.mp ((by positivity : (0 : ℝ) < 5 * r).trans_le hx)
  have hb := norm_fderiv_exteriorFourthRemainder (S := r * (5 / 4))
    (by positivity) (integrable_scaledComplexDensity
      (integrable_circularPhasePatchVorticity hγ hγ1 hZ) A hr.ne')
    (actualScaledCell_supp hγ hγ1 hZ A hr)
    (actualScaledCell_mass hγ hγ1 hZ harea A hr)
    (scaledComplexDensity_fourfold (circularPhasePatchVorticity_fourfold Z hfour) A r)
    hx0 (by nlinarith)
  rw [absMoment_scaledComplexDensity A hr] at hb
  norm_num only [Nat.reduceAdd] at hb
  refine hb.trans ?_
  have hm := circularPhasePatch_absMoment_le hγ hγ1 hZ 8
  let C := (8 / (15 * Real.pi) * (|A| * r ^ 10) / (‖x‖ / 2) ^ 9) / (‖x‖ / 2)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  convert mul_le_mul_of_nonneg_left hm hC using 1 <;> dsimp [C] <;> ring

/-- The derivative after evaluating the true source field on the true
target curve is the chain-rule derivative and obeys the actual
eighth-moment error estimate. -/
theorem circularPhasePatch_scaled_contour_hasDerivAt
    {target : ℝ → ℂ} {θ : ℝ} {v : ℂ} (htarget : HasDerivAt target v θ)
    (hsep : 5 * r ≤ ‖target θ‖) :
    HasDerivAt
      (fun s => exteriorFourthRemainder
        (scaledComplexDensity A r (circularPhasePatchVorticity Z)) (target s))
      ((fderiv ℝ (exteriorFourthRemainder
        (scaledComplexDensity A r (circularPhasePatchVorticity Z))) (target θ)) v) θ := by
  have hx0 : target θ ≠ 0 := norm_pos_iff.mp ((by positivity : (0 : ℝ) < 5 * r).trans_le hsep)
  exact (differentiableAt_exteriorFourthRemainder
    (integrable_scaledComplexDensity (integrable_circularPhasePatchVorticity hγ hγ1 hZ) A hr.ne')
    (actualScaledCell_supp hγ hγ1 hZ A hr) (by nlinarith) hx0).hasFDerivAt.comp_hasDerivAt θ htarget

include harea hfour in
theorem norm_deriv_circularPhasePatch_scaled_contour_remainder
    {target : ℝ → ℂ} {θ : ℝ} {v : ℂ} (htarget : HasDerivAt target v θ)
    (hsep : 5 * r ≤ ‖target θ‖) :
    ‖deriv (fun s => exteriorFourthRemainder
      (scaledComplexDensity A r (circularPhasePatchVorticity Z)) (target s)) θ‖ ≤
      ((8 / (15 * Real.pi) *
        (|A| * r ^ 10 * (5 / 4 : ℝ) ^ 8 *
          finiteContourPatchMassBound circularContourStrengths circularContourRadii) /
            (‖target θ‖ / 2) ^ 9) / (‖target θ‖ / 2)) * ‖v‖ := by
  rw [(circularPhasePatch_scaled_contour_hasDerivAt hγ hγ1 hZ A hr htarget hsep).deriv]
  exact (ContinuousLinearMap.le_opNorm _ _).trans
    (mul_le_mul_of_nonneg_right
      (norm_fderiv_circularPhasePatch_scaled_exterior hγ hγ1 hZ harea hfour A hr hsep) (norm_nonneg _))

end ActualCell

end Euler2D

end
