module

public import RequestProject.Euler.CircularMaterialTransferProfile
public import RequestProject.Euler.CircularPhaseExteriorDerivatives

/-! The same full-time physical cell that defines the proven Laplace
profile drives the actual exterior Biot--Savart field. Its leading
coefficient is precisely that profile's moment; the spatial derivative
remainders are controlled by its true support and conserved mass. -/

@[expose] public section

set_option maxHeartbeats 2500000

noncomputable section

open Complex ComplexConjugate Set MeasureTheory
open scoped NNReal

namespace Euler2D.CircularMaterialTransferProfile

variable {γ : ℝ≥0} {hγ : 0 < γ} {hγ1 : (γ : ℝ) < 1}
  (P : CircularMaterialTransferProfile hγ hγ1)

def physicalVorticity (t : ℝ) : ℂ → ℝ :=
  if t ≤ 0 then circularPhasePatchVorticity (P.ancient t) else P.positiveComplexVorticity t

def physicalSupportRadius (t : ℝ) : ℝ :=
  5 / 4 + P.positiveSpeedBound * max t 0

theorem physicalSupportRadius_pos (t : ℝ) : 0 < P.physicalSupportRadius t := by
  have hp := P.positiveSpeedBound_nonneg
  have hm : 0 ≤ max t 0 := le_max_right _ _
  dsimp [physicalSupportRadius]
  positivity

theorem integrable_physicalVorticity (t : ℝ) : Integrable (P.physicalVorticity t) := by
  unfold physicalVorticity
  split_ifs with ht
  · exact integrable_circularPhasePatchVorticity hγ hγ1 (P.ancient_domain t ht)
  · exact P.integrable_positiveComplexVorticity t

theorem integral_physicalVorticity_zero (t : ℝ) : (∫ z, P.physicalVorticity t z) = 0 := by
  unfold physicalVorticity
  split_ifs with ht
  · exact integral_circularPhasePatchVorticity_zero hγ hγ1
      (P.ancient_domain t ht) (P.ancient_area t ht)
  · exact P.integral_positiveComplexVorticity_zero t

theorem physicalVorticity_fourfold (t : ℝ) (z : ℂ) :
    P.physicalVorticity t (I * z) = P.physicalVorticity t z := by
  unfold physicalVorticity
  split_ifs with ht
  · exact circularPhasePatchVorticity_fourfold _ (P.ancient_fourfold t ht) z
  · exact P.positiveComplexVorticity_fourfold t z

theorem physicalVorticity_support (t : ℝ) (z : ℂ)
    (hz : P.physicalSupportRadius t < ‖z‖) : P.physicalVorticity t z = 0 := by
  unfold physicalVorticity
  split_ifs with ht
  · have hz' : (5 / 4 : ℝ) < ‖z‖ := by
      simpa only [physicalSupportRadius, max_eq_right ht, mul_zero, add_zero] using hz
    by_contra hn
    exact (not_le.mpr hz') (norm_le_of_circularPhasePatchVorticity_ne_zero hγ hγ1
      (P.ancient_domain t ht) hn)
  · apply P.positiveComplexVorticity_support (le_of_not_ge ht)
    simpa only [physicalSupportRadius, max_eq_left (le_of_not_ge ht)] using hz

theorem integral_abs_physicalVorticity_le (t : ℝ) :
    (∫ z, |P.physicalVorticity t z|) ≤
      finiteContourPatchMassBound circularContourStrengths circularContourRadii := by
  unfold physicalVorticity
  split_ifs with ht
  · exact integral_abs_circularPhasePatchVorticity_le hγ hγ1 (P.ancient_domain t ht)
  · rw [P.integral_abs_positiveComplexVorticity t]
    have he := complexPhysicalPlane.symm.measurePreserving.integral_comp
      complexPhysicalPlane.symm.toHomeomorph.measurableEmbedding
      (fun z => |circularPhasePatchVorticity (P.ancient 0) z|)
    have hb := integral_abs_circularPhasePatchVorticity_le hγ hγ1 (P.ancient_domain 0 le_rfl)
    simpa only [circularPhasePatchPlanarVorticity, Real.norm_eq_abs] using he.trans_le hb

theorem momentN_physicalVorticity (t : ℝ) :
    momentN (P.physicalVorticity t) 4 = P.moment t := by
  unfold physicalVorticity
  split_ifs with ht
  · rw [momentN_circularPhasePatchVorticity hγ hγ1 (P.ancient_domain t ht),
      P.moment_negative t ht]
  · exact P.momentN_positiveComplexVorticity (le_of_not_ge ht)

theorem physicalVorticity_absMoment_le (t : ℝ) (m : ℕ) :
    (∫ z : ℂ, ‖z‖ ^ m * |P.physicalVorticity t z|) ≤
      P.physicalSupportRadius t ^ m *
        finiteContourPatchMassBound circularContourStrengths circularContourRadii := by
  have hR := P.physicalSupportRadius_pos t
  have hi := P.integrable_physicalVorticity t
  have hs := P.physicalVorticity_support t
  calc
    _ ≤ P.physicalSupportRadius t ^ m * ∫ z, |P.physicalVorticity t z| := by
      rw [← integral_const_mul]
      apply integral_mono (integrable_norm_pow_mul_of_supp hi hs m) (hi.abs.const_mul _) (fun z => ?_)
      by_cases hz : P.physicalVorticity t z = 0
      · simp [hz]
      have hnorm : ‖z‖ ≤ P.physicalSupportRadius t := not_lt.mp (fun h => hz (hs z h))
      exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg z) hnorm m) (abs_nonneg _)
    _ ≤ _ := mul_le_mul_of_nonneg_left (P.integral_abs_physicalVorticity_le t) (by positivity)

theorem exteriorFourthRemainder_physical_scaled_eq (t A : ℝ) {r : ℝ} (hr : 0 < r) (x : ℂ) :
    exteriorFourthRemainder (scaledComplexDensity A r (P.physicalVorticity t)) x =
      velocityC (scaledComplexDensity A r (P.physicalVorticity t)) x -
        I / (2 * Real.pi) * ((A : ℂ) * (r : ℂ) ^ 6 * P.moment t) * (conj x ^ 5)⁻¹ := by
  rw [exteriorFourthRemainder, momentN_scaledComplexDensity A hr, P.momentN_physicalVorticity]

/-- The exterior field of the actual full-time cell, with the exact
same N(t) used by the nonzero Laplace/retarded-transfer theorem. -/
theorem physical_scaled_exterior_remainder (t A : ℝ) {r : ℝ} (hr : 0 < r)
    {x : ℂ} (hx : 2 * r * P.physicalSupportRadius t ≤ ‖x‖) :
    ‖velocityC (scaledComplexDensity A r (P.physicalVorticity t)) x -
      I / (2 * Real.pi) * ((A : ℂ) * (r : ℂ) ^ 6 * P.moment t) * (conj x ^ 5)⁻¹‖ ≤
      8 / (15 * Real.pi) * (|A| * r ^ 10 * P.physicalSupportRadius t ^ 8 *
        finiteContourPatchMassBound circularContourStrengths circularContourRadii) / ‖x‖ ^ 9 := by
  have hR := P.physicalSupportRadius_pos t
  have hi := P.integrable_physicalVorticity t
  have hs := P.physicalVorticity_support t
  have hx0 : x ≠ 0 := norm_pos_iff.mp
    ((by positivity : (0 : ℝ) < 2 * r * P.physicalSupportRadius t).trans_le hx)
  have hmass : (∫ z, scaledComplexDensity A r (P.physicalVorticity t) z) = 0 := by
    rw [integral_scaledComplexDensity A hr.le, P.integral_physicalVorticity_zero t, mul_zero]
  have hb := exterior_multipole_remainder (integrable_scaledComplexDensity hi A hr.ne')
    (scaledComplexDensity_support hs hr A) hmass
    (scaledComplexDensity_fourfold (P.physicalVorticity_fourfold t) A r)
    hx0 (by nlinarith)
  rw [momentN_scaledComplexDensity A hr, P.momentN_physicalVorticity,
    absMoment_scaledComplexDensity A hr] at hb
  norm_num only [Nat.reduceAdd] at hb
  refine hb.trans ?_
  have hm := P.physicalVorticity_absMoment_le t 8
  let C := 8 / (15 * Real.pi) * (|A| * r ^ 10) / ‖x‖ ^ 9
  have hC : 0 ≤ C := by dsimp [C]; positivity
  convert mul_le_mul_of_nonneg_left hm hC using 1 <;> dsimp [C] <;> ring

theorem physical_scaled_exterior_fderiv (t A : ℝ) {r : ℝ} (hr : 0 < r)
    {x : ℂ} (hx : 4 * r * P.physicalSupportRadius t ≤ ‖x‖) :
    ‖fderiv ℝ (exteriorFourthRemainder (scaledComplexDensity A r (P.physicalVorticity t))) x‖ ≤
      (8 / (15 * Real.pi) * (|A| * r ^ 10 * P.physicalSupportRadius t ^ 8 *
        finiteContourPatchMassBound circularContourStrengths circularContourRadii) /
          (‖x‖ / 2) ^ 9) / (‖x‖ / 2) := by
  have hR := P.physicalSupportRadius_pos t
  have hi := P.integrable_physicalVorticity t
  have hs := P.physicalVorticity_support t
  have hx0 : x ≠ 0 := norm_pos_iff.mp
    ((by positivity : (0 : ℝ) < 4 * r * P.physicalSupportRadius t).trans_le hx)
  have hmass : (∫ z, scaledComplexDensity A r (P.physicalVorticity t) z) = 0 := by
    rw [integral_scaledComplexDensity A hr.le, P.integral_physicalVorticity_zero t, mul_zero]
  have hb := norm_fderiv_exteriorFourthRemainder (S := r * P.physicalSupportRadius t)
    (by positivity) (integrable_scaledComplexDensity hi A hr.ne')
    (scaledComplexDensity_support hs hr A) hmass
    (scaledComplexDensity_fourfold (P.physicalVorticity_fourfold t) A r)
    hx0 (by nlinarith)
  rw [absMoment_scaledComplexDensity A hr] at hb
  norm_num only [Nat.reduceAdd] at hb
  refine hb.trans ?_
  have hm := P.physicalVorticity_absMoment_le t 8
  let C := (8 / (15 * Real.pi) * (|A| * r ^ 10) / (‖x‖ / 2) ^ 9) / (‖x‖ / 2)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  convert mul_le_mul_of_nonneg_left hm hC using 1 <;> dsimp [C] <;> ring

theorem physical_scaled_exterior_iteratedDeriv (t A : ℝ) {r : ℝ} (hr : 0 < r)
    {x : ℂ} (hx : 4 * r * P.physicalSupportRadius t ≤ ‖x‖) (m : ℕ) :
    ‖iteratedDeriv m
      (exteriorFourthRemainderCauchy (scaledComplexDensity A r (P.physicalVorticity t))) x‖ ≤
      (m.factorial : ℝ) * (8 / (15 * Real.pi) *
        (|A| * r ^ 10 * P.physicalSupportRadius t ^ 8 *
          finiteContourPatchMassBound circularContourStrengths circularContourRadii) /
            (‖x‖ / 2) ^ 9) / (‖x‖ / 2) ^ m := by
  have hR := P.physicalSupportRadius_pos t
  have hi := P.integrable_physicalVorticity t
  have hs := P.physicalVorticity_support t
  have hx0 : x ≠ 0 := norm_pos_iff.mp
    ((by positivity : (0 : ℝ) < 4 * r * P.physicalSupportRadius t).trans_le hx)
  have hmass : (∫ z, scaledComplexDensity A r (P.physicalVorticity t) z) = 0 := by
    rw [integral_scaledComplexDensity A hr.le, P.integral_physicalVorticity_zero t, mul_zero]
  have hb := norm_iteratedDeriv_exteriorFourthRemainderCauchy (S := r * P.physicalSupportRadius t)
    (by positivity) (integrable_scaledComplexDensity hi A hr.ne')
    (scaledComplexDensity_support hs hr A) hmass
    (scaledComplexDensity_fourfold (P.physicalVorticity_fourfold t) A r)
    hx0 (by nlinarith) m
  rw [absMoment_scaledComplexDensity A hr] at hb
  norm_num only [Nat.reduceAdd] at hb
  refine hb.trans ?_
  have hm := P.physicalVorticity_absMoment_le t 8
  let C := (m.factorial : ℝ) * (8 / (15 * Real.pi) * (|A| * r ^ 10) /
    (‖x‖ / 2) ^ 9) / (‖x‖ / 2) ^ m
  have hC : 0 ≤ C := by dsimp [C]; positivity
  convert mul_le_mul_of_nonneg_left hm hC using 1 <;> dsimp [C] <;> ring

end Euler2D.CircularMaterialTransferProfile

end
