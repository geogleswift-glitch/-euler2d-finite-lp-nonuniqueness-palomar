module

public import RequestProject.Euler.ComplexDensityScaling
public import RequestProject.Euler.CircularPhasePatchInvariants
public import RequestProject.Euler.CircularPhaseVelocityFlow

/-! The actual spatially scaled physical two-interface cell has the
actual boundary fourth moment as its exterior forcing coefficient.
The remainder comes from the original volume Biot--Savart integral.
This module records pointwise forcing; contour derivative bounds are
handled separately. -/

@[expose] public section

set_option maxHeartbeats 1000000

noncomputable section

open Complex ComplexConjugate Set MeasureTheory
open scoped NNReal

namespace Euler2D

theorem momentN_circularPhasePatchVorticity {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1) {Z : Fin 2 → LittleContourSpace γ}
    (hZ : Z ∈ circularQuarterPhaseDomain hγ hγ1) :
    momentN (circularPhasePatchVorticity Z) 4 = circularBoundaryFourthMoment Z := by
  change (∫ z : ℂ, (circularPhasePatchVorticity Z z : ℂ) * star z ^ 4) = _
  rw [← planarFourthMoment_complex_density]
  exact planarFourthMoment_circularPhasePatch hγ hγ1 hZ

theorem circularPhasePatch_absMoment_le {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1) {Z : Fin 2 → LittleContourSpace γ}
    (hZ : Z ∈ circularQuarterPhaseDomain hγ hγ1) (m : ℕ) :
    (∫ z : ℂ, ‖z‖ ^ m * |circularPhasePatchVorticity Z z|) ≤
      (5 / 4 : ℝ) ^ m * finiteContourPatchMassBound circularContourStrengths circularContourRadii := by
  have hi := integrable_circularPhasePatchVorticity hγ hγ1 hZ
  have hs : ∀ z, (5 / 4 : ℝ) < ‖z‖ → circularPhasePatchVorticity Z z = 0 := by
    intro z hz
    by_contra hn
    exact (not_le.mpr hz) (norm_le_of_circularPhasePatchVorticity_ne_zero hγ hγ1 hZ hn)
  calc
    _ ≤ (5 / 4 : ℝ) ^ m * ∫ z, |circularPhasePatchVorticity Z z| := by
      rw [← integral_const_mul]
      apply integral_mono (integrable_norm_pow_mul_of_supp hi hs m)
        (hi.abs.const_mul _) (fun z => ?_)
      by_cases hz : circularPhasePatchVorticity Z z = 0
      · simp [hz]
      exact mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (norm_nonneg z)
          (norm_le_of_circularPhasePatchVorticity_ne_zero hγ hγ1 hZ hz) m) (abs_nonneg _)
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (integral_abs_circularPhasePatchVorticity_le hγ hγ1 hZ) (by positivity)

theorem circularPhasePatch_scaled_exterior_remainder {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1) {Z : Fin 2 → LittleContourSpace γ}
    (hZ : Z ∈ circularQuarterPhaseDomain hγ hγ1)
    (harea : ∀ i, littleContourArea γ (Z i) = Real.pi * circularContourRadii i ^ 2)
    (hfour : ∀ i, Z i ∈ fourfoldLittleContourSubmodule γ)
    (A : ℝ) {r : ℝ} (hr : 0 < r) {x : ℂ} (hx : (5 / 2 : ℝ) * r ≤ ‖x‖) :
    ‖velocityC (scaledComplexDensity A r (circularPhasePatchVorticity Z)) x -
      I / (2 * Real.pi) * ((A : ℂ) * (r : ℂ) ^ 6 * circularBoundaryFourthMoment Z) *
        (conj x ^ 5)⁻¹‖ ≤
      8 / (15 * Real.pi) * (|A| * r ^ 10 * (5 / 4 : ℝ) ^ 8 *
        finiteContourPatchMassBound circularContourStrengths circularContourRadii) / ‖x‖ ^ 9 := by
  have hi := integrable_circularPhasePatchVorticity hγ hγ1 hZ
  have hs : ∀ z, (5 / 4 : ℝ) < ‖z‖ → circularPhasePatchVorticity Z z = 0 := by
    intro z hz
    by_contra hn
    exact (not_le.mpr hz) (norm_le_of_circularPhasePatchVorticity_ne_zero hγ hγ1 hZ hn)
  have hmass : (∫ z, scaledComplexDensity A r (circularPhasePatchVorticity Z) z) = 0 := by
    rw [integral_scaledComplexDensity A hr.le,
      integral_circularPhasePatchVorticity_zero hγ hγ1 hZ harea, mul_zero]
  have hx0 : x ≠ 0 := norm_pos_iff.mp ((by positivity : (0 : ℝ) < (5 / 2) * r).trans_le hx)
  have hb := exterior_multipole_remainder (integrable_scaledComplexDensity hi A hr.ne')
    (scaledComplexDensity_support hs hr A) hmass
    (scaledComplexDensity_fourfold (circularPhasePatchVorticity_fourfold Z hfour) A r)
    hx0 (show 2 * (r * (5 / 4)) ≤ ‖x‖ by nlinarith)
  rw [momentN_scaledComplexDensity A hr,
    momentN_circularPhasePatchVorticity hγ hγ1 hZ,
    absMoment_scaledComplexDensity A hr] at hb
  norm_num only [Nat.reduceAdd] at hb
  refine hb.trans ?_
  have hm := circularPhasePatch_absMoment_le hγ hγ1 hZ 8
  let C := 8 / (15 * Real.pi) * (|A| * r ^ 10) / ‖x‖ ^ 9
  have hC : 0 ≤ C := by dsimp [C]; positivity
  calc
    _ = C * (∫ z : ℂ, ‖z‖ ^ 8 * |circularPhasePatchVorticity Z z|) := by dsimp [C]; ring
    _ ≤ C * ((5 / 4 : ℝ) ^ 8 *
        finiteContourPatchMassBound circularContourStrengths circularContourRadii) :=
      mul_le_mul_of_nonneg_left hm hC
    _ = _ := by dsimp [C]; ring

/-- Pointwise forcing on an arbitrary actual target contour. The source
is the true indicator density, and the coefficient is its true boundary
moment, rather than an independent model forcing. -/
theorem circularPhasePatch_scaled_contour_remainder {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1) {Z : Fin 2 → LittleContourSpace γ}
    (hZ : Z ∈ circularQuarterPhaseDomain hγ hγ1)
    (harea : ∀ i, littleContourArea γ (Z i) = Real.pi * circularContourRadii i ^ 2)
    (hfour : ∀ i, Z i ∈ fourfoldLittleContourSubmodule γ)
    (A : ℝ) {r R c : ℝ} (hr : 0 < r) (hR : 0 < R) (hc : 0 < c)
    (hsep : (5 / 2 : ℝ) * r ≤ c * R) (target : ℝ → ℂ)
    (htarget : ∀ θ, c * R ≤ ‖target θ‖) (θ : ℝ) :
    ‖velocityC (scaledComplexDensity A r (circularPhasePatchVorticity Z)) (target θ) -
      I / (2 * Real.pi) * ((A : ℂ) * (r : ℂ) ^ 6 * circularBoundaryFourthMoment Z) *
        (conj (target θ) ^ 5)⁻¹‖ / R ≤
      (8 / (15 * Real.pi * c ^ 9) * (5 / 4 : ℝ) ^ 8 *
        finiteContourPatchMassBound circularContourStrengths circularContourRadii) *
          |A| * (r / R) ^ 10 := by
  have hb := circularPhasePatch_scaled_exterior_remainder hγ hγ1 hZ harea hfour A hr
    (hsep.trans (htarget θ))
  have hM : 0 ≤ finiteContourPatchMassBound circularContourStrengths circularContourRadii := by
    exact (integral_nonneg (fun z => abs_nonneg (circularPhasePatchVorticity Z z))).trans
      (integral_abs_circularPhasePatchVorticity_le hγ hγ1 hZ)
  calc
    _ ≤ (8 / (15 * Real.pi) * (|A| * r ^ 10 * (5 / 4 : ℝ) ^ 8 *
        finiteContourPatchMassBound circularContourStrengths circularContourRadii) / ‖target θ‖ ^ 9) / R := by
      exact div_le_div_of_nonneg_right hb hR.le
    _ ≤ (8 / (15 * Real.pi) * (|A| * r ^ 10 * (5 / 4 : ℝ) ^ 8 *
        finiteContourPatchMassBound circularContourStrengths circularContourRadii) / (c * R) ^ 9) / R := by
      apply div_le_div_of_nonneg_right _ hR.le
      apply div_le_div_of_nonneg_left (by positivity) (by positivity)
      exact pow_le_pow_left₀ (by positivity) (htarget θ) 9
    _ = _ := by
      field_simp

end Euler2D

end
