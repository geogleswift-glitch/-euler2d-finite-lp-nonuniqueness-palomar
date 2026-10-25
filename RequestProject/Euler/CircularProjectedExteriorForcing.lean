module

public import RequestProject.Euler.CircularUnstablePointwiseBound
public import RequestProject.Euler.CircularReferenceMultipoleLift
public import RequestProject.Euler.ComplexSourceMomentBounds
public import RequestProject.Euler.CircularPhysicalContourLittle

/-! Construct the true Little contour field of an actual compact
source and identify its leading growing coordinate. Both remainder
terms follow from the original volume velocity and actual support/L1
bounds; no projected forcing or error bound is assumed. -/

@[expose] public section

set_option maxHeartbeats 16000000
set_option maxRecDepth 6500

noncomputable section

open Complex Set MeasureTheory
open scoped NNReal ComplexConjugate

namespace Euler2D

local instance (priority := 2000) projectedExteriorLittle_group (γ : ℝ≥0) :
    NormedAddCommGroup (LittleContourSpace γ) := Submodule.normedAddCommGroup (LittleContourSpace γ)
local instance (priority := 2000) projectedExteriorLittle_space (γ : ℝ≥0) :
    NormedSpace ℝ (LittleContourSpace γ) := Submodule.normedSpace (LittleContourSpace γ)

theorem exists_circular_source_forcing_with_multipole_projection {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) ≤ 1) {w : ℂ → ℝ} {S A d ε : ℝ}
    (hS : 0 ≤ S) (hw : Integrable w) (hsupp : ∀ z, S < ‖z‖ → w z = 0)
    (hmass : ∫ z, w z = 0) (hsym : ∀ z, w (I * z) = w z)
    (hA : (∫ z : ℂ, |w z|) ≤ A) (hd : 0 < d) (hdref : d ≤ cellA) (hsep : 8 * S ≤ d)
    (Z : Fin 2 → LittleContourSpace γ)
    (hZ : ∀ i x, d ≤ ‖ContourC1Space.toBCF γ (Z i).val x‖)
    (hnear : ∀ i θ, ‖LittleContourSpace.lift γ (Z i) θ - refCircle (circularContourRadii i) θ‖ ≤ ε) :
    ∃ Q : Fin 2 → LittleContourSpace γ,
      (∀ i θ, LittleContourSpace.lift γ (Q i) θ = velocityC w (LittleContourSpace.lift γ (Z i) θ)) ∧
      ‖circularUnstableCoordinateCLM γ Q - Kstar * momentN w 4‖ ≤
        (2 / cellA) * (8 / (15 * Real.pi) * (S ^ 8 * A) / d ^ 9 +
          (5 / (2 * Real.pi * d ^ 6)) * (S ^ 4 * A) * ε) := by
  have hAn : 0 ≤ A := (integral_nonneg (fun z : ℂ => abs_nonneg (w z))).trans hA
  have hM₄ := complex_absMoment_le_support_mass hS hw hsupp hA 4
  have hM₈ := complex_absMoment_le_support_mass hS hw hsupp hA 8
  have hmoment := norm_complexMoment_le_support_mass hS hw hsupp hA 4
  have hex (i : Fin 2) : ∃ Qi : LittleContourSpace γ,
      ∀ θ, LittleContourSpace.lift γ Qi θ = velocityC w (LittleContourSpace.lift γ (Z i) θ) := by
    obtain ⟨Qi, hQi, _hnorm⟩ := exists_clusterContourFieldC1 hγ1 hS hw hsupp hmass hsym hM₄ hd
      (by linarith only [hsep, hS] : 4 * S ≤ d) (Z i).val (hZ i)
    have hmem := clusterContourFieldC1_mem_little hγ1 hS hw hsupp hmass hsym hM₄ hd hsep
      (Z i) (hZ i) Qi hQi
    exact ⟨⟨Qi, hmem⟩, hQi⟩
  choose Q hQ using hex
  have hγ1n : γ ≤ 1 := by exact_mod_cast hγ1
  let M := momentN w 4
  let E₀ := 8 / (15 * Real.pi) * (S ^ 8 * A) / d ^ 9
  let E₁ := (5 / (2 * Real.pi * d ^ 6)) * (S ^ 4 * A) * ε
  have hpoint (i : Fin 2) (θ : ℝ) :
      ‖LittleContourSpace.lift γ (Q i) θ -
        LittleContourSpace.lift γ (circularFourthMomentReferenceForcing hγ hγ1n M i) θ‖ ≤ E₀ + E₁ := by
    let z := LittleContourSpace.lift γ (Z i) θ
    let zref := refCircle (circularContourRadii i) θ
    have hz : d ≤ ‖z‖ := hZ i (θ : ContourCircle)
    have hz0 : z ≠ 0 := norm_pos_iff.mp (hd.trans_le hz)
    have href : d ≤ ‖zref‖ := by
      rw [norm_refCircle_eq_abs_radius, abs_of_pos (circularContourRadii_bounds i).1]
      exact hdref.trans (circularContourRadii_bounds i).2.1
    have hrem : ‖velocityC w z - fourthMomentVelocityField M z‖ ≤ E₀ := by
      have hb := exterior_multipole_remainder hw hsupp hmass hsym hz0
        ((by linarith only [hsep, hS] : 2 * S ≤ d).trans hz)
      change ‖velocityC w z - fourthMomentVelocityField M z‖ ≤ _ at hb
      calc
        _ ≤ 8 / (15 * Real.pi) * (∫ y : ℂ, ‖y‖ ^ 8 * |w y|) / ‖z‖ ^ 9 := hb
        _ ≤ 8 / (15 * Real.pi) * (S ^ 8 * A) / ‖z‖ ^ 9 :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hM₈ (by positivity)) (by positivity)
        _ ≤ E₀ := div_le_div_of_nonneg_left (by positivity) (pow_pos hd 9)
          (pow_le_pow_left₀ hd.le hz 9)
    have hshape : ‖fourthMomentVelocityField M z - fourthMomentVelocityField M zref‖ ≤ E₁ := by
      exact (norm_fourthMomentVelocityField_sub_le M hd hz href).trans
        (mul_le_mul (mul_le_mul_of_nonneg_left hmoment (by positivity)) (hnear i θ)
          (norm_nonneg _) (by positivity))
    rw [hQ i θ, lift_circularFourthMomentReferenceForcing_eq_multipole]
    change ‖velocityC w z - fourthMomentVelocityField M zref‖ ≤ E₀ + E₁
    have heq : velocityC w z - fourthMomentVelocityField M zref =
        (velocityC w z - fourthMomentVelocityField M z) +
          (fourthMomentVelocityField M z - fourthMomentVelocityField M zref) := by ring
    rw [heq]
    exact (norm_add_le _ _).trans (add_le_add hrem hshape)
  have hcoordinate := norm_circularUnstableCoordinate_sub_le_of_lift_bound Q
    (circularFourthMomentReferenceForcing hγ hγ1n M) hpoint
  rw [circularFourthMomentReferenceForcing_growing_coordinate] at hcoordinate
  exact ⟨Q, hQ, hcoordinate⟩

end Euler2D

end
