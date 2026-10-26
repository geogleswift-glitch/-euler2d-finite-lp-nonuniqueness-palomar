module

public import RequestProject.Euler.CircularFinitePhaseEndpoint
public import RequestProject.Euler.CircularAncientFiniteInitialFamily
public import RequestProject.Euler.FiniteQuarterTargetSeparation

/-! The genuine finite quarter-phase domain supplies one fixed
target norm budget and both pointwise radius bounds. All constants
precede the physical scales and the finite cutoff. -/

@[expose] public section

set_option maxHeartbeats 6000000
set_option maxRecDepth 5000

noncomputable section

open Complex Set Metric
open scoped NNReal

namespace Euler2D

local instance (priority := 2000) canonicalTargetLittle_group (γ : ℝ≥0) :
    NormedAddCommGroup (LittleContourSpace γ) := Submodule.normedAddCommGroup (LittleContourSpace γ)
local instance (priority := 2000) canonicalTargetLittle_space (γ : ℝ≥0) :
    NormedSpace ℝ (LittleContourSpace γ) := Submodule.normedSpace (LittleContourSpace γ)

def circularCanonicalCellNormBudget {γ : ℝ≥0} (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1) : ℝ :=
  ‖littleCircularReference hγ hγ1‖ + 1

theorem circularCanonicalCellNormBudget_pos {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1) : 0 < circularCanonicalCellNormBudget hγ hγ1 := by
  unfold circularCanonicalCellNormBudget
  positivity

theorem norm_finiteCircular_quarter_cell_le {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1) {R ρ : ℝ} (hR : 0 < R) (hρ : 0 < ρ)
    {k : ℕ} (Z : FiniteCircularIndex k → LittleContourSpace γ)
    (hquarter : IsQuarterPhaseLittleContourFamily (finiteCircularReferenceC1 hγ hγ1 R ρ)
      (finiteCircularInterfaceRadius R ρ) Z) (j : Fin (k + 1)) (i : Fin 2) :
    ‖Z (j, i)‖ ≤ radScale R ρ j * circularCanonicalCellNormBudget hγ hγ1 := by
  obtain ⟨β, hβ⟩ := hquarter
  have hr : 0 < radScale R ρ j := radScale_pos hR hρ j
  have hd : circularContourRadii i ≤ 1 := (circularContourRadii_bounds i).2.2
  have hsmall : ‖contourParameterShiftC1 (β (j, i)) (Z (j, i)).val -
      finiteCircularReferenceC1 hγ hγ1 R ρ (j, i)‖ ≤ radScale R ρ j := by
    have hh := (hβ (j, i)).le
    have hi := mul_le_mul_of_nonneg_right hd hr.le
    dsimp only [finiteCircularInterfaceRadius] at hh
    nlinarith only [hh, hi, hr]
  have hRef : ‖finiteCircularReferenceC1 hγ hγ1 R ρ (j, i)‖ =
      radScale R ρ j * ‖littleCircularReference hγ hγ1 i‖ := by
    rw [finiteCircularReferenceC1, norm_smul, Real.norm_of_nonneg hr.le]
    rfl
  calc
    ‖Z (j, i)‖ = ‖contourParameterShiftC1 (β (j, i)) (Z (j, i)).val‖ :=
      (norm_contourParameterShiftC1 _ _).symm
    _ ≤ ‖contourParameterShiftC1 (β (j, i)) (Z (j, i)).val -
        finiteCircularReferenceC1 hγ hγ1 R ρ (j, i)‖ +
        ‖finiteCircularReferenceC1 hγ hγ1 R ρ (j, i)‖ := norm_le_norm_sub_add _ _
    _ ≤ radScale R ρ j + radScale R ρ j * ‖littleCircularReference hγ hγ1 i‖ :=
      add_le_add hsmall hRef.le
    _ ≤ radScale R ρ j * circularCanonicalCellNormBudget hγ hγ1 := by
      have hh := mul_le_mul_of_nonneg_left (norm_le_pi_norm (littleCircularReference hγ hγ1) i) hr.le
      unfold circularCanonicalCellNormBudget
      calc
        _ ≤ radScale R ρ j + radScale R ρ j * ‖littleCircularReference hγ hγ1‖ :=
          add_le_add (le_refl (radScale R ρ j)) hh
        _ = radScale R ρ j * (‖littleCircularReference hγ hγ1‖ + 1) := by ring

theorem finiteCircular_quarter_cell_target_bounds {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1) {R ρ : ℝ} (hR : 0 < R) (hρ : 0 < ρ)
    {k : ℕ} (Z : FiniteCircularIndex k → LittleContourSpace γ)
    (hquarter : IsQuarterPhaseLittleContourFamily (finiteCircularReferenceC1 hγ hγ1 R ρ)
      (finiteCircularInterfaceRadius R ρ) Z) (j : Fin (k + 1)) :
    (∀ i z, ‖ContourC1Space.toBCF γ (Z (j, i)).val z‖ ≤
      circularCanonicalCellNormBudget hγ hγ1 * radScale R ρ j) ∧
    (∀ i z, (cellA / 2) * radScale R ρ j ≤ ‖ContourC1Space.toBCF γ (Z (j, i)).val z‖) ∧
    (∀ i, ‖Z (j, i)‖ ≤ radScale R ρ j * circularCanonicalCellNormBudget hγ hγ1) := by
  have hnorm := norm_finiteCircular_quarter_cell_le hγ hγ1 hR hρ Z hquarter j
  refine ⟨?_, ?_, hnorm⟩
  · intro i z
    exact (((ContourC1Space.toBCF γ (Z (j, i)).val).norm_coe_le_norm z).trans
      (ContourC1Space.norm_toBCF_le _)).trans ((hnorm i).trans_eq (mul_comm _ _))
  · intro i z
    have hh := quarterPhase_target_radius_lower (finiteCircularReferenceC1 hγ hγ1 R ρ)
      (finiteCircularInterfaceRadius R ρ) (finiteCircularInterfaceRadius_pos hR hρ)
      (lift_finiteCircularReferenceC1 hγ hγ1 R ρ) hquarter (j, i) z
    have hi := mul_le_mul_of_nonneg_right (circularContourRadii_bounds i).2.1 (radScale_pos hR hρ j).le
    dsimp only [finiteCircularInterfaceRadius] at hh
    nlinarith only [hh, hi]

end Euler2D

end
