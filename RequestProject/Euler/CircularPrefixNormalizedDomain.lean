module

public import RequestProject.Euler.CircularCanonicalPrefixCellDerivative
public import RequestProject.Euler.CircularPhaseArea

/-! The original finite canonical domain gives each normalized cell
the original isolated circular quarter-phase domain. No isolated
domain membership is assumed as a new trajectory hypothesis. -/

@[expose] public section

set_option maxHeartbeats 10000000
set_option maxRecDepth 5000

noncomputable section

open Complex Set Metric
open scoped NNReal

namespace Euler2D

attribute [local instance 2000] rigidGaugeLittle_group rigidGaugeLittle_space rigidGaugeFamily_tower
attribute [local instance] LittleContourSpace.complexScalarNormedSpace LittleContourSpace.complexScalarTower

local instance (priority := 2000) normalizedCellC1_group (γ : ℝ≥0) :
    NormedAddCommGroup (ContourC1Space γ) := Submodule.normedAddCommGroup (contourC1GraphSubmodule γ)
local instance (priority := 2000) normalizedCellC1_space (γ : ℝ≥0) :
    NormedSpace ℝ (ContourC1Space γ) := Submodule.normedSpace (contourC1GraphSubmodule γ)

theorem norm_normalizedContour_sub_reference {γ : ℝ≥0} {r : ℝ} (hr : 0 < r)
    (Z Ref : ContourC1Space γ) :
    ‖r⁻¹ • Z - Ref‖ = r⁻¹ * ‖Z - r • Ref‖ := by
  have he : r⁻¹ • Z - Ref = r⁻¹ • (Z - r • Ref) := by
    rw [smul_sub, smul_smul, inv_mul_cancel₀ hr.ne', one_smul]
  rw [he, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr)]

theorem normalizedFiniteCircularCell_mem_quarterPhaseDomain {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1)
    {R ρ : ℝ} (hR : 0 < R) (hρ : 0 < ρ) {k : ℕ}
    (W : FiniteCircularIndex k → LittleContourSpace γ)
    (hphase : IsPhaseAdmissibleLittleContourFamily (finiteCircularReferenceC1 hγ hγ1 R ρ)
      (finiteCircularInterfaceRadius R ρ) W)
    (hquarter : IsQuarterPhaseLittleContourFamily (finiteCircularReferenceC1 hγ hγ1 R ρ)
      (finiteCircularInterfaceRadius R ρ) W)
    (j : Fin (k + 1)) :
    (fun i => (radScale R ρ j)⁻¹ • W (j, i)) ∈ circularQuarterPhaseDomain hγ hγ1 := by
  let r := radScale R ρ j
  have hr : 0 < r := radScale_pos hR hρ j
  have hshift (β : FiniteCircularIndex k → ℝ) (i : Fin 2) :
      (contourParameterShiftFamilyCLM γ (-(fun i => β (j, i)))
        (fun i => (radScale R ρ j)⁻¹ • W (j, i)) i).val =
        r⁻¹ • (contourParameterShiftFamilyCLM γ (-β) W (j, i)).val := by
    change contourParameterShiftC1 (-β (j, i)) (r⁻¹ • (W (j, i)).val) =
      r⁻¹ • contourParameterShiftC1 (-β (j, i)) (W (j, i)).val
    exact (contourParameterShiftC1CLM γ (-β (j, i))).map_smul r⁻¹ (W (j, i)).val
  constructor
  · obtain ⟨β, hnear, hsep⟩ := hphase
    refine ⟨fun i => β (j, i), ?_, ?_⟩
    · intro i
      rw [hshift β i, norm_normalizedContour_sub_reference hr]
      have hn := hnear (j, i)
      change ‖(contourParameterShiftFamilyCLM γ (-β) W (j, i)).val -
        r • circularReferenceC1 hγ hγ1 i‖ < 2 * (r * circularContourRadii i) / Real.pi at hn
      calc
        _ < r⁻¹ * (2 * (r * circularContourRadii i) / Real.pi) := mul_lt_mul_of_pos_left hn (inv_pos.mpr hr)
        _ = _ := by field_simp
    · intro i l hil
      obtain ⟨σ, hσ, hcross⟩ := hsep (j, i) (j, l) (fun heq => hil (congrArg Prod.snd heq))
      refine ⟨r⁻¹ * σ, mul_pos (inv_pos.mpr hr) hσ, ?_⟩
      have hcross' : ContourCrossSeparated
          (r⁻¹ • (contourParameterShiftFamilyCLM γ (-β) W (j, i)).val)
          (r⁻¹ • (contourParameterShiftFamilyCLM γ (-β) W (j, l)).val) (r⁻¹ * σ) := by
        intro x y
        change r⁻¹ * σ ≤ ‖r⁻¹ • ContourC1Space.toBCF γ
          (contourParameterShiftFamilyCLM γ (-β) W (j, i)).val x -
          r⁻¹ • ContourC1Space.toBCF γ (contourParameterShiftFamilyCLM γ (-β) W (j, l)).val y‖
        rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr)]
        exact mul_le_mul_of_nonneg_left (hcross x y) (inv_pos.mpr hr).le
      exact (congrArg₂ (fun Zi Zl : ContourC1Space γ => ContourCrossSeparated Zi Zl (r⁻¹ * σ))
        (hshift β i) (hshift β l)).mpr hcross'
  · obtain ⟨β, hβ⟩ := hquarter
    refine ⟨fun i => -β (j, i), ?_⟩
    intro i
    have hnorm :
        ‖(contourParameterShiftFamilyCLM γ (-(fun i => -β (j, i)))
          (fun i => r⁻¹ • W (j, i)) i).val - circularReferenceC1 hγ hγ1 i‖ =
        r⁻¹ * ‖contourParameterShiftC1 (β (j, i)) (W (j, i)).val -
          r • circularReferenceC1 hγ hγ1 i‖ := by
      have hneg : (-(fun i : Fin 2 => -β (j, i))) = (fun i => β (j, i)) := by
        funext i
        exact neg_neg _
      rw [hneg]
      change ‖contourParameterShiftC1 (β (j, i)) (r⁻¹ • (W (j, i)).val) - _‖ = _
      have hmap : contourParameterShiftC1 (β (j, i)) (r⁻¹ • (W (j, i)).val) =
          r⁻¹ • contourParameterShiftC1 (β (j, i)) (W (j, i)).val :=
        (contourParameterShiftC1CLM γ (β (j, i))).map_smul r⁻¹ (W (j, i)).val
      rw [hmap]
      exact norm_normalizedContour_sub_reference hr _ _
    rw [hnorm]
    have hn := hβ (j, i)
    change ‖contourParameterShiftC1 (β (j, i)) (W (j, i)).val -
      r • circularReferenceC1 hγ hγ1 i‖ < r * circularContourRadii i / 4 at hn
    calc
      _ < r⁻¹ * (r * circularContourRadii i / 4) := mul_lt_mul_of_pos_left hn (inv_pos.mpr hr)
      _ = _ := by field_simp

end Euler2D

end
