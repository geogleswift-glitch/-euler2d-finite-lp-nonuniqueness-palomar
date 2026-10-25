module

public import RequestProject.Euler.CircularCanonicalCurrentCoordinates

/-! The original circular quarter-phase domain is preserved by the
actual material and spatial gauges. Canonical domain membership
therefore gives quarter-phase membership in the actual aligned frame,
without a new contour-domain premise. -/

@[expose] public section

set_option maxHeartbeats 12000000
set_option maxRecDepth 6000

noncomputable section

open Complex Set MeasureTheory Metric
open scoped NNReal

namespace Euler2D

attribute [local instance 2000] rigidGaugeLittle_group rigidGaugeLittle_space rigidGaugeFamily_tower
attribute [local instance] LittleContourSpace.complexScalarNormedSpace LittleContourSpace.complexScalarTower

theorem circularQuarterPhaseDomain_parameterShift {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1) (β : Fin 2 → ℝ)
    {Z : Fin 2 → LittleContourSpace γ} (hZ : Z ∈ circularQuarterPhaseDomain hγ hγ1) :
    contourParameterShiftFamilyCLM γ β Z ∈ circularQuarterPhaseDomain hγ hγ1 := by
  refine ⟨circularBanachDomain_parameterShift hγ hγ1 β hZ.1, ?_⟩
  obtain ⟨c, hc⟩ := hZ.2
  refine ⟨β + c, ?_⟩
  have he : -(β + c) + β = -c := by funext i; simp only [Pi.neg_apply, Pi.add_apply]; ring
  intro i
  rw [contourParameterShiftFamilyCLM_add, he]
  exact hc i

theorem circularQuarterPhaseDomain_rotation {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1) (angle : ℝ)
    {Z : Fin 2 → LittleContourSpace γ} (hZ : Z ∈ circularQuarterPhaseDomain hγ hγ1) :
    contourRotationFamilyLittleCLM γ angle Z ∈ circularQuarterPhaseDomain hγ hγ1 := by
  refine ⟨circularBanachDomain_rotation hγ hγ1 angle hZ.1, ?_⟩
  obtain ⟨c, hc⟩ := hZ.2
  refine ⟨c, ?_⟩
  intro i
  change ‖(contourParameterShiftLittleCLM γ (-c i) (contourRotationLittleCLM γ angle (Z i))).val -
    circularReferenceC1 hγ hγ1 i‖ < _
  rw [contourRotationLittleCLM_parameterShift_comm]
  have hfix := contourRotationC1_refCircle angle (circularReferenceC1 hγ hγ1 i)
    (lift_circularReferenceC1 hγ hγ1 i)
  have he : contourRotationC1 angle
      ((contourParameterShiftLittleCLM γ (-c i) (Z i)).val - circularReferenceC1 hγ hγ1 i) =
      contourRotationC1 angle (contourParameterShiftLittleCLM γ (-c i) (Z i)).val -
        circularReferenceC1 hγ hγ1 i := by
    change contourRotationC1CLM γ angle (_ - _) = _
    rw [map_sub]
    exact congrArg (contourRotationC1 angle
      (contourParameterShiftLittleCLM γ (-c i) (Z i)).val - ·) hfix
  change ‖contourRotationC1 angle (contourParameterShiftLittleCLM γ (-c i) (Z i)).val -
    circularReferenceC1 hγ hγ1 i‖ < _
  rw [← he, norm_contourRotationC1]
  exact hc i

theorem circularQuarterPhaseDomain_complexValueRotation {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1) (angle : ℝ)
    {Z : Fin 2 → LittleContourSpace γ} (hZ : Z ∈ circularQuarterPhaseDomain hγ hγ1) :
    Complex.exp ((angle : ℂ) * I) • Z ∈ circularQuarterPhaseDomain hγ hγ1 := by
  rw [complexValueRotationFamily_eq_shift_rotation]
  exact circularQuarterPhaseDomain_parameterShift hγ hγ1 _
    (circularQuarterPhaseDomain_rotation hγ hγ1 angle hZ)

theorem canonicalPrefixAbsoluteCell_mem_quarterPhaseDomain {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1) {R ρ : ℝ} (hR : 0 < R) (hρ : 0 < ρ)
    (A₀ b : ℝ) (k : ℕ) (X : ℝ → FiniteCircularIndex k → LittleContourSpace γ) (t : ℝ)
    (hphase : IsPhaseAdmissibleLittleContourFamily (finiteCircularReferenceC1 hγ hγ1 R ρ)
      (finiteCircularInterfaceRadius R ρ) (X t))
    (hquarter : IsQuarterPhaseLittleContourFamily (finiteCircularReferenceC1 hγ hγ1 R ρ)
      (finiteCircularInterfaceRadius R ρ) (X t))
    (j : Fin (k + 1)) (entrance τ : ℝ)
    (htime : physicalTimeFromNormalized (ampScale A₀ b k) entrance τ = t) :
    canonicalPrefixAbsoluteCell A₀ b R ρ k entrance X τ j ∈ circularQuarterPhaseDomain hγ hγ1 := by
  rw [canonicalPrefixAbsoluteCell_eq_physicalState A₀ b R ρ k entrance τ t X j htime]
  exact circularQuarterPhaseDomain_complexValueRotation hγ hγ1
    ((t - 0) * (-finiteAncestorAngularVelocity A₀ b j))
      (normalizedFiniteCircularCell_mem_quarterPhaseDomain hγ hγ1 hR hρ (X t) hphase hquarter j)

theorem canonicalPrefixAlignedCurrentCell_mem_quarterPhaseDomain {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1) {R ρ : ℝ} (hR : 0 < R) (hρ : 0 < ρ)
    (A₀ b : ℝ) (k : ℕ) (X : ℝ → FiniteCircularIndex k → LittleContourSpace γ) (t : ℝ)
    (hphase : IsPhaseAdmissibleLittleContourFamily (finiteCircularReferenceC1 hγ hγ1 R ρ)
      (finiteCircularInterfaceRadius R ρ) (X t))
    (hquarter : IsQuarterPhaseLittleContourFamily (finiteCircularReferenceC1 hγ hγ1 R ρ)
      (finiteCircularInterfaceRadius R ρ) (X t))
    (entrance τ : ℝ) (htime : physicalTimeFromNormalized (ampScale A₀ b k) entrance τ = t) :
    canonicalPrefixAlignedCurrentCell A₀ b R ρ k entrance X τ ∈ circularQuarterPhaseDomain hγ hγ1 := by
  exact circularQuarterPhaseDomain_parameterShift hγ hγ1 _
    (canonicalPrefixAbsoluteCell_mem_quarterPhaseDomain hγ hγ1 hR hρ A₀ b k X t hphase hquarter
      (Fin.last k) entrance τ htime)

end Euler2D

end
