module

public import RequestProject.Euler.CircularFiniteNormalizedConstraints
public import RequestProject.Euler.CircularFixedEntranceAlignment

/-! Fixed entrance material alignment of the actual interfaces keeps
their original area and fourfold constraints. The same original
constraint chart therefore recovers each aligned actual endpoint. -/

@[expose] public section

set_option maxHeartbeats 6500000
set_option maxRecDepth 5000

noncomputable section

open Complex Set MeasureTheory Metric
open scoped NNReal ENNReal

namespace Euler2D

attribute [local instance 2000] rigidGaugeLittle_group rigidGaugeLittle_space rigidGaugeFamily_tower
attribute [local instance] LittleContourSpace.complexScalarNormedSpace LittleContourSpace.complexScalarTower

theorem littleContourArea_parameterShiftLittleCLM {γ : ℝ≥0}
    (β : ℝ) (Y : LittleContourSpace γ) :
    littleContourArea γ (contourParameterShiftLittleCLM γ β Y) = littleContourArea γ Y := by
  exact contourArea_parameterShiftC1 β Y.val

theorem mem_fourfoldLittleContourSubmodule_parameterShift {γ : ℝ≥0}
    (β : ℝ) (Y : LittleContourSpace γ) (hY : Y ∈ fourfoldLittleContourSubmodule γ) :
    contourParameterShiftLittleCLM γ β Y ∈ fourfoldLittleContourSubmodule γ := by
  apply (mem_fourfoldLittleContourSubmodule _).mpr
  intro θ
  change LittleContourSpace.lift γ Y (θ + Real.pi / 2 + β) =
    I * LittleContourSpace.lift γ Y (θ + β)
  rw [show θ + Real.pi / 2 + β = (θ + β) + Real.pi / 2 by ring]
  exact (mem_fourfoldLittleContourSubmodule Y).mp hY (θ + β)

namespace CircularMaterialTransferProfile

variable {γ : ℝ≥0} {hγ : 0 < γ} {hγ1 : (γ : ℝ) < 1}
    (P : CircularMaterialTransferProfile hγ hγ1)

theorem exists_uniform_actualMaterial_aligned_constraintChart_radius :
    ∃ ε > 0, ∀ {s R ρ η : ℝ}, s ≤ 0 → ∀ (hR : 0 < R) (hρ : 0 < ρ),
      0 ≤ η → η ≤ cellA / 4 →
      (∀ i, ‖(P.ancient s i).val - circularReferenceC1 hγ hγ1 i‖ ≤ η) →
      ∀ {N k : ℕ} {f : Lp ℝ 2 μT} {T : ℝ} {S : BoundedEulerParticleSystem f T}
        {t c δ : ℝ}, t ∈ Icc (0 : ℝ) T →
      ∀ G : P.FiniteOuterMaterialTube s R ρ N k S t c δ,
      ∀ (j : Fin (N + 1)), (j : ℕ) ≤ k → ∀ (φ : ℝ) (Y : Fin 2 → LittleContourSpace γ),
      (∀ i, G.contours (j, i) = (radScale R ρ j • (exp ((φ : ℂ) * I) • Y i)).val) →
      ∀ β : Fin 2 → ℝ,
      contourParameterShiftFamilyCLM γ β Y ∈ ball (littleCircularReference hγ hγ1) ε →
      circularConstrainedChart hγ hγ1
        (circularConstraintProjectionToTangentCLM hγ hγ1.le
          (contourParameterShiftFamilyCLM γ β Y - littleCircularReference hγ hγ1)) =
            contourParameterShiftFamilyCLM γ β Y := by
  obtain ⟨ε, hε, hchart⟩ := exists_circular_actualConstraintChart_radius hγ hγ1
  refine ⟨ε, hε, ?_⟩
  intro s R ρ η hs hR hρ hη hηa hancient N k f T S t c δ ht G j hj φ Y hraw β hY
  obtain ⟨hfour, harea⟩ := P.finiteOuterMaterialTube_normalized_constraints
    hs hR hρ hη hηa hancient ht G j hj φ Y hraw
  apply hchart _ hY
  · intro i
    exact mem_fourfoldLittleContourSubmodule_parameterShift (β i) (Y i) (hfour i)
  · intro i
    exact (littleContourArea_parameterShiftLittleCLM (β i) (Y i)).trans (harea i)

end CircularMaterialTransferProfile
end Euler2D

end
