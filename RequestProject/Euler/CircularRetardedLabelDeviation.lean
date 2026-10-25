module

public import RequestProject.Euler.CircularFiniteRetardedMaterialTube

/-! The same retarded raw family has a separate true material tube
radius for every label. The common prefix maximum is only used for
quarter-domain validity; interaction rows retain each actual norm. -/

@[expose] public section

set_option maxHeartbeats 4000000
set_option maxRecDepth 4000

noncomputable section

open Complex Set MeasureTheory Metric
open scoped NNReal ENNReal

namespace Euler2D

attribute [local instance 2000] rigidGaugeLittle_group rigidGaugeLittle_space rigidGaugeFamily_tower
attribute [local instance] LittleContourSpace.complexScalarNormedSpace LittleContourSpace.complexScalarTower

namespace CircularMaterialTransferProfile

variable {γ : ℝ≥0} {hγ : 0 < γ} {hγ1 : (γ : ℝ) < 1}
    (P : CircularMaterialTransferProfile hγ hγ1)

theorem finiteRetardedTube_relative_label {s R ρ : ℝ} (hR : 0 < R) (hρ : 0 < ρ)
    {N k : ℕ} {f : Lp ℝ 2 μT} {T : ℝ} {S : BoundedEulerParticleSystem f T}
    {t c δ : ℝ} (G : P.FiniteOuterMaterialTube s R ρ N k S t c δ)
    (Y : Fin (N + 1) → Fin 2 → LittleContourSpace γ) (u φ : Fin (N + 1) → ℝ)
    (hraw : ∀ j : Fin (N + 1), (j : ℕ) ≤ k → ∀ i,
      G.contours (j, i) =
        (radScale R ρ j • (exp (((φ j : ℝ) : ℂ) * I) • Y j i)).val)
    (hsmall : circularRetardedPrefixDeviation hγ hγ1 k Y u ≤ cellA / 4)
    (j : Fin (N + 1)) (hj : (j : ℕ) ≤ k) (i : Fin 2) :
    let G' := P.finiteOuterMaterialTubeOfRetardedFamily hR hρ G Y u φ hraw hsmall
    ‖contourParameterShiftC1 (G'.shifts (j, i)) (G'.contours (j, i)) - G'.reference (j, i)‖ ≤
      radScale R ρ j * ‖Y j - littleCircularMaterialContours hγ hγ1 (u j)‖ := by
  change ‖contourParameterShiftC1 (circularRetardedMaterialShift (φ j) (u j) i)
    (G.contours (j, i)) - finiteCircularReferenceC1 hγ hγ1 R ρ (j, i)‖ ≤ _
  rw [hraw j hj i]
  have hc := norm_le_pi_norm
    (contourParameterShiftFamilyCLM γ (circularRetardedMaterialShift (φ j) (u j))
      (radScale R ρ j • (exp (((φ j : ℝ) : ℂ) * I) • Y j)) -
        radScale R ρ j • littleCircularReference hγ hγ1) i
  rw [norm_circularRetardedPhysicalAligned_sub_reference hγ hγ1
    (radScale_pos hR hρ j).le] at hc
  exact hc

end CircularMaterialTransferProfile
end Euler2D

end
