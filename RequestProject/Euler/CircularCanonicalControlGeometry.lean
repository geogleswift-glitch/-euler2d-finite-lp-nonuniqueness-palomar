module

public import RequestProject.Euler.CircularCanonicalStageDeviation
public import RequestProject.Euler.CircularRetardedTubeAlignment
public import RequestProject.Euler.WeightedPrefixGeometry

/-! The genuine raw canonical path satisfies the physical material
tube required for continuation once its actual two controls are bounded.
No separate geometry or material reconstruction hypothesis is needed. -/

@[expose] public section

set_option maxHeartbeats 8000000
set_option maxRecDepth 6000

noncomputable section

open Complex Set
open scoped NNReal

namespace Euler2D

attribute [local instance 2000] rigidGaugeLittle_group rigidGaugeLittle_space rigidGaugeFamily_tower
attribute [local instance] LittleContourSpace.complexScalarNormedSpace LittleContourSpace.complexScalarTower
attribute [local instance 2000] valueScalarC1_group valueScalarC1_space
attribute [local instance] ContourC1Space.complexScalarNormedSpace ContourC1Space.complexScalarTower

theorem canonicalPrefix_material_tube_of_joint_controls {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1) (A₀ b : ℝ) {R ρ : ℝ}
    (hR : 0 < R) (hρ : 0 < ρ) (k : ℕ) (entrance τ : ℝ)
    (X : ℝ → FiniteCircularIndex k → LittleContourSpace γ) {h K η : ℝ}
    (hh : 0 < h) (hh1 : h ≤ 1) (hK : 0 ≤ K) (hhK : h * K ≤ η)
    (hZ : weightedFamilyNorm h k (canonicalPrefixStageDeviation hγ hγ1 A₀ b R ρ k entrance X τ) ≤ K)
    (hcur : ‖canonicalPrefixStageDeviation hγ hγ1 A₀ b R ρ k entrance X τ k‖ ≤ η) :
    ∃ β : FiniteCircularIndex k → ℝ, ∀ p,
      ‖contourParameterShiftC1 (β p)
          (X (physicalTimeFromNormalized (ampScale A₀ b k) entrance τ) p).val -
        finiteCircularReferenceC1 hγ hγ1 R ρ p‖ ≤ η * radScale R ρ p.1 := by
  let Y := canonicalPrefixAbsoluteFamily A₀ b R ρ k entrance X τ
  let x := canonicalPrefixStageDeviation hγ hγ1 A₀ b R ρ k entrance X τ
  let u : ℕ → ℝ := fun l => ampScale A₀ b l * entrance + b ^ (k - l) * τ
  let φ : ℕ → ℝ := fun l => physicalTimeFromNormalized (ampScale A₀ b k) entrance τ * finiteAncestorAngularVelocity A₀ b l
  let β : FiniteCircularIndex k → ℝ := fun p => circularRetardedMaterialShift (φ p.1) (u p.1) p.2
  have hfull (l : Fin (k + 1)) : ‖x l‖ ≤ η :=
    norm_prefix_le_of_weighted_current hh hh1 hK k x hZ hcur hhK l
  refine ⟨β, ?_⟩
  intro p
  have hraw : (X (physicalTimeFromNormalized (ampScale A₀ b k) entrance τ) p).val =
      (radScale R ρ p.1 • (exp (((φ p.1 : ℝ) : ℂ) * I) • Y p.1 p.2)).val := by
    have he := congrArg (fun V : Fin 2 → LittleContourSpace γ => (V p.2).val)
      (canonicalPrefixAbsoluteCell_raw (A₀ := A₀) (b := b) hR hρ k entrance τ X p.1)
    simpa only [Y, canonicalPrefixAbsoluteFamily, dif_pos (Nat.le_of_lt_succ p.1.isLt), φ,
      Pi.smul_apply] using he.symm
  rw [hraw]
  have hn := norm_le_pi_norm
    (contourParameterShiftFamilyCLM γ (circularRetardedMaterialShift (φ p.1) (u p.1))
      (radScale R ρ p.1 • (exp (((φ p.1 : ℝ) : ℂ) * I) • Y p.1)) -
        radScale R ρ p.1 • littleCircularReference hγ hγ1) p.2
  rw [norm_circularRetardedPhysicalAligned_sub_reference hγ hγ1 (radScale_pos hR hρ p.1).le] at hn
  exact hn.trans ((mul_le_mul_of_nonneg_left (hfull p.1) (radScale_pos hR hρ p.1).le).trans_eq (mul_comm _ _))

end Euler2D

end
