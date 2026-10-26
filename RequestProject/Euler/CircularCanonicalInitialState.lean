module

public import RequestProject.Euler.CircularCanonicalPrefixMaterialBoundary

/-! The first actual stage has exactly the original ancient sample
in its deepest cell and exactly circular ancestors. Hence its actual
weighted ancestor seed is zero at every finite cutoff. -/

@[expose] public section

set_option maxHeartbeats 7000000
set_option maxRecDepth 4500

noncomputable section

open Complex Set MeasureTheory
open scoped NNReal ENNReal

namespace Euler2D

attribute [local instance 2000] rigidGaugeLittle_group rigidGaugeLittle_space rigidGaugeFamily_tower
attribute [local instance] LittleContourSpace.complexScalarNormedSpace LittleContourSpace.complexScalarTower

namespace CircularMaterialTransferProfile

variable {γ : ℝ≥0} {hγ : 0 < γ} {hγ1 : (γ : ℝ) < 1}
    (P : CircularMaterialTransferProfile hγ hγ1)

theorem actualCanonicalPrefix_initial_cell
    {s A₀ b R ρ a Hglob D : ℝ} (hR : 0 < R) (hρ : 0 < ρ)
    {N k : ℕ} (hkN : k ≤ N) {f : Lp ℝ 2 μT} {T : ℝ}
    (S : BoundedEulerParticleSystem f T)
    (X : ℝ → FiniteCircularIndex k → LittleContourSpace γ)
    (hX : P.ActualCanonicalPrefixTrajectory s A₀ b R ρ a Hglob hR hρ hkN S D X)
    (j : Fin (k + 1)) :
    canonicalPrefixAbsoluteCell A₀ b R ρ k 0 X 0 j =
      if (j : ℕ) = N then P.ancient s else littleCircularReference hγ hγ1 := by
  have htime : physicalTimeFromNormalized (ampScale A₀ b k) 0 0 = 0 := by
    simp only [physicalTimeFromNormalized, zero_div, add_zero]
  rw [canonicalPrefixAbsoluteCell_eq_physicalState A₀ b R ρ k 0 0 0 X j htime,
    rigidRotationGauge_entrance, one_smul, hX.initial]
  funext i
  change (radScale R ρ j)⁻¹ •
      (radScale R ρ j • (if (j : ℕ) = N then P.ancient s i else littleCircularReference hγ hγ1 i)) = _
  rw [inv_smul_smul₀ (radScale_pos hR hρ j).ne']
  split_ifs <;> rfl

theorem actualCanonicalPrefix_initial_deepest
    {s A₀ b R ρ a Hglob D : ℝ} (hR : 0 < R) (hρ : 0 < ρ)
    (N : ℕ) {f : Lp ℝ 2 μT} {T : ℝ}
    (S : BoundedEulerParticleSystem f T)
    (X : ℝ → FiniteCircularIndex N → LittleContourSpace γ)
    (hX : P.ActualCanonicalPrefixTrajectory s A₀ b R ρ a Hglob hR hρ le_rfl S D X) :
    canonicalPrefixAbsoluteCell A₀ b R ρ N 0 X 0 (Fin.last N) = P.ancient s := by
  simpa only [Fin.val_last, if_pos rfl, ite_true] using P.actualCanonicalPrefix_initial_cell hR hρ le_rfl S X hX (Fin.last N)

theorem actualCanonicalPrefix_initial_ancestor
    {s A₀ b R ρ a Hglob D : ℝ} (hR : 0 < R) (hρ : 0 < ρ)
    {N k : ℕ} (hkN : k ≤ N) {f : Lp ℝ 2 μT} {T : ℝ}
    (S : BoundedEulerParticleSystem f T)
    (X : ℝ → FiniteCircularIndex k → LittleContourSpace γ)
    (hX : P.ActualCanonicalPrefixTrajectory s A₀ b R ρ a Hglob hR hρ hkN S D X)
    (j : Fin k) :
    canonicalPrefixStageDeviation hγ hγ1 A₀ b R ρ k 0 X 0 j = 0 := by
  have hjN : (j : ℕ) ≠ N := Nat.ne_of_lt (j.isLt.trans_le hkN)
  unfold canonicalPrefixStageDeviation
  simp only [canonicalPrefixAbsoluteFamily, dif_pos j.isLt.le, mul_zero, add_zero,
    littleCircularMaterialContours_zero]
  change canonicalPrefixAbsoluteCell A₀ b R ρ k 0 X 0 j.castSucc - littleCircularReference hγ hγ1 = 0
  rw [P.actualCanonicalPrefix_initial_cell hR hρ hkN S X hX j.castSucc]
  change (if (j : ℕ) = N then P.ancient s else littleCircularReference hγ hγ1) - littleCircularReference hγ hγ1 = 0
  rw [if_neg hjN, sub_self]

theorem actualCanonicalPrefix_initial_weighted_zero
    {s A₀ b R ρ a Hglob D : ℝ} (hR : 0 < R) (hρ : 0 < ρ)
    {N k : ℕ} (hkN : k ≤ N) {f : Lp ℝ 2 μT} {T : ℝ}
    (S : BoundedEulerParticleSystem f T)
    (X : ℝ → FiniteCircularIndex k → LittleContourSpace γ)
    (hX : P.ActualCanonicalPrefixTrajectory s A₀ b R ρ a Hglob hR hρ hkN S D X)
    (h : ℝ) :
    weightedFamilyNorm h k (canonicalPrefixStageDeviation hγ hγ1 A₀ b R ρ k 0 X 0) = 0 := by
  have hf : weightedFamilyDifference h k (canonicalPrefixStageDeviation hγ hγ1 A₀ b R ρ k 0 X 0) = 0 := by
    funext j
    change (h ^ (k - (j : ℕ)))⁻¹ • canonicalPrefixStageDeviation hγ hγ1 A₀ b R ρ k 0 X 0 j = 0
    rw [P.actualCanonicalPrefix_initial_ancestor hR hρ hkN S X hX j, smul_zero]
  change ‖weightedFamilyDifference h k _‖ = 0
  rw [hf, norm_zero]

end CircularMaterialTransferProfile
end Euler2D

end
