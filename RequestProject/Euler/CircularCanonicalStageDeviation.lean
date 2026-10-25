module

public import RequestProject.Euler.CircularCanonicalAbsoluteGauge
public import RequestProject.Euler.BanachWeightedTrajectoryEnvelope

/-! The fixed entrance slow reference is the physical reference at
the same absolute time, for every active label. -/

@[expose] public section

set_option maxHeartbeats 5000000

noncomputable section

open scoped NNReal

namespace Euler2D

attribute [local instance 2000] rigidGaugeLittle_group rigidGaugeLittle_space rigidGaugeFamily_tower

def canonicalPrefixStageDeviation {γ : ℝ≥0} (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1)
    (A₀ b R ρ : ℝ) (k : ℕ) (entrance : ℝ)
    (X : ℝ → FiniteCircularIndex k → LittleContourSpace γ) (τ : ℝ) (l : ℕ) :
    Fin 2 → LittleContourSpace γ :=
  canonicalPrefixAbsoluteFamily A₀ b R ρ k entrance X τ l -
    littleCircularMaterialContours hγ hγ1 (ampScale A₀ b l * entrance + b ^ (k - l) * τ)

theorem canonicalPrefixStageDeviation_eq_physical {γ : ℝ≥0} (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1)
    {A₀ b : ℝ} (hA : A₀ ≠ 0) (hb : b ≠ 0) (R ρ : ℝ) (k : ℕ) (entrance τ : ℝ)
    (X : ℝ → FiniteCircularIndex k → LittleContourSpace γ) (l : ℕ) (hl : l ≤ k) :
    canonicalPrefixStageDeviation hγ hγ1 A₀ b R ρ k entrance X τ l =
      canonicalPrefixAbsoluteFamily A₀ b R ρ k entrance X τ l -
        littleCircularMaterialContours hγ hγ1
          (ampScale A₀ b l * physicalTimeFromNormalized (ampScale A₀ b k) entrance τ) := by
  unfold canonicalPrefixStageDeviation
  rw [canonicalPrefixAbsolute_reference_clock hA hb hl]

theorem weightedFamilyNorm_congr_prefix {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (h : ℝ) (k : ℕ) {x y : ℕ → E} (heq : ∀ j : Fin k, x j = y j) :
    weightedFamilyNorm h k x = weightedFamilyNorm h k y := by
  unfold weightedFamilyNorm weightedFamilyDifference
  congr 1
  funext j
  rw [heq j]

theorem canonicalPrefixStageDeviation_weighted_eq_physical {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1) {A₀ b : ℝ} (hA : A₀ ≠ 0) (hb : b ≠ 0)
    (R ρ : ℝ) (k : ℕ) (entrance τ h : ℝ)
    (X : ℝ → FiniteCircularIndex k → LittleContourSpace γ) :
    weightedFamilyNorm h k (canonicalPrefixStageDeviation hγ hγ1 A₀ b R ρ k entrance X τ) =
      weightedFamilyNorm h k (fun l => canonicalPrefixAbsoluteFamily A₀ b R ρ k entrance X τ l -
        littleCircularMaterialContours hγ hγ1
          (ampScale A₀ b l * physicalTimeFromNormalized (ampScale A₀ b k) entrance τ)) := by
  apply weightedFamilyNorm_congr_prefix
  intro j
  exact canonicalPrefixStageDeviation_eq_physical hγ hγ1 hA hb R ρ k entrance τ X j j.isLt.le

end Euler2D

end
