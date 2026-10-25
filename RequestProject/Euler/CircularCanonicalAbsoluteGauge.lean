module

public import RequestProject.Euler.CircularCanonicalPrefixRetardedAlignment

/-! One absolute rigid gauge for the same canonical X. It equals the
stage gauge times a single fixed entrance rotation. At a common
physical time it is independent of the stage clock. -/

@[expose] public section

set_option maxHeartbeats 7000000

noncomputable section

open Complex Set
open scoped NNReal

namespace Euler2D

attribute [local instance 2000] rigidGaugeLittle_group rigidGaugeLittle_space rigidGaugeFamily_tower
attribute [local instance] LittleContourSpace.complexScalarNormedSpace LittleContourSpace.complexScalarTower

def canonicalPrefixAbsoluteCell {γ : ℝ≥0} (A₀ b R ρ : ℝ) (k : ℕ) (aTime : ℝ)
    (X : ℝ → FiniteCircularIndex k → LittleContourSpace γ) (τ : ℝ) (j : Fin (k + 1)) :
    Fin 2 → LittleContourSpace γ :=
  rigidRotationGauge (finiteAncestorAngularVelocity A₀ b j) 0
      (physicalTimeFromNormalized (ampScale A₀ b k) aTime τ) •
    normalizedPhysicalCurve (ampScale A₀ b k) (radScale R ρ j) aTime (fun t i => X t (j, i)) τ

def canonicalPrefixAbsoluteFamily {γ : ℝ≥0} (A₀ b R ρ : ℝ) (k : ℕ) (aTime : ℝ)
    (X : ℝ → FiniteCircularIndex k → LittleContourSpace γ) (τ : ℝ) (l : ℕ) :
    Fin 2 → LittleContourSpace γ :=
  if hl : l ≤ k then canonicalPrefixAbsoluteCell A₀ b R ρ k aTime X τ ⟨l, Nat.lt_succ_of_le hl⟩ else 0

theorem absoluteGauge_eq_fixedEntranceRotation (Ω A aTime τ : ℝ) :
    rigidRotationGauge Ω 0 (physicalTimeFromNormalized A aTime τ) =
      exp (((-Ω * aTime : ℝ) : ℂ) * I) * rigidRotationGauge (Ω / A) 0 τ := by
  unfold rigidRotationGauge physicalTimeFromNormalized
  rw [← exp_add]
  congr 2
  push_cast
  ring

theorem canonicalPrefixAbsoluteCell_eq_fixedEntranceRotation {γ : ℝ≥0}
    (A₀ b R ρ : ℝ) (k : ℕ) (aTime : ℝ)
    (X : ℝ → FiniteCircularIndex k → LittleContourSpace γ) (τ : ℝ) (j : Fin (k + 1)) :
    canonicalPrefixAbsoluteCell A₀ b R ρ k aTime X τ j =
      exp (((-finiteAncestorAngularVelocity A₀ b j * aTime : ℝ) : ℂ) * I) •
        canonicalPrefixRotatedCell A₀ b R ρ k aTime X τ j := by
  unfold canonicalPrefixAbsoluteCell canonicalPrefixRotatedCell
  rw [absoluteGauge_eq_fixedEntranceRotation, smul_smul]

theorem canonicalPrefixAbsoluteCell_eq_physicalState {γ : ℝ≥0}
    (A₀ b R ρ : ℝ) (k : ℕ) (aTime τ t : ℝ)
    (X : ℝ → FiniteCircularIndex k → LittleContourSpace γ) (j : Fin (k + 1))
    (htime : physicalTimeFromNormalized (ampScale A₀ b k) aTime τ = t) :
    canonicalPrefixAbsoluteCell A₀ b R ρ k aTime X τ j =
      rigidRotationGauge (finiteAncestorAngularVelocity A₀ b j) 0 t •
        ((radScale R ρ j)⁻¹ • (fun i => X t (j, i))) := by
  unfold canonicalPrefixAbsoluteCell normalizedPhysicalCurve
  rw [htime]

theorem canonicalPrefixAbsoluteCell_raw {γ : ℝ≥0} {A₀ b R ρ : ℝ}
    (hR : 0 < R) (hρ : 0 < ρ) (k : ℕ) (aTime τ : ℝ)
    (X : ℝ → FiniteCircularIndex k → LittleContourSpace γ) (j : Fin (k + 1)) :
    radScale R ρ j •
      (exp ((((physicalTimeFromNormalized (ampScale A₀ b k) aTime τ) *
        finiteAncestorAngularVelocity A₀ b j : ℝ) : ℂ) * I) •
        canonicalPrefixAbsoluteCell A₀ b R ρ k aTime X τ j) =
      fun i => X (physicalTimeFromNormalized (ampScale A₀ b k) aTime τ) (j, i) := by
  unfold canonicalPrefixAbsoluteCell normalizedPhysicalCurve
  rw [smul_smul (exp _) (rigidRotationGauge _ _ _), exp_rigidRotationGauge_cancel,
    one_smul, smul_smul, mul_inv_cancel₀ (radScale_pos hR hρ j).ne', one_smul]

theorem canonicalPrefixAbsolute_reference_clock {A₀ b : ℝ} (hA : A₀ ≠ 0) (hb : b ≠ 0)
    {j k : ℕ} (hjk : j ≤ k) (aTime τ : ℝ) :
    ampScale A₀ b j * aTime + b ^ (k - j) * τ =
      ampScale A₀ b j * physicalTimeFromNormalized (ampScale A₀ b k) aTime τ := by
  rw [← ampScale_ratio_eq_pow hA hb hjk]
  unfold physicalTimeFromNormalized
  ring

end Euler2D

end
