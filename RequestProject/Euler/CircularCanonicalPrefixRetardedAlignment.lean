module

public import RequestProject.Euler.CircularCanonicalPrefixCellDerivative
public import RequestProject.Euler.CircularRetardedLabelDeviation
public import RequestProject.Euler.CircularActualPrefixRotatedDerivative

/-! The one fixed stage gauge of the actual canonical X reconstructs
its literal raw contours. Retarded geometric shifts therefore give
the true own deviation of that same Y, with no dynamics reset. -/

@[expose] public section

set_option maxHeartbeats 9000000
set_option maxRecDepth 5000

noncomputable section

open Complex Set MeasureTheory Metric
open scoped NNReal ENNReal

namespace Euler2D

attribute [local instance 2000] rigidGaugeLittle_group rigidGaugeLittle_space rigidGaugeFamily_tower
attribute [local instance] LittleContourSpace.complexScalarNormedSpace LittleContourSpace.complexScalarTower

def canonicalPrefixRotatedCell {γ : ℝ≥0} (A₀ b R ρ : ℝ) (k : ℕ) (aTime : ℝ)
    (X : ℝ → FiniteCircularIndex k → LittleContourSpace γ) (τ : ℝ) (j : Fin (k + 1)) :
    Fin 2 → LittleContourSpace γ :=
  rigidRotationGauge (finiteAncestorAngularVelocity A₀ b j / ampScale A₀ b k) 0 τ •
    normalizedPhysicalCurve (ampScale A₀ b k) (radScale R ρ j) aTime (fun t i => X t (j, i)) τ

def canonicalPrefixRotatedExtension {γ : ℝ≥0} (A₀ b R ρ : ℝ) {N k : ℕ} (aTime : ℝ)
    (X : ℝ → FiniteCircularIndex k → LittleContourSpace γ) (τ : ℝ) (l : Fin (N + 1)) :
    Fin 2 → LittleContourSpace γ :=
  if hl : (l : ℕ) ≤ k then canonicalPrefixRotatedCell A₀ b R ρ k aTime X τ ⟨l, Nat.lt_succ_of_le hl⟩ else 0

theorem exp_rigidRotationGauge_cancel (ω τ : ℝ) :
    exp (((τ * ω : ℝ) : ℂ) * I) * rigidRotationGauge ω 0 τ = 1 := by
  unfold rigidRotationGauge
  rw [← exp_add]
  convert exp_zero using 1
  congr 1
  push_cast
  ring

theorem canonicalPrefixRotatedCell_raw {γ : ℝ≥0} {A₀ b R ρ : ℝ}
    (hR : 0 < R) (hρ : 0 < ρ) (k : ℕ) (aTime τ : ℝ)
    (X : ℝ → FiniteCircularIndex k → LittleContourSpace γ) (j : Fin (k + 1)) :
    radScale R ρ j •
      (exp (((τ * (finiteAncestorAngularVelocity A₀ b j / ampScale A₀ b k) : ℝ) : ℂ) * I) •
        canonicalPrefixRotatedCell A₀ b R ρ k aTime X τ j) =
      fun i => X (physicalTimeFromNormalized (ampScale A₀ b k) aTime τ) (j, i) := by
  unfold canonicalPrefixRotatedCell normalizedPhysicalCurve
  rw [smul_smul (exp _) (rigidRotationGauge _ _ _), exp_rigidRotationGauge_cancel,
    one_smul, smul_smul, mul_inv_cancel₀ (radScale_pos hR hρ j).ne', one_smul]

namespace CircularMaterialTransferProfile

variable {γ : ℝ≥0} {hγ : 0 < γ} {hγ1 : (γ : ℝ) < 1}
    (P : CircularMaterialTransferProfile hγ hγ1)

theorem actualCanonicalPrefix_retarded_raw
    {s A₀ b R ρ c δ : ℝ} (hR : 0 < R) (hρ : 0 < ρ)
    {N k : ℕ} (hkN : k ≤ N) {f : Lp ℝ 2 μT} {T : ℝ}
    (S : BoundedEulerParticleSystem f T) (t : ℝ)
    (G : P.FiniteOuterMaterialTube s R ρ N k S t c δ)
    (X : ℝ → FiniteCircularIndex k → LittleContourSpace γ)
    (hG : ∀ p, G.contours (finiteCircularPrefixIndex hkN p) = (X t p).val)
    (aTime τ : ℝ) (htime : physicalTimeFromNormalized (ampScale A₀ b k) aTime τ = t)
    (l : Fin (N + 1)) (hl : (l : ℕ) ≤ k) (i : Fin 2) :
    G.contours (l, i) =
      (radScale R ρ l •
        (exp (((τ * (finiteAncestorAngularVelocity A₀ b l / ampScale A₀ b k) : ℝ) : ℂ) * I) •
          canonicalPrefixRotatedExtension A₀ b R ρ aTime X τ l i)).val := by
  let ll : Fin (k + 1) := ⟨l, Nat.lt_succ_of_le hl⟩
  have hr := congrArg (fun W : Fin 2 → LittleContourSpace γ => (W i).val)
    (canonicalPrefixRotatedCell_raw (A₀ := A₀) (b := b) hR hρ k aTime τ X ll)
  rw [htime] at hr
  have hGi : G.contours (l, i) = (X t (ll, i)).val := hG (ll, i)
  rw [hGi]
  simpa only [canonicalPrefixRotatedExtension, dif_pos hl, Pi.smul_apply] using hr.symm

theorem actualCanonicalPrefix_retarded_ownDeviation
    {s A₀ b R ρ c δ : ℝ} (hR : 0 < R) (hρ : 0 < ρ)
    {N k : ℕ} (hkN : k ≤ N) {f : Lp ℝ 2 μT} {T : ℝ}
    (S : BoundedEulerParticleSystem f T) (t : ℝ)
    (G : P.FiniteOuterMaterialTube s R ρ N k S t c δ)
    (X : ℝ → FiniteCircularIndex k → LittleContourSpace γ)
    (hG : ∀ p, G.contours (finiteCircularPrefixIndex hkN p) = (X t p).val)
    (aTime τ : ℝ) (htime : physicalTimeFromNormalized (ampScale A₀ b k) aTime τ = t)
    (u : Fin (N + 1) → ℝ)
    (hsmall : circularRetardedPrefixDeviation hγ hγ1 k
      (canonicalPrefixRotatedExtension A₀ b R ρ aTime X τ) u ≤ cellA / 4) :
    ∃ G' : P.FiniteOuterMaterialTube s R ρ N k S t c
        (circularRetardedPrefixDeviation hγ hγ1 k (canonicalPrefixRotatedExtension A₀ b R ρ aTime X τ) u),
      G'.contours = G.contours ∧ ∀ (l : Fin (N + 1)), (l : ℕ) ≤ k → ∀ i,
        ‖contourParameterShiftC1 (G'.shifts (l, i)) (G'.contours (l, i)) - G'.reference (l, i)‖ ≤
          radScale R ρ l * ‖canonicalPrefixRotatedExtension A₀ b R ρ aTime X τ l -
            littleCircularMaterialContours hγ hγ1 (u l)‖ := by
  let Y : Fin (N + 1) → Fin 2 → LittleContourSpace γ :=
    canonicalPrefixRotatedExtension A₀ b R ρ aTime X τ
  let φ := fun l : Fin (N + 1) => τ * (finiteAncestorAngularVelocity A₀ b l / ampScale A₀ b k)
  have hraw := P.actualCanonicalPrefix_retarded_raw hR hρ hkN S t G X hG aTime τ htime
  let G' := P.finiteOuterMaterialTubeOfRetardedFamily hR hρ G Y u φ hraw hsmall
  refine ⟨G', rfl, ?_⟩
  intro l hl i
  exact P.finiteRetardedTube_relative_label hR hρ G Y u φ hraw hsmall l hl i

end CircularMaterialTransferProfile
end Euler2D

end
