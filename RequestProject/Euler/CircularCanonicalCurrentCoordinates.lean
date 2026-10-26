module

public import RequestProject.Euler.CircularCanonicalStageDeviation
public import RequestProject.Euler.CircularPrefixNormalizedDomain
public import RequestProject.Euler.CircularFiniteAlignedConstraints
public import RequestProject.Euler.CircularFinitePrefixPlanarRows

/-! One fixed current-cell material alignment of the same canonical
path. Its norm is exactly the original stage deviation. Its isolated
domain and original constraint coordinates follow from actual geometry. -/

@[expose] public section

set_option maxHeartbeats 12000000
set_option maxRecDepth 5500

noncomputable section

open Complex Set MeasureTheory Metric
open scoped NNReal ENNReal

namespace Euler2D

attribute [local instance 2000] rigidGaugeLittle_group rigidGaugeLittle_space rigidGaugeFamily_tower
attribute [local instance] LittleContourSpace.complexScalarNormedSpace LittleContourSpace.complexScalarTower
attribute [local irreducible] circularBanachField circularBanachDomain

def canonicalPrefixAlignedCurrentCell {γ : ℝ≥0} (A₀ b R ρ : ℝ) (k : ℕ) (entrance : ℝ)
    (X : ℝ → FiniteCircularIndex k → LittleContourSpace γ) (τ : ℝ) :
    Fin 2 → LittleContourSpace γ :=
  contourParameterShiftFamilyCLM γ (circularRetardedMaterialShift 0 (ampScale A₀ b k * entrance))
    (canonicalPrefixAbsoluteCell A₀ b R ρ k entrance X τ (Fin.last k))

theorem norm_canonicalPrefixAlignedCurrentCell_sub_reference {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1) (A₀ b R ρ : ℝ) (k : ℕ) (entrance τ : ℝ)
    (X : ℝ → FiniteCircularIndex k → LittleContourSpace γ) :
    ‖canonicalPrefixAlignedCurrentCell A₀ b R ρ k entrance X τ -
      littleCircularMaterialContours hγ hγ1 τ‖ =
        ‖canonicalPrefixStageDeviation hγ hγ1 A₀ b R ρ k entrance X τ k‖ := by
  have hh := norm_circularFixedEntranceShift_sub_reference hγ hγ1 0
    (ampScale A₀ b k * entrance) τ
    (canonicalPrefixAbsoluteCell A₀ b R ρ k entrance X τ (Fin.last k))
  simpa only [canonicalPrefixAlignedCurrentCell, canonicalPrefixStageDeviation,
    canonicalPrefixAbsoluteFamily, dif_pos (le_refl k), Nat.sub_self, pow_zero, one_mul,
    Complex.ofReal_zero, zero_mul, exp_zero, one_smul, Fin.last] using hh

theorem canonicalPrefixAbsoluteCell_mem_circularDomain {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1) {R ρ : ℝ} (hR : 0 < R) (hρ : 0 < ρ)
    (A₀ b : ℝ) (k : ℕ) (X : ℝ → FiniteCircularIndex k → LittleContourSpace γ) (t : ℝ)
    (hphase : IsPhaseAdmissibleLittleContourFamily (finiteCircularReferenceC1 hγ hγ1 R ρ)
      (finiteCircularInterfaceRadius R ρ) (X t))
    (hquarter : IsQuarterPhaseLittleContourFamily (finiteCircularReferenceC1 hγ hγ1 R ρ)
      (finiteCircularInterfaceRadius R ρ) (X t))
    (j : Fin (k + 1)) (entrance τ : ℝ)
    (htime : physicalTimeFromNormalized (ampScale A₀ b k) entrance τ = t) :
    canonicalPrefixAbsoluteCell A₀ b R ρ k entrance X τ j ∈ circularBanachDomain hγ hγ1 := by
  rw [canonicalPrefixAbsoluteCell_eq_physicalState A₀ b R ρ k entrance τ t X j htime]
  exact circularRigidRotatedCurve_mem hγ hγ1 (finiteAncestorAngularVelocity A₀ b j) 0 t
    (normalizedFiniteCircularCell_mem_quarterPhaseDomain hγ hγ1 hR hρ (X t) hphase hquarter j).1

theorem canonicalPrefixAlignedCurrentCell_mem_circularDomain {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1) {R ρ : ℝ} (hR : 0 < R) (hρ : 0 < ρ)
    (A₀ b : ℝ) (k : ℕ) (X : ℝ → FiniteCircularIndex k → LittleContourSpace γ) (t : ℝ)
    (hphase : IsPhaseAdmissibleLittleContourFamily (finiteCircularReferenceC1 hγ hγ1 R ρ)
      (finiteCircularInterfaceRadius R ρ) (X t))
    (hquarter : IsQuarterPhaseLittleContourFamily (finiteCircularReferenceC1 hγ hγ1 R ρ)
      (finiteCircularInterfaceRadius R ρ) (X t))
    (entrance τ : ℝ) (htime : physicalTimeFromNormalized (ampScale A₀ b k) entrance τ = t) :
    canonicalPrefixAlignedCurrentCell A₀ b R ρ k entrance X τ ∈ circularBanachDomain hγ hγ1 := by
  exact circularBanachDomain_parameterShift hγ hγ1 _
    (canonicalPrefixAbsoluteCell_mem_circularDomain hγ hγ1 hR hρ A₀ b k X t hphase hquarter
      (Fin.last k) entrance τ htime)

namespace CircularMaterialTransferProfile

variable {γ : ℝ≥0} {hγ : 0 < γ} {hγ1 : (γ : ℝ) < 1}
    (P : CircularMaterialTransferProfile hγ hγ1)

theorem exists_uniform_actualCanonical_alignedCurrent_constraintChart_radius :
    ∃ ε > 0, ∀ {s R ρ η A₀ b entrance τ t : ℝ}, s ≤ 0 →
      ∀ (hR : 0 < R) (hρ : 0 < ρ), 0 ≤ η → η ≤ cellA / 4 →
      (∀ i, ‖(P.ancient s i).val - circularReferenceC1 hγ hγ1 i‖ ≤ η) →
      ∀ {N k : ℕ} (hkN : k ≤ N) {f : Lp ℝ 2 μT} {T : ℝ}
        {S : BoundedEulerParticleSystem f T} {c δ : ℝ},
      t ∈ Icc (0 : ℝ) T → ∀ G : P.FiniteOuterMaterialTube s R ρ N k S t c δ,
      ∀ X : ℝ → FiniteCircularIndex k → LittleContourSpace γ,
      (∀ p, G.contours (finiteCircularPrefixIndex hkN p) = (X t p).val) →
      physicalTimeFromNormalized (ampScale A₀ b k) entrance τ = t →
      canonicalPrefixAlignedCurrentCell A₀ b R ρ k entrance X τ ∈
        ball (littleCircularReference hγ hγ1) ε →
      circularConstrainedChart hγ hγ1
        (circularConstraintProjectionToTangentCLM hγ hγ1.le
          (canonicalPrefixAlignedCurrentCell A₀ b R ρ k entrance X τ - littleCircularReference hγ hγ1)) =
            canonicalPrefixAlignedCurrentCell A₀ b R ρ k entrance X τ := by
  obtain ⟨ε, hε, hchart⟩ := P.exists_uniform_actualMaterial_aligned_constraintChart_radius
  refine ⟨ε, hε, ?_⟩
  intro s R ρ η A₀ b entrance τ t hs hR hρ hη hηa hancient N k hkN f T S c δ ht G X hG htime hnear
  apply hchart hs hR hρ hη hηa hancient ht G (finitePrefixForcingIndex hkN (Fin.last k))
    (by simp only [finitePrefixForcingIndex, Fin.val_last, le_refl])
    (t * finiteAncestorAngularVelocity A₀ b k)
    (canonicalPrefixAbsoluteCell A₀ b R ρ k entrance X τ (Fin.last k)) ?_
    (circularRetardedMaterialShift 0 (ampScale A₀ b k * entrance)) hnear
  intro i
  have hh := congrArg (fun V : Fin 2 → LittleContourSpace γ => (V i).val)
    (canonicalPrefixAbsoluteCell_raw (A₀ := A₀) (b := b) hR hρ k entrance τ X (Fin.last k))
  rw [htime] at hh
  simpa only [finitePrefixForcingIndex, finiteCircularPrefixIndex, Fin.val_last, Pi.smul_apply] using
    (hG (Fin.last k, i)).trans hh.symm

end CircularMaterialTransferProfile
end Euler2D

end
