module

public import RequestProject.Euler.CircularSameFlowExistingBlockComparison
public import RequestProject.Euler.CircularPhysicalRotatingFrame

/-! The actual physical trajectory, after its exact entrance-centered
normalization and removal of the real ancestor angular velocity, is
compared directly to the fixed iterate of the same original X. The
constants are chosen before every physical amplitude, radius, entrance
time, forcing, and finite cutoff. -/

@[expose] public section

set_option maxHeartbeats 16000000
set_option maxRecDepth 4000

noncomputable section

open Complex Set Filter Topology Metric
open scoped NNReal ContDiff

namespace Euler2D

attribute [local instance 2000] returnConjugacyLittle_group returnConjugacyLittle_space
  returnConjugacyFamily_tower returnConjugacyTangent_group returnConjugacyTangent_space
  returnConjugacyTangent_continuousAdd rigidGaugeFamily_tower
attribute [local instance] LittleContourSpace.complexScalarNormedSpace LittleContourSpace.complexScalarTower

attribute [local irreducible] circularConstrainedTangentSubmodule
  circularConstrainedReturnMap circularConstrainedChart circularConstraintProjectionToTangentCLM
  circularBanachField circularBanachDomain

theorem exists_circular_sameFlow_physical_existing_block_comparison {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1) {R : ℝ} (hR : 0 < R)
    {X : (Fin 2 → LittleContourSpace γ) → ℝ → Fin 2 → LittleContourSpace γ}
    (hX : IsBanachFlowOn (circularBanachField hγ hγ1) (circularBanachDomain hγ hγ1)
      (ball (littleCircularReference hγ hγ1) R) period X)
    (hd : ContDiffAt ℝ 2 (fun W => X W period) (littleCircularReference hγ hγ1))
    (hfix : X (littleCircularReference hγ hγ1) period = littleCircularReference hγ hγ1)
    (harea : ∀ W ∈ ball (littleCircularReference hγ hγ1) R, ∀ i,
      littleContourArea γ (X W period i) = littleContourArea γ (W i))
    {m : ℕ} (hm : 0 < m) :
    ∃ U : Set (Fin 2 → LittleContourSpace γ), IsOpen U ∧
      U ⊆ circularBanachDomain hγ hγ1 ∧
      U ⊆ ⋃ t : ℝ, ball (littleCircularMaterialContours hγ hγ1 t) (cellA / 4) ∧
      ∃ K : ℝ≥0, ∃ ζ > 0,
        ∀ {A r ε : ℝ}, 0 < A → 0 < r → 0 ≤ ε →
        ∀ e Ω : ℝ, ∀ v ∈ ball (0 : CircularConstrainedTangentSpace γ) ζ,
        ∀ z p : ℝ → Fin 2 → LittleContourSpace γ,
          r⁻¹ • z e = circularConstrainedChart hγ hγ1 v →
          (∀ τ ∈ Icc (0 : ℝ) ((m : ℝ) * period),
            normalizedPhysicalCurve A r e z τ ∈ circularBanachDomain hγ hγ1) →
          (∀ τ ∈ Icc (0 : ℝ) ((m : ℝ) * period),
            HasDerivAt z
              ((A * r) • circularBanachField hγ hγ1
                (r⁻¹ • z (physicalTimeFromNormalized A e τ)) +
                ((Ω : ℂ) * I) • z (physicalTimeFromNormalized A e τ) +
                p (physicalTimeFromNormalized A e τ)) (physicalTimeFromNormalized A e τ)) →
          (∀ τ ∈ Icc (0 : ℝ) ((m : ℝ) * period),
            rigidRotationGauge (Ω / A) 0 τ • normalizedPhysicalCurve A r e z τ ∈ U) →
          (∀ τ ∈ Icc (0 : ℝ) ((m : ℝ) * period),
            ‖p (physicalTimeFromNormalized A e τ)‖ / (A * r) ≤ ε) →
          ‖circularConstraintProjectionToTangentCLM hγ hγ1.le
              ((rigidRotationGauge (Ω / A) 0 ((m : ℝ) * period) •
                normalizedPhysicalCurve A r e z ((m : ℝ) * period)) -
                littleCircularReference hγ hγ1) -
              (circularConstrainedReturnMap hγ hγ1 (fun W => X W period))^[m] v‖ ≤
            ‖circularConstraintProjectionToTangentCLM hγ hγ1.le‖ *
              (ε * ((m : ℝ) * period) * Real.exp ((K : ℝ) * ((m : ℝ) * period))) := by
  obtain ⟨U, hU, hUD, hUref, K, ζ, hζ, hcompare⟩ :=
    exists_circular_sameFlow_existing_block_comparison (γ := γ) (R := R) (X := X)
      hγ hγ1 hR hX hd hfix harea (m := m) hm
  refine ⟨U, hU, hUD, hUref, K, ζ, hζ, ?_⟩
  intro A r ε hA hr hε e Ω v hv z p hinit hmem hzd hym hbudget
  let y : ℝ → Fin 2 → LittleContourSpace γ := fun τ =>
    rigidRotationGauge (Ω / A) 0 τ • normalizedPhysicalCurve A r e z τ
  let q : ℝ → Fin 2 → LittleContourSpace γ := fun τ =>
    rigidRotationGauge (Ω / A) 0 τ • ((A * r)⁻¹ • p (physicalTimeFromNormalized A e τ))
  have hyd (τ : ℝ) (hτ : τ ∈ Icc (0 : ℝ) ((m : ℝ) * period)) :
      HasDerivAt y (circularBanachField hγ hγ1 (y τ) + q τ) τ :=
    hasDerivAt_circularNormalizedPhysicalRotatedCurve hγ hγ1 hA.ne' hr.ne'
      (hmem τ hτ) (hzd τ hτ)
  have hy0 : y 0 = circularConstrainedChart hγ hγ1 v :=
    (circularNormalizedPhysicalRotatedCurve_initial A r e Ω z).trans hinit
  have hyc : ContinuousOn y (Icc (0 : ℝ) ((m : ℝ) * period)) :=
    fun τ hτ => (hyd τ hτ).continuousAt.continuousWithinAt
  have hqb (τ : ℝ) (hτ : τ ∈ Icc (0 : ℝ) ((m : ℝ) * period)) : ‖q τ‖ ≤ ε := by
    change ‖rigidRotationGauge (Ω / A) 0 τ •
      ((A * r)⁻¹ • p (physicalTimeFromNormalized A e τ))‖ ≤ ε
    rw [norm_normalizedPhysicalRotatedForcing hA hr]
    exact hbudget τ hτ
  exact hcompare (ε := ε) hε v hv (y := y) (p := q) hy0 hyc hyd hym hqb

end Euler2D

end
