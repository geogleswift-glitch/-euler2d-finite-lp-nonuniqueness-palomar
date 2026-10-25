module

public import RequestProject.Euler.CircularCoRotatedFlowCoordinates
public import RequestProject.Euler.ContourLittleShiftContinuity

/-! The original co-parameter frame is continuous along every actual
continuous material curve in the little norm. Only strong continuity
and the genuine isometry are used; no extra time derivative is assumed. -/

@[expose] public section

set_option maxHeartbeats 6000000
set_option maxRecDepth 6000

noncomputable section

open Set Filter Topology Metric
open scoped NNReal ContDiff

namespace Euler2D

theorem continuousOn_isometric_family_apply {A E : Type*}
    [PseudoMetricSpace A] [PseudoMetricSpace E] {J : Set A}
    (S : A → E → E) (hiso : ∀ t, Isometry (S t))
    (hstrong : ∀ z, ContinuousOn (fun t => S t z) J)
    {y : A → E} (hy : ContinuousOn y J) :
    ContinuousOn (fun t => S t (y t)) J := by
  intro t ht
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  obtain ⟨d₁, hd₁, h₁⟩ := (Metric.continuousWithinAt_iff.mp (hy t ht)) (ε / 2) (half_pos hε)
  obtain ⟨d₂, hd₂, h₂⟩ := (Metric.continuousWithinAt_iff.mp (hstrong (y t) t ht)) (ε / 2) (half_pos hε)
  refine ⟨min d₁ d₂, lt_min hd₁ hd₂, ?_⟩
  intro s hs hst
  calc
    dist (S s (y s)) (S t (y t)) ≤
        dist (S s (y s)) (S s (y t)) + dist (S s (y t)) (S t (y t)) := dist_triangle _ _ _
    _ = dist (y s) (y t) + dist (S s (y t)) (S t (y t)) := by rw [(hiso s).dist_eq]
    _ < ε / 2 + ε / 2 := add_lt_add
      (h₁ hs (hst.trans_le (min_le_left _ _))) (h₂ hs (hst.trans_le (min_le_right _ _)))
    _ = ε := by ring

attribute [local instance 2000] quadraticReferenceC1_group quadraticReferenceLittle_group
  quadraticReferenceLittle_space quadraticReferenceFamily_tower
  returnConjugacyTangent_group returnConjugacyTangent_space returnConjugacyTangent_continuousAdd

theorem isometry_circularCoRotationCLM (γ : ℝ≥0) (t : ℝ) :
    Isometry (circularCoRotationCLM γ t) := by
  exact (contourParameterShiftFamilyIsometry γ (fun i : Fin 2 => -circularContourAngularVelocities i * t)).isometry

theorem continuous_circularCoRotationCLM_apply {γ : ℝ≥0} (hγ1 : γ ≤ 1)
    (Z : Fin 2 → LittleContourSpace γ) :
    Continuous (fun t : ℝ => circularCoRotationCLM γ t Z) := by
  have hp : Continuous (fun t : ℝ => fun i : Fin 2 => -circularContourAngularVelocities i * t) := by
    apply continuous_pi
    intro i
    exact continuous_const.mul continuous_id
  exact (continuous_contourParameterShiftFamilyCLM hγ1 Z).comp hp

theorem continuousOn_circularCoRotatedCurve {γ : ℝ≥0} (hγ1 : γ ≤ 1)
    {J : Set ℝ} {y : ℝ → Fin 2 → LittleContourSpace γ} (hy : ContinuousOn y J) :
    ContinuousOn (fun t => circularCoRotationCLM γ t (y t)) J :=
  continuousOn_isometric_family_apply (fun t => circularCoRotationCLM γ t)
    (isometry_circularCoRotationCLM γ)
    (fun Z => (continuous_circularCoRotationCLM_apply hγ1 Z).continuousOn) hy

attribute [local irreducible] circularConstrainedTangentSubmodule circularBanachField circularBanachDomain
  circularConstrainedChart circularConstraintProjectionToTangentCLM circularCoRotationCLM
  contourC1GraphSubmodule holderGraphSubmodule

theorem continuousOn_circularCoRotatedConstrainedMap {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1) {V : Set (Fin 2 → LittleContourSpace γ)} {T : ℝ}
    {X : (Fin 2 → LittleContourSpace γ) → ℝ → Fin 2 → LittleContourSpace γ}
    (hX : IsBanachFlowOn (circularBanachField hγ hγ1) (circularBanachDomain hγ hγ1) V T X)
    (v : CircularConstrainedTangentSpace γ) (hv : circularConstrainedChart hγ hγ1 v ∈ V) :
    ContinuousOn (fun t => circularCoRotatedConstrainedMap hγ hγ1 X t v) (Icc (0 : ℝ) T) := by
  have hc := continuousOn_circularCoRotatedCurve hγ1.le (hX.continuous _ hv)
  unfold circularCoRotatedConstrainedMap circularConstrainedReturnMap
  exact (circularConstraintProjectionToTangentCLM hγ hγ1.le).continuous.comp_continuousOn
    (hc.sub continuousOn_const)

end Euler2D

end
