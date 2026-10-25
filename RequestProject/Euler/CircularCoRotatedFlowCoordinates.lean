module

public import RequestProject.Euler.CircularCoRotatedFlow
public import RequestProject.Euler.CircularActualConstraintChart
public import RequestProject.Euler.CircularAreaChartQuadratic
public import RequestProject.Euler.CircularPhaseArea
public import RequestProject.Euler.BanachUniformProjectedChartBound

/-! The actual co-rotated flow has the original area coordinates on
one common neighborhood for an entire compact time window. Its bound
and inverse identity are obtained from the same actual material flow. -/

@[expose] public section

set_option maxHeartbeats 6000000
set_option maxRecDepth 6000

noncomputable section

open Set Filter Topology Metric
open scoped NNReal ContDiff

namespace Euler2D

attribute [local instance 2000] returnConjugacyLittle_group returnConjugacyLittle_space
  returnConjugacyFamily_tower returnConjugacyTangent_group returnConjugacyTangent_space
  returnConjugacyTangent_continuousAdd

def circularCoRotatedConstrainedMap {γ : ℝ≥0} (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1)
    (X : (Fin 2 → LittleContourSpace γ) → ℝ → Fin 2 → LittleContourSpace γ) (t : ℝ) :
    CircularConstrainedTangentSpace γ → CircularConstrainedTangentSpace γ :=
  circularConstrainedReturnMap hγ hγ1 (fun W => circularCoRotationCLM γ t (X W t))

theorem circularCoRotationCLM_area {γ : ℝ≥0} (t : ℝ) (W : Fin 2 → LittleContourSpace γ) (i : Fin 2) :
    littleContourArea γ (circularCoRotationCLM γ t W i) = littleContourArea γ (W i) := by
  exact contourArea_parameterShiftC1 (-circularContourAngularVelocities i * t) (W i).val

theorem circularCoRotationCLM_fourfold {γ : ℝ≥0} (t : ℝ) (W : Fin 2 → LittleContourSpace γ)
    (hW : ∀ i, W i ∈ fourfoldLittleContourSubmodule γ) :
    ∀ i, circularCoRotationCLM γ t W i ∈ fourfoldLittleContourSubmodule γ := by
  intro i
  have hi : contourRotationLittleCLM γ (Real.pi / 2) (W i) = W i := by
    have hh := hW i
    change contourRotationLittleCLM γ (Real.pi / 2) (W i) - W i = 0 at hh
    exact sub_eq_zero.mp hh
  change contourRotationLittleCLM γ (Real.pi / 2)
    (contourParameterShiftLittleCLM γ (-circularContourAngularVelocities i * t) (W i)) -
      contourParameterShiftLittleCLM γ (-circularContourAngularVelocities i * t) (W i) = 0
  rw [← contourRotationLittleCLM_parameterShift_comm, hi, sub_self]

attribute [local irreducible] circularBanachField circularBanachDomain circularCoRotationCLM
  littleCircularReference littleCircularMaterialContours circularConstrainedTangentSubmodule
  circularConstraintProjectionToTangentCLM circularConstrainedChart circularConstrainedReturnMap
  circularCoRotatedConstrainedMap contourC1GraphSubmodule holderGraphSubmodule

theorem exists_circularCoRotatedFlow_uniform_constraint_coordinates {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1) {T R d : ℝ}
    (hT : 0 < T) (hR : 0 < R) (hd : 0 < d)
    {X : (Fin 2 → LittleContourSpace γ) → ℝ → Fin 2 → LittleContourSpace γ}
    (hX : IsBanachFlowOn (circularBanachField hγ hγ1) (circularBanachDomain hγ hγ1)
      (ball (littleCircularReference hγ hγ1) R) T X)
    (harea : ∀ W ∈ ball (littleCircularReference hγ hγ1) R, ∀ t ∈ Icc (0 : ℝ) T, ∀ i,
      littleContourArea γ (X W t i) = littleContourArea γ (W i)) :
    ∃ η > 0, ∃ C > 0, ∀ v : CircularConstrainedTangentSpace γ, ‖v‖ < η →
      circularConstrainedChart hγ hγ1 v ∈ ball (littleCircularReference hγ hγ1) R ∧
      ∀ t ∈ Icc (0 : ℝ) T,
        circularCoRotationCLM γ t (X (circularConstrainedChart hγ hγ1 v) t) ∈
          ball (littleCircularReference hγ hγ1) d ∧
        ‖circularCoRotatedConstrainedMap hγ hγ1 X t v‖ ≤ C * ‖v‖ ∧
        circularConstrainedChart hγ hγ1 (circularCoRotatedConstrainedMap hγ hγ1 X t v) =
          circularCoRotationCLM γ t (X (circularConstrainedChart hγ hγ1 v) t) := by
  let Φ := circularConstrainedChart hγ hγ1
  let c := littleCircularReference hγ hγ1
  let Qproj := circularConstraintProjectionToTangentCLM hγ hγ1.le
  obtain ⟨δ, hδ, Cf, hCf, hflow⟩ := exists_circularCoRotatedFlow_uniform_linear_bound hγ hγ1 hT hR hX
  obtain ⟨a, ha, hinverse⟩ := exists_circular_actualConstraintChart_radius hγ hγ1
  obtain ⟨Cq, hCq, r, hr, hchart⟩ := exists_circularConstrainedChart_quadratic_bound hγ hγ1
  let K := 1 + Cq * r
  have hK : 0 < K := by dsimp only [K]; positivity
  have hΦc : ContinuousAt Φ 0 := (hasFDerivAt_circularConstrainedChart_zero hγ hγ1).continuousAt
  have hΦ0 : Φ 0 = c := circularConstrainedChart_zero hγ hγ1
  obtain ⟨b, hb, C, hC, hbound⟩ := exists_uniform_projected_chart_bound hΦc hΦ0 Qproj
    hr hK hδ hCf hR (lt_min hd ha)
    (fun v hv => (hchart v (by simpa only [mem_closedBall, dist_zero_right] using hv)).2)
    (fun t : Icc (0 : ℝ) T => fun W => circularCoRotationCLM γ t.val (X W t.val))
    (fun t W hW => hflow W hW t.val t.property)
  have hnear : ∀ᶠ v in 𝓝 (0 : CircularConstrainedTangentSpace γ), ‖v‖ < b :=
    (continuous_norm.tendsto _).eventually (eventually_lt_nhds (by simpa only [norm_zero] using hb))
  obtain ⟨η, hη, hspec⟩ := Metric.eventually_nhds_iff.mp
    (hnear.and (eventually_circularConstrainedChart_positive hγ hγ1))
  refine ⟨η, hη, C, hC, ?_⟩
  intro v hv
  obtain ⟨hvb, hpos⟩ := hspec (by simpa only [dist_zero_right] using hv)
  have hvR : Φ v ∈ ball c R := (hbound v hvb).1
  refine ⟨hvR, ?_⟩
  intro t ht
  let Z := circularCoRotationCLM γ t (X (Φ v) t)
  have hZball : Z ∈ ball c (min d a) := ((hbound v hvb).2.2 ⟨t, ht⟩).1
  have hZfour : ∀ i, Z i ∈ fourfoldLittleContourSubmodule γ :=
    circularCoRotationCLM_fourfold t _ (fun i =>
      circularBanachFlow_fourfold hγ hγ1 hX hvR (circularConstrainedChart_fourfold hγ hγ1 v) ht i)
  have hZarea (i : Fin 2) : littleContourArea γ (Z i) = Real.pi * circularContourRadii i ^ 2 :=
    (circularCoRotationCLM_area t _ i).trans
      ((harea (Φ v) hvR t ht i).trans (circularConstrainedChart_area hγ hγ1 v hpos i))
  refine ⟨ball_subset_ball (min_le_left _ _) hZball, ?_, ?_⟩
  · unfold circularCoRotatedConstrainedMap circularConstrainedReturnMap
    change ‖Qproj (Z - c)‖ ≤ C * ‖v‖
    exact ((hbound v hvb).2.2 ⟨t, ht⟩).2
  · unfold circularCoRotatedConstrainedMap circularConstrainedReturnMap
    change Φ (Qproj (Z - c)) = Z
    exact hinverse Z (ball_subset_ball (min_le_right _ _) hZball) hZfour hZarea

end Euler2D

end
