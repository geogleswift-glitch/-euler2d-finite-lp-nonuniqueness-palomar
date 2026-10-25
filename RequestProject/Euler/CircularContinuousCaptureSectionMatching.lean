module

public import RequestProject.Euler.CircularActualCaptureScaleError

/-! A continuous actual co-frame section matches one fixed canonical
ancient section, with its quantitative error and its original first
crossing time. The canonical time precedes the actual path, its horizon
and its error budget. The off-graph bound can be supplied by the actual
scale-error theorem, rather than postulated for the application. -/

@[expose] public section

set_option maxHeartbeats 16000000
set_option maxRecDepth 6500

noncomputable section

open Set Filter Topology Metric
open scoped NNReal ContDiff

namespace Euler2D

attribute [local instance 2000] quadraticReferenceC1_group localGraphLittle_group localGraphLittle_space
  localGraphFamily_tower localGraphTangent_group localGraphTangent_space
  localGraphTangent_complete localGraphTangent_continuousAdd

attribute [local irreducible] circularBanachField circularBanachDomain circularCoRotationCLM
  littleCircularReference circularConstrainedTangentSubmodule circularConstrainedChart
  circularConstraintProjectionToTangentCLM circularConstrainedReturnMap circularConstrainedUnstableProjectionCLM
  circularCoRotatedConstrainedMap contourC1GraphSubmodule holderGraphSubmodule

namespace CircularMaterialTransferProfile

variable {γ : ℝ≥0} {hγ : 0 < γ} {hγ1 : (γ : ℝ) < 1} (P : CircularMaterialTransferProfile hγ hγ1)

theorem exists_continuous_capture_section_matching_constants {R r : ℝ} (hR : 0 < R) (hr : 0 < r)
    {X : (Fin 2 → LittleContourSpace γ) → ℝ → Fin 2 → LittleContourSpace γ}
    (hX : IsBanachFlowOn (circularBanachField hγ hγ1) (circularBanachDomain hγ hγ1)
      (ball (littleCircularReference hγ hγ1) R) period X)
    (hd : DifferentiableAt ℝ (fun W => X W period) (littleCircularReference hγ hγ1))
    (hfix : X (littleCircularReference hγ hγ1) period = littleCircularReference hγ hγ1)
    (hareaX : ∀ W ∈ ball (littleCircularReference hγ hγ1) R, ∀ i,
      littleContourArea γ (X W period i) = littleContourArea γ (W i))
    {x : CircularConstrainedTangentSpace γ → ℕ → CircularConstrainedTangentSpace γ}
    (hg : IsLocalWeightedBackwardGraph
      (banachDoubleReturn (circularConstrainedReturnMap hγ hγ1 (fun W => X W period)))
      (circularConstrainedUnstableProjectionCLM hγ hγ1.le) circularAncientBackwardWeight r x)
    (hsamples : ∃ N : ℕ, ∀ n ≥ N, ∃ ξ : CircularConstrainedTangentSpace γ,
      circularConstrainedUnstableProjectionCLM hγ hγ1.le ξ = ξ ∧ ‖ξ‖ ≤ r / 2 ∧
      P.ancient (-(n : ℝ) * (period + period)) = circularConstrainedChart hγ hγ1 (x ξ 0)) :
    ∃ d > 0, d ≤ r / 2 ∧ ∃ ε > 0, ∃ C > 0,
      ∀ δ ∈ Ioo (0 : ℝ) d, ∃ s < 0,
        ‖P.coRotatedAncientGraphBase s‖ = δ ∧
        ∀ {D error : ℝ} (y : ℝ → Fin 2 → LittleContourSpace γ),
          HasFirstCircularCoRotatedCaptureSection hγ hγ1 y D δ →
          (∀ t ∈ Icc (0 : ℝ) D, ‖y t - littleCircularMaterialContours hγ hγ1 t‖ < ε) →
          (∀ t ∈ Icc (0 : ℝ) D, ∀ i, y t i ∈ fourfoldLittleContourSubmodule γ) →
          (∀ t ∈ Icc (0 : ℝ) D, ∀ i, littleContourArea γ (y t i) = Real.pi * circularContourRadii i ^ 2) →
          (∀ t ∈ Icc (0 : ℝ) D,
            let v := circularConstraintProjectionToTangentCLM hγ hγ1.le
              (circularCoRotationCLM γ t (y t) - littleCircularReference hγ hγ1)
            ‖v - x (circularConstrainedUnstableProjectionCLM hγ hγ1.le v) 0‖ ≤ error) →
          ∃ τ ∈ Ioc (0 : ℝ) D, ∃ b : ℝ,
            ‖circularCoRotationCLM γ τ (y τ) -
              contourRotationFamilyLittleCLM γ b (circularCoRotationCLM γ s (P.ancient s))‖ ≤ C * error ∧
            ∀ u ∈ Ico (0 : ℝ) τ,
              ‖circularConstrainedUnstableProjectionCLM hγ hγ1.le
                (circularConstraintProjectionToTangentCLM hγ hγ1.le
                  (circularCoRotationCLM γ u (y u) - littleCircularReference hγ hγ1))‖ < δ := by
  obtain ⟨d, hdpos, hdr, ε, hε, C, hC, hmatch⟩ :=
    P.exists_actual_same_graph_canonical_section_matching hR hr hX hd hfix hareaX hg hsamples
  refine ⟨d, hdpos, hdr, ε, hε, C, hC, ?_⟩
  intro δ hδ
  obtain ⟨s, hs, hsδ, hsection⟩ := hmatch δ hδ
  refine ⟨s, hs, hsδ, ?_⟩
  intro D error y hfirst hnear hfour harea hoff
  obtain ⟨τ, hτ, hvalue, hbefore⟩ := hfirst
  have hτD : τ ∈ Icc (0 : ℝ) D := ⟨hτ.1.le, hτ.2⟩
  let Z := circularCoRotationCLM γ τ (y τ)
  have hZ : Z ∈ ball (littleCircularReference hγ hγ1) ε := by
    apply mem_ball_iff_norm.mpr
    change ‖circularCoRotationCLM γ τ (y τ) - littleCircularReference hγ hγ1‖ < ε
    rw [norm_circularCoRotationCLM_sub_reference hγ hγ1 τ]
    exact hnear τ hτD
  have hfourZ := circularCoRotationCLM_fourfold τ (y τ) (hfour τ hτD)
  have hareaZ (i : Fin 2) : littleContourArea γ (Z i) = Real.pi * circularContourRadii i ^ 2 :=
    (circularCoRotationCLM_area τ (y τ) i).trans (harea τ hτD i)
  obtain ⟨b, _, hbound⟩ := hsection Z hZ hfourZ hareaZ hvalue
  exact ⟨τ, hτ, b, hbound.trans (mul_le_mul_of_nonneg_left (hoff τ hτD) hC.le), hbefore⟩

end CircularMaterialTransferProfile
end Euler2D

end
