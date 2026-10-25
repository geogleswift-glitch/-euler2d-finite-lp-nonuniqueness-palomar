module

public import RequestProject.Euler.CircularCanonicalFixedSection
public import RequestProject.Euler.CircularActualConstraintChart

/-! A real nearby contour at a fixed growing-coordinate norm is close
to one fixed section of the same canonical ancient curve. The error is
the actual distance from the already chosen backward graph. -/

@[expose] public section

set_option maxHeartbeats 16000000
set_option maxRecDepth 6000

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
  circularConstrainedRotationCLM contourC1GraphSubmodule holderGraphSubmodule

theorem exists_circularConstrainedChart_local_lipschitz {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1) :
    ∃ a > 0, ∃ C > 0, ∀ v w : CircularConstrainedTangentSpace γ,
      ‖v‖ < a → ‖w‖ < a →
      ‖circularConstrainedChart hγ hγ1 v - circularConstrainedChart hγ hγ1 w‖ ≤ C * ‖v - w‖ := by
  have hf : ContDiffAt ℝ 1 (circularConstrainedChart hγ hγ1) 0 :=
    contDiffAt_circularConstrainedChart hγ hγ1 1 0 (fun i => by
      change 0 < 1 - littleContourArea γ 0 / _
      simp only [littleContourArea_zero, zero_div, sub_zero, zero_lt_one])
  obtain ⟨K, U, hU, hLip⟩ := hf.exists_lipschitzOnWith
  obtain ⟨a, ha, haU⟩ := Metric.mem_nhds_iff.mp hU
  refine ⟨a, ha, (K : ℝ) + 1, by positivity, ?_⟩
  intro v w hv hw
  have hvU : v ∈ U := haU (by simpa only [mem_ball, dist_zero_right] using hv)
  have hwU : w ∈ U := haU (by simpa only [mem_ball, dist_zero_right] using hw)
  have hh : ‖circularConstrainedChart hγ hγ1 v - circularConstrainedChart hγ hγ1 w‖ ≤
      (K : ℝ) * ‖v - w‖ := by
    simpa only [dist_eq_norm] using hLip.dist_le_mul v hvU w hwU
  exact hh.trans (mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _))

namespace CircularMaterialTransferProfile

variable {γ : ℝ≥0} {hγ : 0 < γ} {hγ1 : (γ : ℝ) < 1} (P : CircularMaterialTransferProfile hγ hγ1)

theorem exists_actual_same_graph_canonical_section_matching {R r : ℝ} (hR : 0 < R) (hr : 0 < r)
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
        ∀ Z ∈ ball (littleCircularReference hγ hγ1) ε,
          (∀ i, Z i ∈ fourfoldLittleContourSubmodule γ) →
          (∀ i, littleContourArea γ (Z i) = Real.pi * circularContourRadii i ^ 2) →
          let v := circularConstraintProjectionToTangentCLM hγ hγ1.le
            (Z - littleCircularReference hγ hγ1)
          let ξ := circularConstrainedUnstableProjectionCLM hγ hγ1.le v
          ‖ξ‖ = δ → ∃ b : ℝ,
            circularConstrainedChart hγ hγ1 (x ξ 0) =
              contourRotationFamilyLittleCLM γ b (circularCoRotationCLM γ s (P.ancient s)) ∧
            ‖Z - contourRotationFamilyLittleCLM γ b (circularCoRotationCLM γ s (P.ancient s))‖ ≤
              C * ‖v - x ξ 0‖ := by
  obtain ⟨d₀, hd₀, hd₀r, hsection⟩ :=
    P.exists_same_graph_fixed_canonical_section hR hr hX hd hfix hareaX hg hsamples
  obtain ⟨a, ha, C, hC, hLip⟩ := exists_circularConstrainedChart_local_lipschitz hγ hγ1
  obtain ⟨e, he, hchart⟩ := exists_circular_actualConstraintChart_radius hγ hγ1
  let J := circularConstraintProjectionToTangentCLM hγ hγ1.le
  let Q := circularConstrainedUnstableProjectionCLM hγ hγ1.le
  let d := min d₀ (a / 4)
  let ε := min e (a / (‖J‖ + 1))
  have hdpos : 0 < d := lt_min hd₀ (by positivity)
  have hε : 0 < ε := lt_min he (by positivity)
  refine ⟨d, hdpos, (min_le_left _ _).trans hd₀r, ε, hε, C, hC, ?_⟩
  intro δ hδ
  obtain ⟨s, hs, hsδ, _, hmatch⟩ := hsection δ ⟨hδ.1, hδ.2.trans_le (min_le_left _ _)⟩
  refine ⟨s, hs, hsδ, ?_⟩
  intro Z hZ hfour harea
  let v := J (Z - littleCircularReference hγ hγ1)
  let ξ := Q v
  dsimp only
  intro hξδ
  have hξ : Q ξ = ξ := circularConstrainedUnstableProjectionCLM_idempotent hγ hγ1.le v
  have hξr : ‖ξ‖ ≤ r / 2 := by
    rw [hξδ]
    exact hδ.2.le.trans ((min_le_left _ _).trans hd₀r)
  obtain ⟨b, _, htarget⟩ := hmatch ξ hξ hξδ
  refine ⟨b, htarget, ?_⟩
  have hZe : Z ∈ ball (littleCircularReference hγ hγ1) e :=
    ball_subset_ball (min_le_left _ _) hZ
  have hvchart : circularConstrainedChart hγ hγ1 v = Z := hchart Z hZe hfour harea
  have hZv : ‖Z - littleCircularReference hγ hγ1‖ < a / (‖J‖ + 1) :=
    (mem_ball_iff_norm.mp hZ).trans_le (min_le_right _ _)
  have hv : ‖v‖ < a := by
    have hmul := (lt_div_iff₀ (show 0 < ‖J‖ + 1 by positivity)).mp hZv
    have hop : ‖v‖ ≤ ‖J‖ * ‖Z - littleCircularReference hγ hγ1‖ := J.le_opNorm _
    nlinarith only [hop, hmul, norm_nonneg (Z - littleCircularReference hγ hγ1)]
  have hx : ‖x ξ 0‖ < a := by
    have hnorm : ‖x ξ 0‖ ≤ 2 * ‖ξ‖ := by
      simpa only [pow_zero, mul_one] using hg.norm_le ξ hξ hξr 0
    have hδa : δ < a / 4 := hδ.2.trans_le (min_le_right _ _)
    rw [hξδ] at hnorm
    linarith only [hnorm, hδa, ha]
  calc
    ‖Z - contourRotationFamilyLittleCLM γ b (circularCoRotationCLM γ s (P.ancient s))‖ =
        ‖circularConstrainedChart hγ hγ1 v - circularConstrainedChart hγ hγ1 (x ξ 0)‖ := by
      rw [hvchart, htarget]
    _ ≤ C * ‖v - x ξ 0‖ := hLip v (x ξ 0) hv hx

end CircularMaterialTransferProfile
end Euler2D

end
