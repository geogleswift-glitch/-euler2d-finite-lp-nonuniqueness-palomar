module

public import RequestProject.Euler.CircularAncientGraphFlowCell
public import RequestProject.Euler.CircularMaterialTransferProfile

/-! Every sufficiently negative cell of the same canonical ancient
curve lies on its already fixed backward graph in the original global
co-parameter frame. The true extended flow is constructed internally. -/

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

theorem circularCoRotationCLM_nat_double_period (γ : ℝ≥0) (n : ℕ) (Z : Fin 2 → LittleContourSpace γ) :
    circularCoRotationCLM γ ((n : ℝ) * (period + period)) Z = Z := by
  have hL (W : Fin 2 → LittleContourSpace γ) : circularCoRotationCLM γ (period + period) W = W := by
    rw [← circularCoRotationCLM_add, circularCoRotationCLM_period, circularCoRotationCLM_period]
  induction n with
  | zero => simpa only [Nat.cast_zero, zero_mul] using circularCoRotationCLM_zero γ Z
  | succ n ih =>
    rw [show ((n + 1 : ℕ) : ℝ) * (period + period) =
      (n : ℝ) * (period + period) + (period + period) by push_cast; ring]
    rw [← circularCoRotationCLM_add, hL]
    exact ih

theorem circularCoRotationCLM_negative_double_grid (γ : ℝ≥0) (n : ℕ) (Z : Fin 2 → LittleContourSpace γ) :
    circularCoRotationCLM γ (-(n : ℝ) * (period + period)) Z = Z := by
  have h := circularCoRotationCLM_add γ (-((n : ℝ) * (period + period)))
    ((n : ℝ) * (period + period)) Z
  rw [neg_add_cancel, circularCoRotationCLM_zero, circularCoRotationCLM_nat_double_period] at h
  simpa only [neg_mul] using h

attribute [local irreducible] circularBanachField circularBanachDomain circularCoRotationCLM
  littleCircularReference circularConstrainedTangentSubmodule circularConstrainedChart
  circularConstraintProjectionToTangentCLM circularConstrainedReturnMap circularConstrainedUnstableProjectionCLM
  circularCoRotatedConstrainedMap contourC1GraphSubmodule holderGraphSubmodule

namespace CircularMaterialTransferProfile

variable {γ : ℝ≥0} {hγ : 0 < γ} {hγ1 : (γ : ℝ) < 1} (P : CircularMaterialTransferProfile hγ hγ1)

theorem eventually_ancient_cells_on_same_graph {R r : ℝ} (hR : 0 < R) (hr : 0 < r)
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
    ∀ ε > 0, ∀ᶠ n : ℕ in atTop, ∀ u ∈ Icc (0 : ℝ) (period + period),
      ∃ α : CircularConstrainedTangentSpace γ,
        circularConstrainedUnstableProjectionCLM hγ hγ1.le α = α ∧ ‖α‖ ≤ r / 2 ∧ ‖α‖ < ε ∧
        circularConstrainedChart hγ hγ1 (x α 0) =
          circularCoRotationCLM γ (-(n : ℝ) * (period + period) + u)
            (P.ancient (-(n : ℝ) * (period + period) + u)) := by
  let L := period + period
  let c := littleCircularReference hγ hγ1
  let Q := circularConstrainedUnstableProjectionCLM hγ hγ1.le
  let J := circularConstraintProjectionToTangentCLM hγ hγ1.le
  let B := Q.comp J
  have hp : 0 < period := by unfold period; positivity
  have hL : 0 < L := add_pos hp hp
  obtain ⟨S, hS, Y, hY, hsY, heY, hmY, hareaY, hfourY⟩ :=
    exists_circularContour_constrained_interval_flow hγ hγ1 1 (add_pos hL hp)
  have hw : 1 ≤ circularAncientBackwardWeight := by linarith [circularAncientBackwardWeight_bounds.1]
  obtain ⟨η, hη, hηr, C, hC, hcell⟩ := exists_same_circularBackwardGraph_actual_cell_radius
    hγ hγ1 hL hR hS hr hw hX hd hfix hareaX hY hareaY hg
  have hzero : Tendsto (fun n : ℕ => P.ancient (-(n : ℝ) * L) - c) atTop (𝓝 0) := by
    simpa only [L, c, sub_self] using P.ancient_samples_tendsto.sub_const c
  have hlim : Tendsto (fun n : ℕ => B (P.ancient (-(n : ℝ) * L) - c)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, map_zero] using (B.continuous.tendsto 0).comp hzero
  intro ε hε
  let δ := min η (ε / (C + 1))
  have hδ : 0 < δ := lt_min hη (div_pos hε (by positivity))
  have hsmall : ∀ᶠ n : ℕ in atTop, ‖B (P.ancient (-(n : ℝ) * L) - c)‖ < δ :=
    hlim.norm.eventually (eventually_lt_nhds (by simpa only [norm_zero] using hδ))
  obtain ⟨Ns, hNs⟩ := eventually_atTop.mp hsmall
  obtain ⟨Ng, hNg⟩ := hsamples
  filter_upwards [eventually_ge_atTop (max 1 (max Ng Ns))] with n hn
  intro u hu
  have hn1 : 1 ≤ n := (le_max_left _ _).trans hn
  have hng : Ng ≤ n := (le_max_left _ _).trans ((le_max_right _ _).trans hn)
  have hns : Ns ≤ n := (le_max_right _ _).trans ((le_max_right _ _).trans hn)
  obtain ⟨ξ, hξ, hξr, hsample⟩ := hNg n hng
  have hbase : B (P.ancient (-(n : ℝ) * L) - c) = ξ := by
    change Q (J (P.ancient (-(n : ℝ) * L) - c)) = ξ
    rw [hsample, circularConstrainedChart_projection_left_inverse]
    exact hg.coordinate ξ hξ hξr
  have hξδ : ‖ξ‖ < δ := by
    have hh := hNs n hns
    rwa [hbase] at hh
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
  have ha : -(n : ℝ) * L + L ≤ 0 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hnR) hL.le]
  obtain ⟨α, hα, hαr, hbound, hchart⟩ := hcell P.ancient P.ancient_continuous
    (fun t ht => (P.ancient_domain t ht).1) P.ancient_derivative (-(n : ℝ) * L) ha ξ hξ
    (hξδ.le.trans (min_le_left _ _)) hsample u hu
  have hαε : ‖α‖ < ε := by
    have hh : ‖ξ‖ < ε / (C + 1) := hξδ.trans_le (min_le_right _ _)
    have hh' := (lt_div_iff₀ (by positivity : 0 < C + 1)).mp hh
    nlinarith [norm_nonneg ξ]
  have hframe : circularCoRotationCLM γ (-(n : ℝ) * L + u)
      (P.ancient (-(n : ℝ) * L + u)) =
      circularCoRotationCLM γ u (P.ancient (-(n : ℝ) * L + u)) := by
    rw [← circularCoRotationCLM_add, circularCoRotationCLM_negative_double_grid]
  exact ⟨α, hα, hαr, hαε, hchart.trans hframe.symm⟩

end CircularMaterialTransferProfile
end Euler2D

end
