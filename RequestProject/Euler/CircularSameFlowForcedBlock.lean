module

public import RequestProject.Euler.CircularSameFlowMaterialBlock
public import RequestProject.Euler.CircularForcedIntervalComparison
public import RequestProject.Euler.CircularForcedReturnCoordinateError
public import RequestProject.Euler.UniformForcedPeriodSmallness

/-! Full-block forced solutions are compared to the fixed iterate of
the same original circular return map. Actual whole-interval existence
and the original material-block identification are both retained. -/

@[expose] public section

set_option maxHeartbeats 24000000
set_option maxRecDepth 4000

noncomputable section

open Set Filter Topology Metric
open scoped NNReal ContDiff

namespace Euler2D

local instance (priority := 2000) sameForcedBlockLittle_group (γ : ℝ≥0) :
    NormedAddCommGroup (LittleContourSpace γ) := Submodule.normedAddCommGroup (LittleContourSpace γ)
local instance (priority := 2000) sameForcedBlockLittle_space (γ : ℝ≥0) :
    NormedSpace ℝ (LittleContourSpace γ) := Submodule.normedSpace (LittleContourSpace γ)
local instance (priority := 2000) sameForcedBlockFamily_tower (γ : ℝ≥0) :
    IsScalarTower ℝ ℝ (Fin 2 → LittleContourSpace γ) where
  smul_assoc a b Z := by
    funext i
    change (a * b) • Z i = a • (b • Z i)
    exact (smul_smul a b (Z i)).symm
local instance (priority := 2000) sameForcedBlockTangent_group (γ : ℝ≥0) :
    NormedAddCommGroup (CircularConstrainedTangentSpace γ) :=
      Submodule.normedAddCommGroup (circularConstrainedTangentSubmodule γ)
local instance (priority := 2000) sameForcedBlockTangent_space (γ : ℝ≥0) :
    NormedSpace ℝ (CircularConstrainedTangentSpace γ) :=
      Submodule.normedSpace (circularConstrainedTangentSubmodule γ)
local instance (priority := 2000) sameForcedBlockTangent_continuousAdd (γ : ℝ≥0) :
    ContinuousAdd (CircularConstrainedTangentSpace γ) where
  continuous_add := by
    have h1 : Continuous (fun p : CircularConstrainedTangentSpace γ × CircularConstrainedTangentSpace γ =>
        p.1.val) := continuous_subtype_val.comp continuous_fst
    have h2 : Continuous (fun p : CircularConstrainedTangentSpace γ × CircularConstrainedTangentSpace γ =>
        p.2.val) := continuous_subtype_val.comp continuous_snd
    exact (h1.add h2).subtype_mk _

attribute [local irreducible] circularConstrainedTangentSubmodule
  circularConstrainedReturnMap circularConstrainedChart circularConstraintProjectionToTangentCLM

theorem exists_circular_sameFlow_forced_block_comparison {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1) {R : ℝ} (hR : 0 < R)
    {X : (Fin 2 → LittleContourSpace γ) → ℝ → Fin 2 → LittleContourSpace γ}
    (hX : IsBanachFlowOn (circularBanachField hγ hγ1) (circularBanachDomain hγ hγ1)
      (ball (littleCircularReference hγ hγ1) R) period X)
    (hd : ContDiffAt ℝ 2 (fun W => X W period) (littleCircularReference hγ hγ1))
    (hfix : X (littleCircularReference hγ hγ1) period = littleCircularReference hγ hγ1)
    (harea : ∀ W ∈ ball (littleCircularReference hγ hγ1) R, ∀ i,
      littleContourArea γ (X W period i) = littleContourArea γ (W i))
    {m : ℕ} (hm : 0 < m) :
    ∃ L > 0, ∃ K : ℝ≥0, ∃ δ > 0, ∃ ζ > 0, ∃ η > 0,
      ∀ J : ℝ≥0, (J : ℝ) ≤ 1 → ∀ ε ∈ Icc (0 : ℝ) η,
      ∀ q : ℝ → (Fin 2 → LittleContourSpace γ) → Fin 2 → LittleContourSpace γ,
      (∀ t ∈ Icc (0 : ℝ) ((m : ℝ) * period), LipschitzOnWith J (q t) (ball 0 L)) →
      (∀ W ∈ ball (0 : Fin 2 → LittleContourSpace γ) L,
        ContinuousOn (fun t => q t W) (Icc (0 : ℝ) ((m : ℝ) * period))) →
      (∀ t ∈ Icc (0 : ℝ) ((m : ℝ) * period),
        ∀ W ∈ ball (0 : Fin 2 → LittleContourSpace γ) L, ‖q t W‖ ≤ ε) →
      ∃ Y : (Fin 2 → LittleContourSpace γ) → ℝ → Fin 2 → LittleContourSpace γ,
        IsNonautonomousBanachFlowOn (fun t W => circularBanachField hγ hγ1 W + q t W)
          (circularBanachDomain hγ hγ1) (ball (littleCircularReference hγ hγ1) δ)
          ((m : ℝ) * period) Y ∧
        (∀ W ∈ ball (littleCircularReference hγ hγ1) δ,
          ∀ t ∈ Icc (0 : ℝ) ((m : ℝ) * period), ∀ i θ,
          HasDerivAt (fun s => LittleContourSpace.lift γ (Y W s i) θ)
            (contourBoundaryField circularContourStrengths
              (fun j => LittleContourSpace.lift γ (Y W t j)) i θ +
              LittleContourSpace.lift γ (q t (Y W t) i) θ) t) ∧
        ∀ v ∈ ball (0 : CircularConstrainedTangentSpace γ) ζ,
          ‖circularConstrainedReturnMap hγ hγ1 (fun W => Y W ((m : ℝ) * period)) v -
              (circularConstrainedReturnMap hγ hγ1 (fun W => X W period))^[m] v‖ ≤
            ‖circularConstraintProjectionToTangentCLM hγ hγ1.le‖ *
              (ε * ((m : ℝ) * period) * Real.exp ((K : ℝ) * ((m : ℝ) * period))) := by
  have hT : 0 < (m : ℝ) * period := mul_pos (Nat.cast_pos.mpr hm) (by unfold period; positivity)
  obtain ⟨ρ, hρ, Z, hZ, hconj⟩ :=
    exists_circular_sameFlow_material_block_return hγ hγ1 hR hX hd hfix harea hm
  obtain ⟨L, hL, K, r, hr, hperiod⟩ := exists_circular_forced_interval_comparison_constants hγ hγ1 hT
  obtain ⟨δ₀, hδ₀, η, hη, hsmall₀, hsmall⟩ := exists_uniform_forced_flow_smallness hr hT K
  let δ : ℝ := min ρ δ₀
  have hδ : 0 < δ := lt_min hρ hδ₀
  have hinput : ∀ᶠ v : CircularConstrainedTangentSpace γ in 𝓝 0,
      circularConstrainedChart hγ hγ1 v ∈ ball (littleCircularReference hγ hγ1) δ :=
    (hasFDerivAt_circularConstrainedChart_zero hγ hγ1).continuousAt
      (by rw [circularConstrainedChart_zero]; exact ball_mem_nhds _ hδ)
  obtain ⟨ζ, hζ, hζprop⟩ := Metric.eventually_nhds_iff.mp (hinput.and hconj)
  refine ⟨L, hL, K, δ, hδ, ζ, hζ, η, hη, ?_⟩
  intro J hJ ε hε q hqLip hqc hqbound
  obtain ⟨Y, hY, _, hYd, hcompare⟩ :=
    hperiod J hδ₀ hε.1 hsmall₀ (hsmall J hJ ε hε) q hqLip hqc hqbound
  have hsubset : ball (littleCircularReference hγ hγ1) δ ⊆
      ball (littleCircularReference hγ hγ1) δ₀ := ball_subset_ball (min_le_right _ _)
  refine ⟨Y, ⟨fun W hW => hY.initial W (hsubset hW), fun W hW => hY.continuous W (hsubset hW),
    fun W hW => hY.hasDerivAt W (hsubset hW), fun W hW => hY.mem W (hsubset hW)⟩,
    fun W hW => hYd W (hsubset hW), ?_⟩
  intro v hv
  have he := circularConstrainedReturnMap_difference_le hγ hγ1
    (fun W => Z W ((m : ℝ) * period)) (fun W => Y W ((m : ℝ) * period)) v
  have hh := hcompare hZ (circularConstrainedChart hγ hγ1 v) (hζprop hv).1
    ((m : ℝ) * period) ⟨hT.le, le_rfl⟩
  have hout := he.trans (mul_le_mul_of_nonneg_left hh
    (norm_nonneg (circularConstraintProjectionToTangentCLM hγ hγ1.le)))
  simpa only [(hζprop hv).2] using hout

end Euler2D

end
