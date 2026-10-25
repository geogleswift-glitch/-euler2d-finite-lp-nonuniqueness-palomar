module

public import RequestProject.Euler.CircularSameFlowMaterialBlock
public import RequestProject.Euler.CircularExistingForcedIntervalComparison
public import RequestProject.Euler.CircularForcedReturnCoordinateError

/-! The endpoint of an already existing actual material trajectory is
compared to the fixed iterate of the same original return map. Only
the actual forcing values on this trajectory are bounded. -/

@[expose] public section

set_option maxHeartbeats 16000000
set_option maxRecDepth 4000

noncomputable section

open Set Filter Topology Metric
open scoped NNReal ContDiff

namespace Euler2D

attribute [local instance 2000] returnConjugacyLittle_group returnConjugacyLittle_space
  returnConjugacyFamily_tower returnConjugacyTangent_group returnConjugacyTangent_space
  returnConjugacyTangent_continuousAdd

attribute [local irreducible] circularConstrainedTangentSubmodule
  circularConstrainedReturnMap circularConstrainedChart circularConstraintProjectionToTangentCLM

theorem exists_circular_sameFlow_existing_block_comparison {γ : ℝ≥0}
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
        ∀ {ε : ℝ}, 0 ≤ ε →
        ∀ v ∈ ball (0 : CircularConstrainedTangentSpace γ) ζ,
        ∀ {y p : ℝ → Fin 2 → LittleContourSpace γ},
          y 0 = circularConstrainedChart hγ hγ1 v →
          ContinuousOn y (Icc (0 : ℝ) ((m : ℝ) * period)) →
          (∀ t ∈ Icc (0 : ℝ) ((m : ℝ) * period),
            HasDerivAt y (circularBanachField hγ hγ1 (y t) + p t) t) →
          (∀ t ∈ Icc (0 : ℝ) ((m : ℝ) * period), y t ∈ U) →
          (∀ t ∈ Icc (0 : ℝ) ((m : ℝ) * period), ‖p t‖ ≤ ε) →
          ‖circularConstraintProjectionToTangentCLM hγ hγ1.le
              (y ((m : ℝ) * period) - littleCircularReference hγ hγ1) -
              (circularConstrainedReturnMap hγ hγ1 (fun W => X W period))^[m] v‖ ≤
            ‖circularConstraintProjectionToTangentCLM hγ hγ1.le‖ *
              (ε * ((m : ℝ) * period) * Real.exp ((K : ℝ) * ((m : ℝ) * period))) := by
  have hT : 0 < (m : ℝ) * period :=
    mul_pos (Nat.cast_pos.mpr hm) (by unfold period; positivity)
  obtain ⟨ρ, hρ, Z, hZ, hconj⟩ :=
    exists_circular_sameFlow_material_block_return hγ hγ1 hR hX hd hfix harea hm
  obtain ⟨U, hU, hUD, hUref, K, r, hr, δ, hδ, htube, hcompare⟩ :=
    exists_circular_existing_forced_interval_constants hγ hγ1 hT
  have hinput : ∀ᶠ v : CircularConstrainedTangentSpace γ in 𝓝 0,
      circularConstrainedChart hγ hγ1 v ∈
        ball (littleCircularReference hγ hγ1) (min ρ δ) :=
    (hasFDerivAt_circularConstrainedChart_zero hγ hγ1).continuousAt
      (by rw [circularConstrainedChart_zero]; exact ball_mem_nhds _ (lt_min hρ hδ))
  obtain ⟨ζ, hζ, hζprop⟩ := Metric.eventually_nhds_iff.mp (hinput.and hconj)
  refine ⟨U, hU, hUD, hUref, K, ζ, hζ, ?_⟩
  intro ε hε v hv y p hy0 hyc hyd hym hp
  have hh := hcompare hZ hε (hζprop hv).1 hy0 hyc hyd hym hp
    ((m : ℝ) * period) ⟨hT.le, le_rfl⟩
  have he := circularConstrainedReturnMap_difference_le hγ hγ1
    (fun W => Z W ((m : ℝ) * period)) (fun _ => y ((m : ℝ) * period)) v
  have hout := he.trans (mul_le_mul_of_nonneg_left hh
    (norm_nonneg (circularConstraintProjectionToTangentCLM hγ hγ1.le)))
  rw [(hζprop hv).2] at hout
  simpa only [circularConstrainedReturnMap] using hout

end Euler2D

end
