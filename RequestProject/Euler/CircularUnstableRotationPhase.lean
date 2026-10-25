module

public import RequestProject.Euler.CircularUnstableRotationCovariance
public import Mathlib.Analysis.SpecialFunctions.Complex.Arg

/-! Exact phase alignment on the original two-real-dimensional
growing plane, and on the same already fixed local backward graph. -/

@[expose] public section

set_option maxHeartbeats 8000000
set_option maxRecDepth 6000

noncomputable section

open Complex Set Filter Topology Metric
open scoped NNReal ContDiff ComplexConjugate

namespace Euler2D

attribute [local instance 2000] constrainedRotationLittle_group constrainedRotationLittle_space
  constrainedRotationFamily_tower constrainedRotationTangent_group constrainedRotationTangent_space

theorem exists_fourth_character_mul_eq_of_norm_eq {c d : ℂ} (h : ‖c‖ = ‖d‖) :
    ∃ b : ℝ, contourCircleCharacter (-4) b * c = d := by
  by_cases hc : c = 0
  · have hd : d = 0 := norm_eq_zero.mp (by simpa only [hc, norm_zero] using h.symm)
    exact ⟨0, by simp only [hc, hd, mul_zero]⟩
  · let q := d / c
    have hq : ‖q‖ = 1 := by
      dsimp only [q]
      rw [norm_div, ← h, div_self (norm_ne_zero_iff.mpr hc)]
    have he : exp ((q.arg : ℂ) * I) = q := by
      have hh := norm_mul_exp_arg_mul_I q
      rw [hq, ofReal_one, one_mul] at hh
      exact hh
    refine ⟨-q.arg / 4, ?_⟩
    have hb : contourCircleCharacter (-4) (-q.arg / 4) = q := by
      unfold contourCircleCharacter
      have hh : ((-4 : ℤ) : ℂ) * ((-q.arg / 4 : ℝ) : ℂ) * I = (q.arg : ℂ) * I := by
        push_cast
        ring
      rw [hh]
      exact he
    rw [hb]
    exact div_mul_cancel₀ d hc

theorem norm_circularConstrainedUnstableEmbeddingCLM {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : γ ≤ 1) (c : ℂ) :
    ‖circularConstrainedUnstableEmbeddingCLM hγ hγ1 c‖ =
      ‖c‖ * ‖circularConstrainedUnstableEmbeddingCLM hγ hγ1 1‖ := by
  obtain ⟨b, hb⟩ := exists_fourth_character_mul_eq_of_norm_eq
    (c := (‖c‖ : ℂ)) (d := c) (by
      simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg c)])
  have he : circularConstrainedUnstableEmbeddingCLM hγ hγ1 c =
      circularConstrainedRotationCLM γ b (circularConstrainedUnstableEmbeddingCLM hγ hγ1 (‖c‖ : ℂ)) := by
    rw [circularConstrainedUnstableEmbeddingCLM_rotation, hb]
  have hs : circularConstrainedUnstableEmbeddingCLM hγ hγ1 (‖c‖ : ℂ) =
      ‖c‖ • circularConstrainedUnstableEmbeddingCLM hγ hγ1 1 := by
    rw [← map_smul]
    congr 1
    simp only [Complex.real_smul, mul_one]
  rw [he, norm_circularConstrainedRotationCLM, hs, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (norm_nonneg c)]

theorem norm_circularConstrainedUnstableEmbedding_one_pos {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : γ ≤ 1) :
    0 < ‖circularConstrainedUnstableEmbeddingCLM hγ hγ1 1‖ := by
  apply norm_pos_iff.mpr
  intro h
  have he := circularConstrainedUnstableCoordinate_embedding hγ hγ1 (1 : ℂ)
  rw [h, ContinuousLinearMap.map_zero (circularConstrainedUnstableCoordinateCLM γ)] at he
  exact zero_ne_one he

theorem exists_circularConstrainedUnstable_rotation_of_norm_eq {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : γ ≤ 1) {ξ ζ : CircularConstrainedTangentSpace γ}
    (hξ : circularConstrainedUnstableProjectionCLM hγ hγ1 ξ = ξ)
    (hζ : circularConstrainedUnstableProjectionCLM hγ hγ1 ζ = ζ) (hn : ‖ξ‖ = ‖ζ‖) :
    ∃ b : ℝ, circularConstrainedRotationCLM γ b ξ = ζ := by
  let a := circularConstrainedUnstableCoordinateCLM γ ξ
  let d := circularConstrainedUnstableCoordinateCLM γ ζ
  have ha : circularConstrainedUnstableEmbeddingCLM hγ hγ1 a = ξ := hξ
  have hd : circularConstrainedUnstableEmbeddingCLM hγ hγ1 d = ζ := hζ
  have hn' : ‖a‖ = ‖d‖ := by
    have he : ‖a‖ * ‖circularConstrainedUnstableEmbeddingCLM hγ hγ1 1‖ =
        ‖d‖ * ‖circularConstrainedUnstableEmbeddingCLM hγ hγ1 1‖ := by
      rw [← norm_circularConstrainedUnstableEmbeddingCLM hγ hγ1 a,
        ← norm_circularConstrainedUnstableEmbeddingCLM hγ hγ1 d, ha, hd]
      exact hn
    exact mul_right_cancel₀ (norm_circularConstrainedUnstableEmbedding_one_pos hγ hγ1).ne' he
  obtain ⟨b, hb⟩ := exists_fourth_character_mul_eq_of_norm_eq hn'
  refine ⟨b, ?_⟩
  rw [← ha, circularConstrainedUnstableEmbeddingCLM_rotation, hb, hd]

attribute [local irreducible] circularConstrainedTangentSubmodule circularConstrainedUnstableProjectionCLM
  circularConstrainedReturnMap circularConstrainedChart circularConstraintProjectionToTangentCLM
  circularConstrainedRotationCLM circularConstrainedUnstableEmbeddingCLM circularConstrainedUnstableCoordinateCLM
  circularBanachField circularBanachDomain littleCircularReference contourC1GraphSubmodule holderGraphSubmodule

theorem exists_same_circularBackwardGraph_phase_alignment_radius {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1) {R : ℝ} (hR : 0 < R)
    {X : (Fin 2 → LittleContourSpace γ) → ℝ → Fin 2 → LittleContourSpace γ}
    (hX : IsBanachFlowOn (circularBanachField hγ hγ1) (circularBanachDomain hγ hγ1)
      (ball (littleCircularReference hγ hγ1) R) period X)
    (hd : DifferentiableAt ℝ (fun W => X W period) (littleCircularReference hγ hγ1))
    (hfix : X (littleCircularReference hγ hγ1) period = littleCircularReference hγ hγ1)
    {w r : ℝ} (hw : 1 ≤ w) (hr : 0 < r)
    {x : CircularConstrainedTangentSpace γ → ℕ → CircularConstrainedTangentSpace γ}
    (hg : IsLocalWeightedBackwardGraph
      (banachDoubleReturn (circularConstrainedReturnMap hγ hγ1 (fun W => X W period)))
      (circularConstrainedUnstableProjectionCLM hγ hγ1.le) w r x) :
    ∃ η > 0, η ≤ r / 2 ∧ ∀ ξ ζ : CircularConstrainedTangentSpace γ,
      circularConstrainedUnstableProjectionCLM hγ hγ1.le ξ = ξ →
      circularConstrainedUnstableProjectionCLM hγ hγ1.le ζ = ζ →
      ‖ξ‖ ≤ η → ‖ξ‖ = ‖ζ‖ → ∃ b : ℝ,
        x ζ = (fun n => circularConstrainedRotationCLM γ b (x ξ n)) := by
  obtain ⟨η, hη, hηr, hinv⟩ := exists_same_circularBackwardGraph_exact_rotation_radius
    hγ hγ1 hR hX hd hfix hw hr hg
  refine ⟨η, hη, hηr, ?_⟩
  intro ξ ζ hξ hζ hξη hn
  obtain ⟨b, hb⟩ := exists_circularConstrainedUnstable_rotation_of_norm_eq hγ hγ1.le hξ hζ hn
  have he := hinv b ξ hξ hξη
  rw [hb] at he
  exact ⟨b, he⟩

end Euler2D

end
