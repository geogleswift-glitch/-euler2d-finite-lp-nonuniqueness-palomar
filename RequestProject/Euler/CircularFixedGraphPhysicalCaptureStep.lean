module

public import RequestProject.Euler.CircularFixedGraphForcedCaptureBlockBounds
public import RequestProject.Euler.CircularPhysicalExistingBlockComparison

/-! A fixed block of an existing physical trajectory gives the two
capture estimates in the same old ancient graph coordinates. The
block and all analytic constants precede the physical parameters. -/

@[expose] public section

set_option maxHeartbeats 24000000
set_option maxRecDepth 4000

noncomputable section

open Complex Set Filter Topology Metric
open scoped NNReal ContDiff

namespace Euler2D

attribute [local instance 2000] captureBlockLittle_group captureBlockLittle_space
  captureBlockFamily_tower captureBlockTangent_group captureBlockTangent_space
  captureBlockTangent_continuousAdd captureBlockEndo_monoid captureBlockTangent_complete
  rigidGaugeFamily_tower
attribute [local instance] LittleContourSpace.complexScalarNormedSpace LittleContourSpace.complexScalarTower

attribute [local irreducible] circularConstrainedTangentSubmodule circularConstrainedUnstableProjectionCLM
  circularConstrainedReturnMap circularConstrainedUnstableEmbeddingCLM circularConstrainedUnstableCoordinateCLM
  circularConstrainedChart circularConstraintProjectionToTangentCLM
  circularBanachField circularBanachDomain

theorem exists_circularFixedGraph_physical_capture_step {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1) {R r₀ : ℝ} (hR : 0 < R) (hr₀ : 0 < r₀)
    {X : (Fin 2 → LittleContourSpace γ) → ℝ → Fin 2 → LittleContourSpace γ}
    (hX : IsBanachFlowOn (circularBanachField hγ hγ1) (circularBanachDomain hγ hγ1)
      (ball (littleCircularReference hγ hγ1) R) period X)
    (hd : ContDiffAt ℝ 2 (fun W => X W period) (littleCircularReference hγ hγ1))
    (hfix : X (littleCircularReference hγ hγ1) period = littleCircularReference hγ hγ1)
    (harea : ∀ W ∈ ball (littleCircularReference hγ hγ1) R, ∀ i,
      littleContourArea γ (X W period i) = littleContourArea γ (W i))
    {x : CircularConstrainedTangentSpace γ → ℕ → CircularConstrainedTangentSpace γ}
    (hg : IsLocalWeightedBackwardGraph
      (banachDoubleReturn (circularConstrainedReturnMap hγ hγ1 (fun W => X W period)))
      (circularConstrainedUnstableProjectionCLM hγ hγ1.le) circularAncientBackwardWeight r₀ x) :
    ∃ k : ℕ, 0 < k ∧ ∃ q : ℝ, 1 < q ∧ q ^ 2 < (lamMult ^ 2) ^ k ∧
      let F := circularConstrainedReturnMap hγ hγ1 (fun W => X W period)
      let P := circularConstrainedUnstableProjectionCLM hγ hγ1.le
      let L := ((fderiv ℝ F 0) ^ 2) ^ k
      let g := fun v => x v 0 - v
      let T := ((2 * k : ℕ) : ℝ) * period
      (∀ w, P w = 0 → ‖L w‖ ≤ q * ‖w‖) ∧
      ∃ C > 0, ∃ d > 0, d ≤ r₀ / 2 ∧ ∃ E > 0, ∃ ε₀ > 0,
      ∃ U : Set (Fin 2 → LittleContourSpace γ), IsOpen U ∧ U ⊆ circularBanachDomain hγ hγ1 ∧
        ∀ α w, P α = α → P w = 0 → ‖α‖ + ‖w‖ ≤ d →
        ∀ {A r ε : ℝ}, 0 < A → 0 < r → ε ∈ Icc (0 : ℝ) ε₀ →
        ∀ e Ω : ℝ, ∀ z p : ℝ → Fin 2 → LittleContourSpace γ,
          r⁻¹ • z e = circularConstrainedChart hγ hγ1 (α + g α + w) →
          (∀ τ ∈ Icc (0 : ℝ) T,
            normalizedPhysicalCurve A r e z τ ∈ circularBanachDomain hγ hγ1) →
          (∀ τ ∈ Icc (0 : ℝ) T,
            HasDerivAt z ((A * r) • circularBanachField hγ hγ1
              (r⁻¹ • z (physicalTimeFromNormalized A e τ)) +
              ((Ω : ℂ) * I) • z (physicalTimeFromNormalized A e τ) +
              p (physicalTimeFromNormalized A e τ)) (physicalTimeFromNormalized A e τ)) →
          (∀ τ ∈ Icc (0 : ℝ) T,
            rigidRotationGauge (Ω / A) 0 τ • normalizedPhysicalCurve A r e z τ ∈ U) →
          (∀ τ ∈ Icc (0 : ℝ) T, ‖p (physicalTimeFromNormalized A e τ)‖ / (A * r) ≤ ε) →
          let v := circularConstraintProjectionToTangentCLM hγ hγ1.le
            ((rigidRotationGauge (Ω / A) 0 T • normalizedPhysicalCurve A r e z T) -
              littleCircularReference hγ hγ1)
          ‖P v - (lamMult ^ 2) ^ k • α‖ ≤ C * (‖α‖ + ‖w‖) ^ 2 + E * ε ∧
          ‖(v - P v) - g (P v) - L w‖ ≤ C * (‖α‖ + ‖w‖) * ‖w‖ + E * ε := by
  obtain ⟨k, hk, q, hq, hgap, hcomp, C, hC, d₀, hd₀, hdr, η₀, hη₀, B, hB, hflat⟩ :=
    exists_circularFixedGraph_forced_capture_block_bounds (γ := γ) (R := R) (r := r₀)
      (X := X) (x := x) hγ hγ1 hR hr₀ hX hd hfix harea hg
  let F := circularConstrainedReturnMap hγ hγ1 (fun W => X W period)
  let P := circularConstrainedUnstableProjectionCLM hγ hγ1.le
  let g := fun v => x v 0 - v
  let T : ℝ := ((2 * k : ℕ) : ℝ) * period
  have hT : 0 < T := mul_pos (Nat.cast_pos.mpr (by omega)) (by unfold period; positivity)
  obtain ⟨U, hU, hUD, _, K, ζ, hζ, hcompare⟩ :=
    exists_circular_sameFlow_physical_existing_block_comparison (γ := γ) (R := R) (X := X)
      hγ hγ1 hR hX hd hfix harea
      (m := 2 * k) (by omega)
  let d : ℝ := min d₀ (ζ / 4)
  have hdpos : 0 < d := lt_min hd₀ (by positivity)
  let Cf : ℝ := ‖circularConstraintProjectionToTangentCLM hγ hγ1.le‖ *
    (T * Real.exp ((K : ℝ) * T))
  have hCf : 0 ≤ Cf := mul_nonneg (norm_nonneg _) (mul_nonneg hT.le (Real.exp_pos _).le)
  let E : ℝ := ‖P‖ * Cf + B * Cf + 1
  have hPCf : 0 ≤ ‖P‖ * Cf := mul_nonneg (norm_nonneg _) hCf
  have hBCf : 0 ≤ B * Cf := mul_nonneg hB.le hCf
  have hE : 0 < E := by dsimp only [E]; linarith
  let ε₀ : ℝ := η₀ / (Cf + 1)
  have hε₀ : 0 < ε₀ := div_pos hη₀ (by linarith)
  refine ⟨k, hk, q, hq, hgap, hcomp, C, hC, d, hdpos,
    (min_le_left _ _).trans hdr, E, hE, ε₀, hε₀, U, hU, hUD, ?_⟩
  intro α w hα hw hsize A r ε hA hr hε e Ω z p hinit hmem hzd hym hbudget
  have hαr : ‖α‖ ≤ r₀ / 2 :=
    (le_add_of_nonneg_right (norm_nonneg w)).trans (hsize.trans ((min_le_left _ _).trans hdr))
  have hxin := hg.norm_le α hα hαr 0
  simp only [pow_zero, mul_one] at hxin
  have hzin : α + g α + w ∈ ball (0 : CircularConstrainedTangentSpace γ) ζ := by
    apply mem_ball_zero_iff.mpr
    have hz : α + g α + w = x α 0 + w := by dsimp only [g]; abel
    rw [hz]
    have hsd : ‖α‖ + ‖w‖ ≤ ζ / 4 := hsize.trans (min_le_right _ _)
    have hn := (norm_add_le (x α 0) w).trans (add_le_add hxin le_rfl)
    linarith [norm_nonneg w]
  have herror := hcompare hA hr hε.1 e Ω (α + g α + w) hzin z p
    hinit hmem hzd hym hbudget
  have herror' : ‖circularConstraintProjectionToTangentCLM hγ hγ1.le
      ((rigidRotationGauge (Ω / A) 0 T • normalizedPhysicalCurve A r e z T) -
        littleCircularReference hγ hγ1) - F^[2 * k] (α + g α + w)‖ ≤ Cf * ε := by
    exact herror.trans_eq (by dsimp only [Cf]; ring)
  have hηcap : Cf * ε ≤ η₀ := by
    have hh := (le_div_iff₀ (by linarith : 0 < Cf + 1)).mp hε.2
    nlinarith [hε.1]
  let v := circularConstraintProjectionToTangentCLM hγ hγ1.le
    ((rigidRotationGauge (Ω / A) 0 T • normalizedPhysicalCurve A r e z T) -
      littleCircularReference hγ hγ1)
  have hb := hflat α w hα hw (hsize.trans (min_le_left _ _)) v
    (mul_nonneg hCf hε.1) hηcap herror'
  have hE1 : ‖P‖ * (Cf * ε) ≤ E * ε := by
    have hh : ‖P‖ * Cf ≤ E := by dsimp only [E]; linarith
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hh hε.1
  have hE2 : B * (Cf * ε) ≤ E * ε := by
    have hh : B * Cf ≤ E := by dsimp only [E]; linarith
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hh hε.1
  exact ⟨hb.1.trans (add_le_add le_rfl hE1), hb.2.trans (add_le_add le_rfl hE2)⟩

end Euler2D

end
