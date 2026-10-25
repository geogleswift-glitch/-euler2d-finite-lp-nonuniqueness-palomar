module

public import RequestProject.Euler.CircularCaptureLinearBlock
public import RequestProject.Euler.CircularFixedGraphQuadraticBound
public import RequestProject.Euler.BanachFixedGraphBlockFlattening
public import RequestProject.Euler.BanachFixedGraphUniformInvarianceFlattening
public import RequestProject.Euler.BanachFixedPointIterates
public import RequestProject.Euler.CaptureBlockPowerGap
public import RequestProject.Euler.BanachCaptureLinearBlock

/-! A fixed even iterate of the same actual return map has the spectral
gap needed by capture in the original norm. The same old weighted graph
is genuinely invariant under this iterate. The block is chosen before
any physical scale, layer ratio, or truncation. -/

@[expose] public section

set_option maxHeartbeats 24000000
set_option maxRecDepth 4000


noncomputable section

open Set Filter Topology Metric
open scoped NNReal ContDiff

namespace Euler2D

attribute [local instance 2000] captureBlockLittle_group captureBlockLittle_space
  captureBlockFamily_tower captureBlockTangent_group captureBlockTangent_space
  captureBlockTangent_continuousAdd captureBlockEndo_monoid captureBlockTangent_complete

attribute [local irreducible] circularConstrainedTangentSubmodule circularConstrainedUnstableProjectionCLM
  circularConstrainedReturnMap circularConstrainedUnstableEmbeddingCLM circularConstrainedUnstableCoordinateCLM
  circularConstrainedChart circularConstraintProjectionToTangentCLM

theorem exists_circularFixedGraph_capture_block_bounds {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1) {R r : ℝ} (hR : 0 < R) (hr : 0 < r)
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
      (circularConstrainedUnstableProjectionCLM hγ hγ1.le) circularAncientBackwardWeight r x) :
    ∃ k : ℕ, 0 < k ∧ ∃ q : ℝ, 1 < q ∧ q ^ 2 < (lamMult ^ 2) ^ k ∧
      let F := circularConstrainedReturnMap hγ hγ1 (fun W => X W period)
      let P := circularConstrainedUnstableProjectionCLM hγ hγ1.le
      let T := F^[2 * k]
      let A := ((fderiv ℝ F 0) ^ 2) ^ k
      (∀ w, P w = 0 → ‖A w‖ ≤ q * ‖w‖) ∧
      (∀ v, A (P v) = (lamMult ^ 2) ^ k • P v) ∧
      ∃ C > 0, ∃ s > 0, s ≤ r / 2 ∧ ∀ α w, P α = α → P w = 0 → ‖α‖ + ‖w‖ ≤ s →
        let g := fun v => x v 0 - v
        let z := α + g α + w
        ‖P (T z) - A α‖ ≤ C * (‖α‖ + ‖w‖) ^ 2 ∧
        ‖(T z - P (T z)) - g (P (T z)) - A w‖ ≤ C * (‖α‖ + ‖w‖) * ‖w‖ := by
  let F := circularConstrainedReturnMap hγ hγ1 (fun W => X W period)
  let L := fderiv ℝ F 0
  let P := circularConstrainedUnstableProjectionCLM hγ hγ1.le
  have hblock := exists_circularConstrained_capture_linear_block (γ := γ) (R := R) (X := X)
    hγ hγ1 hR hX hd hfix harea
  obtain ⟨k, hk, q, hq, hgap, hT, hT0, hTA, hqbound, heigen, hinv⟩ :=
    hblock
  let T := F^[2 * k]
  let A := (L ^ 2) ^ k
  obtain ⟨d, hd₀, hdr, H, hH, hquad⟩ :=
    circularFixedBackwardGraph_quadratic_difference hγ hγ1 hR hr hX hd hfix harea hg
  have hw : 1 ≤ circularAncientBackwardWeight := by
    have hh := circularAncientBackwardWeight_bounds.1
    linarith
  have hfd : DifferentiableAt ℝ (fun W => X W period) (littleCircularReference hγ hγ1) :=
    hd.differentiableAt (by norm_num)
  have hcomm₂ : (L ^ 2).comp P = P.comp (L ^ 2) :=
    circularConstrainedDoubleDerivative_projection_commute hγ hγ1 hR hX hfd hfix harea
  have hc : Commute (L ^ 2) P := hcomm₂
  have hcomm : A.comp P = P.comp A := hc.pow_left k
  obtain ⟨C, hC, s, hs, hsd, hbounds⟩ :=
    exists_fixedGraph_flattening_of_uniform_invariance
      (E := CircularConstrainedTangentSpace γ) (F := banachDoubleReturn F)
      (P := P) (ρ := circularAncientBackwardWeight) (r := r) (x := x) (d := d) (H := H) hg hw hr
      (circularConstrainedUnstableProjectionCLM_idempotent hγ hγ1.le)
      T hT hT0 A hTA hcomm hd₀ hdr hH hquad hinv
  refine ⟨k, hk, q, hq, hgap, ?_⟩
  dsimp only
  exact ⟨hqbound, heigen, C, hC, s, hs, hsd.trans hdr, hbounds⟩

end Euler2D

end



