module

public import RequestProject.Euler.CircularFlattenedMaterialTransferProfile
public import RequestProject.Euler.CircularFixedGraphQuadraticBound

/-! The same ancient Y, original period X, fixed graph x, and transfer
Profile retain a locally Lipschitz flattening. This is the actual graph
needed to pass endpoint forcing errors to capture coordinates. -/

@[expose] public section

set_option maxHeartbeats 16000000
set_option maxRecDepth 4000

noncomputable section

open Set Filter Topology Metric
open scoped NNReal ContDiff

namespace Euler2D

local instance (priority := 2000) robustAncientLittle_group (γ : ℝ≥0) :
    NormedAddCommGroup (LittleContourSpace γ) := Submodule.normedAddCommGroup (LittleContourSpace γ)
local instance (priority := 2000) robustAncientLittle_space (γ : ℝ≥0) :
    NormedSpace ℝ (LittleContourSpace γ) := Submodule.normedSpace (LittleContourSpace γ)
local instance (priority := 2000) robustAncientFamily_tower (γ : ℝ≥0) :
    IsScalarTower ℝ ℝ (Fin 2 → LittleContourSpace γ) where
  smul_assoc a b Z := by
    funext i
    change (a * b) • Z i = a • (b • Z i)
    exact (smul_smul a b (Z i)).symm
local instance (priority := 2000) robustAncientTangent_group (γ : ℝ≥0) :
    NormedAddCommGroup (CircularConstrainedTangentSpace γ) :=
      Submodule.normedAddCommGroup (circularConstrainedTangentSubmodule γ)
local instance (priority := 2000) robustAncientTangent_space (γ : ℝ≥0) :
    NormedSpace ℝ (CircularConstrainedTangentSpace γ) :=
      Submodule.normedSpace (circularConstrainedTangentSubmodule γ)
local instance (priority := 2000) robustAncientTangent_continuousAdd (γ : ℝ≥0) :
    ContinuousAdd (CircularConstrainedTangentSpace γ) where
  continuous_add := by
    have h1 : Continuous (fun p : CircularConstrainedTangentSpace γ × CircularConstrainedTangentSpace γ =>
        p.1.val) := continuous_subtype_val.comp continuous_fst
    have h2 : Continuous (fun p : CircularConstrainedTangentSpace γ × CircularConstrainedTangentSpace γ =>
        p.2.val) := continuous_subtype_val.comp continuous_snd
    exact (h1.add h2).subtype_mk _

attribute [local irreducible] circularConstrainedTangentSubmodule circularConstrainedUnstableProjectionCLM
  circularConstrainedReturnMap circularConstrainedUnstableEmbeddingCLM circularConstrainedUnstableCoordinateCLM
  circularConstrainedChart circularConstraintProjectionToTangentCLM

def HasCircularRobustFlattenedAncientSamples {γ : ℝ≥0} (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1)
    (Y : ℝ → Fin 2 → LittleContourSpace γ) : Prop :=
  ∃ R > 0, ∃ X : (Fin 2 → LittleContourSpace γ) → ℝ → Fin 2 → LittleContourSpace γ,
    IsBanachFlowOn (circularBanachField hγ hγ1) (circularBanachDomain hγ hγ1)
      (ball (littleCircularReference hγ hγ1) R) period X ∧
    ContDiffAt ℝ 2 (fun W => X W period) (littleCircularReference hγ hγ1) ∧
    X (littleCircularReference hγ hγ1) period = littleCircularReference hγ hγ1 ∧
    (∀ W ∈ ball (littleCircularReference hγ hγ1) R, ∀ i,
      littleContourArea γ (X W period i) = littleContourArea γ (W i)) ∧
    ∃ r > 0, ∃ x : CircularConstrainedTangentSpace γ → ℕ → CircularConstrainedTangentSpace γ,
      IsLocalWeightedBackwardGraph
        (banachDoubleReturn (circularConstrainedReturnMap hγ hγ1 (fun W => X W period)))
        (circularConstrainedUnstableProjectionCLM hγ hγ1.le) circularAncientBackwardWeight r x ∧
      ∃ C > 0, ∃ s > 0, s ≤ r / 2 ∧
        (∀ α w, circularConstrainedUnstableProjectionCLM hγ hγ1.le α = α →
          circularConstrainedUnstableProjectionCLM hγ hγ1.le w = 0 → ‖α‖ + ‖w‖ ≤ s →
          let P := circularConstrainedUnstableProjectionCLM hγ hγ1.le
          let F := circularConstrainedReturnMap hγ hγ1 (fun W => X W period)
          let L := fderiv ℝ F 0
          let g := fun v => x v 0 - v
          let z := α + g α + w
          ‖P (F z) - (-lamMult : ℝ) • α‖ ≤ C * (‖α‖ + ‖w‖) ^ 2 ∧
          ‖(F z - P (F z)) - g (P (F z)) - L w‖ ≤ C * (‖α‖ + ‖w‖) * ‖w‖) ∧
        (∃ N : ℕ, ∀ n ≥ N, ∃ α : CircularConstrainedTangentSpace γ,
          circularConstrainedUnstableProjectionCLM hγ hγ1.le α = α ∧ ‖α‖ ≤ r / 2 ∧
          Y (-(n : ℝ) * (period + period)) = circularConstrainedChart hγ hγ1 (x α 0)) ∧
        ∃ d > 0, d ≤ r / 2 ∧ ∃ B > 0, ∀ u v,
          ‖circularConstrainedUnstableProjectionCLM hγ hγ1.le u‖ ≤ d →
          ‖circularConstrainedUnstableProjectionCLM hγ hγ1.le v‖ ≤ d →
          let P := circularConstrainedUnstableProjectionCLM hγ hγ1.le
          let g := fun α => x α 0 - α
          ‖(v - P v - g (P v)) - (u - P u - g (P u))‖ ≤ B * ‖v - u‖

theorem HasCircularFlattenedAncientSamples.robust {γ : ℝ≥0}
    {hγ : 0 < γ} {hγ1 : (γ : ℝ) < 1} {Y : ℝ → Fin 2 → LittleContourSpace γ}
    (h : HasCircularFlattenedAncientSamples hγ hγ1 Y) :
    HasCircularRobustFlattenedAncientSamples hγ hγ1 Y := by
  rcases h with ⟨R, hR, X, hX, hd, hfix, harea, r, hr, x, hg, C, hC, s, hs, hsr, hflat, hsample⟩
  obtain ⟨d, hd₀, hdr, B, hB, hLip⟩ :=
    circularFixedBackwardGraph_flattening_lipschitz hγ hγ1 hR hr hX hd hfix harea hg
  exact ⟨R, hR, X, hX, hd, hfix, harea, r, hr, x, hg, C, hC, s, hs, hsr, hflat,
    hsample, d, hd₀, hdr, B, hB, hLip⟩

theorem exists_circularMaterialTransferProfile_with_robustFlattenedGraph {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1) :
    ∃ P : CircularMaterialTransferProfile hγ hγ1,
      HasCircularFlattenedAncientSamples hγ hγ1 P.ancient ∧
      HasCircularRobustFlattenedAncientSamples hγ hγ1 P.ancient := by
  obtain ⟨P, hP⟩ := exists_circularMaterialTransferProfile_with_flattenedGraph hγ hγ1
  exact ⟨P, hP, hP.robust⟩

end Euler2D

end
