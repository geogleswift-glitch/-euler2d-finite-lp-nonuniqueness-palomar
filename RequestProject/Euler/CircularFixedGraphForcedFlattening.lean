module

public import RequestProject.Euler.CircularFixedGraphQuadraticBound
public import RequestProject.Euler.BanachLocalFlatEndpointPerturbation

/-! The same fixed ancient graph admits robust flattened return bounds.
A small error in the actual endpoint gives a controlled additive error
in both capture coordinates. The projection stay-in-range conclusions
are proved from the actual unforced remainder bound. -/

@[expose] public section

set_option maxHeartbeats 24000000
set_option maxRecDepth 4000

noncomputable section

open Set Filter Topology Metric
open scoped NNReal ContDiff

namespace Euler2D

local instance (priority := 2000) fixedForceLittle_group (γ : ℝ≥0) :
    NormedAddCommGroup (LittleContourSpace γ) := Submodule.normedAddCommGroup (LittleContourSpace γ)
local instance (priority := 2000) fixedForceLittle_space (γ : ℝ≥0) :
    NormedSpace ℝ (LittleContourSpace γ) := Submodule.normedSpace (LittleContourSpace γ)
local instance (priority := 2000) fixedForceFamily_tower (γ : ℝ≥0) :
    IsScalarTower ℝ ℝ (Fin 2 → LittleContourSpace γ) where
  smul_assoc a b Z := by
    funext i
    change (a * b) • Z i = a • (b • Z i)
    exact (smul_smul a b (Z i)).symm
local instance (priority := 2000) fixedForceTangent_group (γ : ℝ≥0) :
    NormedAddCommGroup (CircularConstrainedTangentSpace γ) :=
      Submodule.normedAddCommGroup (circularConstrainedTangentSubmodule γ)
local instance (priority := 2000) fixedForceTangent_space (γ : ℝ≥0) :
    NormedSpace ℝ (CircularConstrainedTangentSpace γ) :=
      Submodule.normedSpace (circularConstrainedTangentSubmodule γ)
local instance (priority := 2000) fixedForceTangent_continuousAdd (γ : ℝ≥0) :
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

theorem circularFixedBackwardGraph_forced_flattened_bounds {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1) {R r s C : ℝ}
    (hR : 0 < R) (hr : 0 < r) (hs : 0 < s) (hC : 0 < C)
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
      (circularConstrainedUnstableProjectionCLM hγ hγ1.le) circularAncientBackwardWeight r x)
    (hflat : ∀ α w, circularConstrainedUnstableProjectionCLM hγ hγ1.le α = α →
      circularConstrainedUnstableProjectionCLM hγ hγ1.le w = 0 → ‖α‖ + ‖w‖ ≤ s →
      let P := circularConstrainedUnstableProjectionCLM hγ hγ1.le
      let F := circularConstrainedReturnMap hγ hγ1 (fun W => X W period)
      let L := fderiv ℝ F 0
      let g := fun v => x v 0 - v
      let z := α + g α + w
      ‖P (F z) - (-lamMult : ℝ) • α‖ ≤ C * (‖α‖ + ‖w‖) ^ 2 ∧
      ‖(F z - P (F z)) - g (P (F z)) - L w‖ ≤ C * (‖α‖ + ‖w‖) * ‖w‖) :
    ∃ t > 0, t ≤ s ∧ ∃ η₀ > 0, ∃ B > 0, ∀ α w,
      circularConstrainedUnstableProjectionCLM hγ hγ1.le α = α →
      circularConstrainedUnstableProjectionCLM hγ hγ1.le w = 0 → ‖α‖ + ‖w‖ ≤ t →
      let P := circularConstrainedUnstableProjectionCLM hγ hγ1.le
      let F := circularConstrainedReturnMap hγ hγ1 (fun W => X W period)
      let L := fderiv ℝ F 0
      let g := fun v => x v 0 - v
      let z := α + g α + w
      ∀ v {η : ℝ}, 0 ≤ η → η ≤ η₀ → ‖v - F z‖ ≤ η →
        ‖P v - (-lamMult : ℝ) • α‖ ≤ C * (‖α‖ + ‖w‖) ^ 2 + ‖P‖ * η ∧
        ‖(v - P v) - g (P v) - L w‖ ≤ C * (‖α‖ + ‖w‖) * ‖w‖ + B * η := by
  obtain ⟨d, hd₀, _, B, hB, hLip⟩ :=
    circularFixedBackwardGraph_flattening_lipschitz hγ hγ1 hR hr hX hd hfix harea hg
  let P := circularConstrainedUnstableProjectionCLM hγ hγ1.le
  let F := circularConstrainedReturnMap hγ hγ1 (fun W => X W period)
  let g := fun v => x v 0 - v
  have hLam : 0 < lamMult := zero_lt_one.trans one_lt_lamMult
  have hU (α : CircularConstrainedTangentSpace γ) :
      ‖(-lamMult : ℝ) • α‖ = lamMult * ‖α‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_neg, abs_of_pos hLam]
  obtain ⟨t, ht, hts, η₀, hη₀, hbounds⟩ :=
    local_flattened_bounds_of_endpoint_perturbation F (fderiv ℝ F 0) P g
      (fun α => (-lamMult : ℝ) • α) hLam.le hC hs hd₀ hB hU hLip hflat
  exact ⟨t, ht, hts, η₀, hη₀, B, hB, hbounds⟩

end Euler2D

end
