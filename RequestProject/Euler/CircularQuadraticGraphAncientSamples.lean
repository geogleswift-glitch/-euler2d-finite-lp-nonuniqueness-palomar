module

public import RequestProject.Euler.CircularQuadraticBackwardGraph

/-! The existing actual ancient material samples are retained and
identified with the same-X quadratic graph after a deep negative shift. -/

@[expose] public section

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000

noncomputable section

open Set Filter Topology Metric
open scoped NNReal ContDiff

namespace Euler2D

local instance (priority := 2000) sampleGraphLittle_group (γ : ℝ≥0) :
    NormedAddCommGroup (LittleContourSpace γ) := Submodule.normedAddCommGroup (LittleContourSpace γ)
local instance (priority := 2000) sampleGraphLittle_space (γ : ℝ≥0) :
    NormedSpace ℝ (LittleContourSpace γ) := Submodule.normedSpace (LittleContourSpace γ)
local instance (priority := 2000) sampleGraphFamily_tower (γ : ℝ≥0) :
    IsScalarTower ℝ ℝ (Fin 2 → LittleContourSpace γ) where
  smul_assoc a b Z := by
    funext i
    change (a * b) • Z i = a • (b • Z i)
    exact (smul_smul a b (Z i)).symm
local instance (priority := 2000) sampleGraphTangent_group (γ : ℝ≥0) :
    NormedAddCommGroup (CircularConstrainedTangentSpace γ) :=
  Submodule.normedAddCommGroup (circularConstrainedTangentSubmodule γ)
local instance (priority := 2000) sampleGraphTangent_space (γ : ℝ≥0) :
    NormedSpace ℝ (CircularConstrainedTangentSpace γ) :=
  Submodule.normedSpace (circularConstrainedTangentSubmodule γ)
local instance (priority := 2000) sampleGraphTangent_continuousAdd (γ : ℝ≥0) :
    ContinuousAdd (CircularConstrainedTangentSpace γ) where
  continuous_add := by
    have h1 : Continuous (fun p : CircularConstrainedTangentSpace γ × CircularConstrainedTangentSpace γ =>
        p.1.val) := continuous_subtype_val.comp continuous_fst
    have h2 : Continuous (fun p : CircularConstrainedTangentSpace γ × CircularConstrainedTangentSpace γ =>
        p.2.val) := continuous_subtype_val.comp continuous_snd
    exact (h1.add h2).subtype_mk _
local instance (priority := 2000) sampleGraphEndo_monoid (γ : ℝ≥0) :
    Monoid (CircularConstrainedTangentSpace γ →L[ℝ] CircularConstrainedTangentSpace γ) :=
  (ContinuousLinearMap.monoidWithZero :
    MonoidWithZero (CircularConstrainedTangentSpace γ →L[ℝ] CircularConstrainedTangentSpace γ)).toMonoid
local instance (priority := 2000) sampleGraphTangent_complete (γ : ℝ≥0) :
    CompleteSpace (CircularConstrainedTangentSpace γ) := circularConstrainedTangentSpace_complete γ

attribute [local irreducible] circularConstrainedTangentSubmodule circularConstrainedUnstableProjectionCLM
  circularConstrainedReturnMap circularConstrainedUnstableEmbeddingCLM circularConstrainedUnstableCoordinateCLM
  circularConstrainedChart circularConstraintProjectionToTangentCLM

theorem circularAncient_samples_on_quadraticBackwardGraph {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1)
    {X : (Fin 2 → LittleContourSpace γ) → ℝ → Fin 2 → LittleContourSpace γ}
    {r : ℝ} (hr : 0 < r)
    {x : CircularConstrainedTangentSpace γ → ℕ → CircularConstrainedTangentSpace γ}
    (hg : IsLocalWeightedBackwardGraph
      (banachDoubleReturn (circularConstrainedReturnMap hγ hγ1 (fun W => X W period)))
      (circularConstrainedUnstableProjectionCLM hγ hγ1.le) circularAncientBackwardWeight r x)
    (y : ℕ → CircularConstrainedTangentSpace γ)
    (hback : ∀ n, banachDoubleReturn (circularConstrainedReturnMap hγ hγ1 (fun W => X W period))
      (y (n + 1)) = y n)
    {C : ℝ} (hnorm : ∀ n, ‖y n‖ ≤ C * (circularAncientBackwardWeight⁻¹) ^ n)
    (Y : ℝ → Fin 2 → LittleContourSpace γ)
    (hYsamp : ∀ n : ℕ, Y (-((n : ℕ) : ℝ) * (period + period)) =
      circularConstrainedChart hγ hγ1 (y n)) :
    ∃ N : ℕ, ∀ n ≥ N,
      ‖circularConstrainedUnstableProjectionCLM hγ hγ1.le (y n)‖ ≤ r / 2 ∧
      x (circularConstrainedUnstableProjectionCLM hγ hγ1.le (y n)) = (fun k => y (n + k)) ∧
      Y (-((n : ℕ) : ℝ) * (period + period)) =
        circularConstrainedChart hγ hγ1
          (x (circularConstrainedUnstableProjectionCLM hγ hγ1.le (y n)) 0) := by
  have hw : 1 < circularAncientBackwardWeight := by
    have hh := circularAncientBackwardWeight_bounds.1
    linarith
  obtain ⟨N, hN⟩ := hg.exists_orbit_tail_eq hw hr
    (circularConstrainedUnstableProjectionCLM_idempotent hγ hγ1.le) y hback hnorm
  refine ⟨N, ?_⟩
  intro n hn
  have ht := hN n hn
  refine ⟨ht.1, ht.2, ?_⟩
  rw [ht.2, hYsamp n]
  rfl

theorem exists_circularAncient_same_samples_quadraticGraph {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1) {R : ℝ} (hR : 0 < R)
    {X : (Fin 2 → LittleContourSpace γ) → ℝ → Fin 2 → LittleContourSpace γ}
    (hX : IsBanachFlowOn (circularBanachField hγ hγ1) (circularBanachDomain hγ hγ1)
      (ball (littleCircularReference hγ hγ1) R) period X)
    (hd : ContDiffAt ℝ 2 (fun W => X W period) (littleCircularReference hγ hγ1))
    (hfix : X (littleCircularReference hγ hγ1) period = littleCircularReference hγ hγ1)
    (harea : ∀ W ∈ ball (littleCircularReference hγ hγ1) R, ∀ i,
      littleContourArea γ (X W period i) = littleContourArea γ (W i))
    (y : ℕ → CircularConstrainedTangentSpace γ)
    (hback : ∀ n, banachDoubleReturn (circularConstrainedReturnMap hγ hγ1 (fun W => X W period))
      (y (n + 1)) = y n)
    {C : ℝ} (hnorm : ∀ n, ‖y n‖ ≤ C * (circularAncientBackwardWeight⁻¹) ^ n)
    (Y : ℝ → Fin 2 → LittleContourSpace γ)
    (hYsamp : ∀ n : ℕ, Y (-((n : ℕ) : ℝ) * (period + period)) =
      circularConstrainedChart hγ hγ1 (y n))
    {rmax : ℝ} (hrmax : 0 < rmax) :
    ∃ r > 0, r ≤ rmax ∧ ∃ x : CircularConstrainedTangentSpace γ → ℕ → CircularConstrainedTangentSpace γ,
      IsLocalWeightedBackwardGraph
        (banachDoubleReturn (circularConstrainedReturnMap hγ hγ1 (fun W => X W period)))
        (circularConstrainedUnstableProjectionCLM hγ hγ1.le) circularAncientBackwardWeight r x ∧
      ∃ H > 0,
        (∀ ξ, circularConstrainedUnstableProjectionCLM hγ hγ1.le ξ = ξ → ‖ξ‖ ≤ r / 2 →
          ∀ ζ, circularConstrainedUnstableProjectionCLM hγ hγ1.le ζ = ζ → ‖ζ‖ ≤ r / 2 →
            ‖(x ξ 0 - ξ) - (x ζ 0 - ζ)‖ ≤ H * (‖ξ‖ + ‖ζ‖) * ‖ξ - ζ‖) ∧
        ∃ N : ℕ, ∀ n ≥ N,
          ‖circularConstrainedUnstableProjectionCLM hγ hγ1.le (y n)‖ ≤ r / 2 ∧
          x (circularConstrainedUnstableProjectionCLM hγ hγ1.le (y n)) = (fun k => y (n + k)) ∧
          Y (-((n : ℕ) : ℝ) * (period + period)) =
            circularConstrainedChart hγ hγ1
              (x (circularConstrainedUnstableProjectionCLM hγ hγ1.le (y n)) 0) := by
  obtain ⟨r, hr, hrr, x, hg, _, H, hH, hquad, _⟩ :=
    exists_circularConstrained_quadraticBackwardGraph hγ hγ1 hR hX hd hfix harea hrmax
  exact ⟨r, hr, hrr, x, hg, H, hH, hquad,
    circularAncient_samples_on_quadraticBackwardGraph hγ hγ1 hr hg y hback hnorm Y hYsamp⟩

end Euler2D

end
