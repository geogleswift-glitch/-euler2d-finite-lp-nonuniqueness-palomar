module

public import RequestProject.Euler.CircularSharpBackwardAsymptotic
public import RequestProject.Euler.CircularPatchMomentSmooth
public import RequestProject.Euler.CircularPatchMomentUnstableLinear
public import RequestProject.Euler.BanachObservableAsymptotic
public import RequestProject.Euler.CircularConstrainedPatchMoment
public import RequestProject.Euler.BanachNonzeroOrbitAsymptotic
public import RequestProject.Euler.CircularHyperbolicGap
public import RequestProject.Euler.BanachDoubleReturn
public import RequestProject.Euler.BanachNonlinearKernelOrbit

/-! Genuine nonlinear ancient discrete orbits of the original
fourfold fixed-area return map. The full original Banach power bound,
actual unstable projection, and true derivative are used directly. -/

@[expose] public section

set_option maxHeartbeats 16000000
set_option maxRecDepth 4000

noncomputable section

open Set Filter Topology Metric
open scoped NNReal ContDiff

namespace Euler2D

local instance (priority := 2000) momentAsymptoticLittle_group (γ : ℝ≥0) :
    NormedAddCommGroup (LittleContourSpace γ) := Submodule.normedAddCommGroup (LittleContourSpace γ)
local instance (priority := 2000) momentAsymptoticLittle_space (γ : ℝ≥0) :
    NormedSpace ℝ (LittleContourSpace γ) := Submodule.normedSpace (LittleContourSpace γ)
local instance (priority := 2000) momentAsymptoticFamily_tower (γ : ℝ≥0) :
    IsScalarTower ℝ ℝ (Fin 2 → LittleContourSpace γ) where
  smul_assoc a b Z := by
    funext i
    change (a * b) • Z i = a • (b • Z i)
    exact (smul_smul a b (Z i)).symm
local instance (priority := 2000) momentAsymptoticTangent_group (γ : ℝ≥0) :
    NormedAddCommGroup (CircularConstrainedTangentSpace γ) :=
  Submodule.normedAddCommGroup (circularConstrainedTangentSubmodule γ)
local instance (priority := 2000) momentAsymptoticTangent_space (γ : ℝ≥0) :
    NormedSpace ℝ (CircularConstrainedTangentSpace γ) :=
  Submodule.normedSpace (circularConstrainedTangentSubmodule γ)
local instance (priority := 2000) momentAsymptoticTangent_continuousAdd (γ : ℝ≥0) :
    ContinuousAdd (CircularConstrainedTangentSpace γ) where
  continuous_add := by
    have h1 : Continuous (fun p : CircularConstrainedTangentSpace γ × CircularConstrainedTangentSpace γ =>
        p.1.val) := continuous_subtype_val.comp continuous_fst
    have h2 : Continuous (fun p : CircularConstrainedTangentSpace γ × CircularConstrainedTangentSpace γ =>
        p.2.val) := continuous_subtype_val.comp continuous_snd
    exact (h1.add h2).subtype_mk _
local instance (priority := 2000) momentAsymptoticEndo_monoid (γ : ℝ≥0) :
    Monoid (CircularConstrainedTangentSpace γ →L[ℝ] CircularConstrainedTangentSpace γ) :=
  (ContinuousLinearMap.monoidWithZero :
    MonoidWithZero (CircularConstrainedTangentSpace γ →L[ℝ] CircularConstrainedTangentSpace γ)).toMonoid
local instance (priority := 2000) momentAsymptoticTangent_complete (γ : ℝ≥0) :
    CompleteSpace (CircularConstrainedTangentSpace γ) := circularConstrainedTangentSpace_complete γ

attribute [local irreducible] circularConstrainedTangentSubmodule circularConstrainedUnstableProjectionCLM
  circularConstrainedReturnMap circularConstrainedUnstableEmbeddingCLM circularConstrainedUnstableCoordinateCLM
  circularConstrainedChart circularConstraintProjectionToTangentCLM circularConstrainedPatchFourthMoment

theorem exists_circularConstrained_patchMoment_asymptotic_orbit {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1) {R : ℝ} (hR : 0 < R)
    {X : (Fin 2 → LittleContourSpace γ) → ℝ → Fin 2 → LittleContourSpace γ}
    (hX : IsBanachFlowOn (circularBanachField hγ hγ1) (circularBanachDomain hγ hγ1)
      (ball (littleCircularReference hγ hγ1) R) period X)
    (hd : ContDiffAt ℝ 2 (fun W => X W period) (littleCircularReference hγ hγ1))
    (hfix : X (littleCircularReference hγ hγ1) period = littleCircularReference hγ hγ1)
    (harea : ∀ W ∈ ball (littleCircularReference hγ hγ1) R, ∀ i,
      littleContourArea γ (X W period i) = littleContourArea γ (W i))
    {rmax : ℝ} (hrmax : 0 < rmax) :
    ∃ t : ℝ, 0 < t ∧ ∃ x : ℕ → CircularConstrainedTangentSpace γ,
    ∃ ν : ℂ, ν ≠ 0 ∧ ∃ E > 0,
      (∀ n, banachDoubleReturn (circularConstrainedReturnMap hγ hγ1 (fun W => X W period))
        (x (n + 1)) = x n) ∧
      (∀ n, x n ∈ closedBall 0 rmax) ∧
      (∀ n, ‖x n‖ ≤ 2 * circularAncientBackwardRatio ^ n *
        ‖t • circularConstrainedUnstableEmbeddingCLM hγ hγ1.le 1‖) ∧
      circularConstrainedPatchFourthMoment hγ hγ1.le (x 0) ≠ 0 ∧
      (∀ n : ℕ, ‖circularConstrainedPatchFourthMoment hγ hγ1.le (x n) -
        ((lamMult ^ 2)⁻¹) ^ n • ν‖ ≤ E * (circularAncientBackwardRatio ^ 2) ^ n) ∧
      Tendsto x atTop (𝓝 0) := by
  obtain ⟨κ, hκ, rq, hrq, hquad⟩ := exists_circularConstrainedPatchFourthMoment_quadratic_bound hγ hγ1.le
  let cap := min rmax rq
  have hcap : 0 < cap := lt_min hrmax hrq
  obtain ⟨t, ht, x, c, B, hB, hrec, hball, hnorm, hproj, hcP, hcne, herr, hmoment, hlim⟩ :=
    exists_circularConstrained_nonzero_asymptotic_orbit hγ hγ1 hR hX hd hfix harea hcap
  let D := fderiv ℝ (circularConstrainedPatchFourthMoment hγ hγ1.le) 0
  let ν := D c
  have hν : ν ≠ 0 := fderiv_circularConstrainedPatchFourthMoment_ne_zero_on_unstable hγ hγ1 c hcP hcne
  have hxn (n : ℕ) : ‖x n‖ ≤ (2 * ‖t • circularConstrainedUnstableEmbeddingCLM hγ hγ1.le 1‖) *
      circularAncientBackwardRatio ^ n := by
    calc
      _ ≤ 2 * circularAncientBackwardRatio ^ n *
        ‖t • circularConstrainedUnstableEmbeddingCLM hγ hγ1.le 1‖ := hnorm n
      _ = _ := by ring
  have hxq (n : ℕ) : ‖circularConstrainedPatchFourthMoment hγ hγ1.le (x n) - D (x n)‖ ≤
      κ * ‖x n‖ ^ 2 := hquad _ (closedBall_subset_closedBall (min_le_right _ _) (hball n))
  let Cerr := κ * (2 * ‖t • circularConstrainedUnstableEmbeddingCLM hγ hγ1.le 1‖) ^ 2 + ‖D‖ * B
  let E := Cerr + 1
  have hE : 0 < E := by dsimp only [E, Cerr]; positivity
  refine ⟨t, ht, x, ν, hν, E, hE, hrec,
    fun n => closedBall_subset_closedBall (min_le_left _ _) (hball n), hnorm, hmoment, ?_, hlim⟩
  intro n
  have he := observable_quadratic_backward_asymptotic (a := lamMult ^ 2) (b := circularAncientBackwardRatio)
    (circularConstrainedPatchFourthMoment hγ hγ1.le) D x c hκ.le hxn herr hxq n
  calc
    _ ≤ Cerr * (circularAncientBackwardRatio ^ 2) ^ n := he
    _ ≤ E * (circularAncientBackwardRatio ^ 2) ^ n := mul_le_mul_of_nonneg_right
      (by dsimp only [E]; linarith) (pow_nonneg (sq_nonneg _) n)

end Euler2D

end
