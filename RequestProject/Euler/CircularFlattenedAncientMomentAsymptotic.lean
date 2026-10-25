module

public import RequestProject.Euler.CircularAncientMomentAsymptotic
public import RequestProject.Euler.CircularSharpFlattenedAncientSamples
public import RequestProject.Euler.CircularMomentAsymptoticOfSharpState

/-! The same actual sharp material Y supplies both its genuine nonzero
moment asymptotic and the original return-map flattening budget. -/

@[expose] public section

set_option maxHeartbeats 20000000
set_option maxRecDepth 4000

noncomputable section

open Set Filter Topology Metric Asymptotics
open scoped NNReal ContDiff

namespace Euler2D

local instance (priority := 2000) flattenedMomentLittle_group (γ : ℝ≥0) :
    NormedAddCommGroup (LittleContourSpace γ) := Submodule.normedAddCommGroup (LittleContourSpace γ)
local instance (priority := 2000) flattenedMomentLittle_space (γ : ℝ≥0) :
    NormedSpace ℝ (LittleContourSpace γ) := Submodule.normedSpace (LittleContourSpace γ)
local instance (priority := 2000) flattenedMomentFamily_tower (γ : ℝ≥0) :
    IsScalarTower ℝ ℝ (Fin 2 → LittleContourSpace γ) where
  smul_assoc a b Z := by
    funext i
    change (a * b) • Z i = a • (b • Z i)
    exact (smul_smul a b (Z i)).symm
local instance (priority := 2000) flattenedMomentTangent_group (γ : ℝ≥0) :
    NormedAddCommGroup (CircularConstrainedTangentSpace γ) :=
  Submodule.normedAddCommGroup (circularConstrainedTangentSubmodule γ)
local instance (priority := 2000) flattenedMomentTangent_space (γ : ℝ≥0) :
    NormedSpace ℝ (CircularConstrainedTangentSpace γ) :=
  Submodule.normedSpace (circularConstrainedTangentSubmodule γ)
local instance (priority := 2000) flattenedMomentTangent_continuousAdd (γ : ℝ≥0) :
    ContinuousAdd (CircularConstrainedTangentSpace γ) where
  continuous_add := by
    have h1 : Continuous (fun p : CircularConstrainedTangentSpace γ × CircularConstrainedTangentSpace γ =>
        p.1.val) := continuous_subtype_val.comp continuous_fst
    have h2 : Continuous (fun p : CircularConstrainedTangentSpace γ × CircularConstrainedTangentSpace γ =>
        p.2.val) := continuous_subtype_val.comp continuous_snd
    exact (h1.add h2).subtype_mk _

attribute [local irreducible] circularConstrainedTangentSubmodule circularConstrainedUnstableProjectionCLM
  circularConstrainedUnstableEmbeddingCLM circularConstrainedUnstableCoordinateCLM

theorem exists_circularAncientMaterial_fourthMoment_with_flattenedGraph {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1) :
    ∃ Y : ℝ → Fin 2 → LittleContourSpace γ, ∃ κ : ℂ, ∃ δ > 0,
      κ ≠ 0 ∧ ContinuousOn Y (Iic 0) ∧
      (∀ s ≤ 0, Y s ∈ circularQuarterPhaseDomain hγ hγ1) ∧
      (∀ s ≤ 0, HasDerivAt Y (circularBanachField hγ hγ1 (Y s)) s) ∧
      Tendsto (fun n : ℕ => Y (-(n : ℝ) * (period + period))) atTop
        (𝓝 (littleCircularReference hγ hγ1)) ∧
      (∀ s ≤ 0, ∀ i, littleContourArea γ (Y s i) = Real.pi * circularContourRadii i ^ 2) ∧
      (∀ s ≤ 0, ∀ i, Y s i ∈ fourfoldLittleContourSubmodule γ) ∧
      (fun s : ℝ => circularBoundaryFourthMoment (Y s) - κ * Complex.exp ((s : ℂ) * lamStar)) =O[atBot]
        (fun s : ℝ => Real.exp ((sigma + δ) * s)) ∧
      HasCircularFlattenedAncientSamples hγ hγ1 Y := by
  obtain ⟨Y, A, v, E, hE, hYc, hYm, hYd, hLim, hArea, hFour,
      hAc, hA0, hAd, hvP, hv0, hstate, hflatY⟩ :=
    exists_circularAncientMaterial_sharp_with_flattenedGraph hγ hγ1
  obtain ⟨κ, δ, hδ, hκ, hbot⟩ := circularAncient_fourthMoment_asymptotic_of_sharp_state
    hγ hγ1 Y A v hE hAc hA0 hAd hvP hv0 hstate
  exact ⟨Y, κ, δ, hδ, hκ, hYc, hYm, hYd, hLim, hArea, hFour, hbot, hflatY⟩

end Euler2D

end

