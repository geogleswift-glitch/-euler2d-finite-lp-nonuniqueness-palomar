module

public import RequestProject.Euler.FinitePhaseForcedLocalFlow
public import RequestProject.Euler.BanachTimeContinuousForcing

/-! Restart at an arbitrary absolute time using the same forcing,
including the original material boundary equation. -/

@[expose] public section

set_option maxHeartbeats 3000000

noncomputable section

open Set Filter Topology Metric
open scoped NNReal

namespace Euler2D

local instance (priority := 2000) phaseTimeRestartLittle_group (γ : ℝ≥0) :
    NormedAddCommGroup (LittleContourSpace γ) := Submodule.normedAddCommGroup (LittleContourSpace γ)
local instance (priority := 2000) phaseTimeRestartLittle_space (γ : ℝ≥0) :
    NormedSpace ℝ (LittleContourSpace γ) := Submodule.normedSpace (LittleContourSpace γ)
local instance (priority := 2000) phaseTimeRestartC1_group (γ : ℝ≥0) :
    NormedAddCommGroup (ContourC1Space γ) := Submodule.normedAddCommGroup (contourC1GraphSubmodule γ)
local instance (priority := 2000) phaseTimeRestartC1_space (γ : ℝ≥0) :
    NormedSpace ℝ (ContourC1Space γ) := Submodule.normedSpace (contourC1GraphSubmodule γ)

theorem exists_finitePhase_time_restart {γ : ℝ≥0} {ι : Type} [Fintype ι]
    (hγ : 0 < (γ : ℝ)) (hγ1 : (γ : ℝ) < 1)
    (Z₀ : ι → ContourC1Space γ) (r : ι → ℝ) (hr : ∀ i, 0 < r i)
    (href : ∀ i, ContourC1Space.lift γ (Z₀ i) = refCircle (r i)) (g : ι → ℝ)
    (Z : ι → LittleContourSpace γ) (hZ : IsPhaseAdmissibleLittleContourFamily Z₀ r Z)
    (E : ℝ → (ι → LittleContourSpace γ) → ι → LittleContourSpace γ)
    {U : Set (ι → LittleContourSpace γ)} {K : ℝ≥0} {H : ℝ}
    (hH : 0 < H) (hU : U ∈ 𝓝 Z)
    (hELip : ∀ t, LipschitzOnWith K (E t) U)
    (hEc : ∀ W ∈ U, Continuous (fun t => E t W)) (τ : ℝ) :
    ∃ ρ > 0, ∃ δ > 0, δ ≤ H ∧
      ∃ X : (ι → LittleContourSpace γ) → ℝ → ι → LittleContourSpace γ,
      IsNonautonomousBanachFlowOn
        (fun t W => finiteContourPhaseFieldTotal hγ hγ1 Z₀ r hr href g W + E (τ + t) W)
        ({W | IsPhaseAdmissibleLittleContourFamily Z₀ r W} ∩ U) (ball Z ρ) δ X ∧
      ∀ W ∈ ball Z ρ, ∀ t ∈ Icc (0 : ℝ) δ, ∀ i θ,
        HasDerivAt (fun s => LittleContourSpace.lift γ (X W s i) θ)
          (contourBoundaryField g (fun j => LittleContourSpace.lift γ (X W t j)) i θ +
            LittleContourSpace.lift γ (E (τ + t) (X W t) i) θ) t := by
  apply exists_finitePhase_forced_local_flow hγ hγ1 Z₀ r hr href g Z hZ
    (fun t W => E (τ + t) W) hH hU
  · intro t _
    exact hELip (τ + t)
  · intro W hW
    exact ((hEc W hW).comp (continuous_const.add continuous_id)).continuousOn

theorem continuousAt_finitePhase_forcedField {γ : ℝ≥0} {ι : Type} [Fintype ι]
    (hγ : 0 < (γ : ℝ)) (hγ1 : (γ : ℝ) < 1)
    (Z₀ : ι → ContourC1Space γ) (r : ι → ℝ) (hr : ∀ i, 0 < r i)
    (href : ∀ i, ContourC1Space.lift γ (Z₀ i) = refCircle (r i)) (g : ι → ℝ)
    (Z : ι → LittleContourSpace γ) (hZ : IsPhaseAdmissibleLittleContourFamily Z₀ r Z)
    (E : ℝ → (ι → LittleContourSpace γ) → ι → LittleContourSpace γ)
    {U : Set (ι → LittleContourSpace γ)} {K : ℝ≥0} {τ : ℝ}
    (hU : U ∈ 𝓝 Z) (hELip : ∀ t, LipschitzOnWith K (E t) U)
    (hEc : ContinuousAt (fun t => E t Z) τ) :
    ContinuousAt (fun p : ℝ × (ι → LittleContourSpace γ) =>
      finiteContourPhaseFieldTotal hγ hγ1 Z₀ r hr href g p.2 + E p.1 p.2) (τ, Z) := by
  exact (((contDiffAt_finiteContourPhaseFieldTotal hγ hγ1 Z₀ r hr href g Z hZ 1).continuousAt).comp
      continuous_snd.continuousAt).add (continuousAt_timeState_of_lipschitzOn hU hELip hEc)

end Euler2D

end
