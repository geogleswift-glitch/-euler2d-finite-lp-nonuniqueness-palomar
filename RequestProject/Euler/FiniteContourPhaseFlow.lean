module

public import RequestProject.Euler.FiniteContourPhaseField
public import RequestProject.Euler.LocalSmoothBanachFlow

/-! Actual finite contour flows of every finite initial-data order at
every admissible phase, with their literal material boundary equation. -/

@[expose] public section

noncomputable section

open Set Filter Topology Metric
open scoped NNReal ContDiff

namespace Euler2D

local instance (priority := 2000) phaseFlowLittle_group (γ : ℝ≥0) :
    NormedAddCommGroup (LittleContourSpace γ) := Submodule.normedAddCommGroup (LittleContourSpace γ)
local instance (priority := 2000) phaseFlowLittle_space (γ : ℝ≥0) :
    NormedSpace ℝ (LittleContourSpace γ) := Submodule.normedSpace (LittleContourSpace γ)
local instance (priority := 2000) phaseFlowC1_group (γ : ℝ≥0) :
    NormedAddCommGroup (ContourC1Space γ) := Submodule.normedAddCommGroup (contourC1GraphSubmodule γ)

set_option maxHeartbeats 600000 in
theorem exists_finiteContour_phase_smooth_flow {γ : ℝ≥0} {ι : Type} [Fintype ι]
    (hγ : 0 < (γ : ℝ)) (hγ1 : (γ : ℝ) < 1)
    (Z₀ : ι → ContourC1Space γ) (r : ι → ℝ) (hr : ∀ i, 0 < r i)
    (href : ∀ i, ContourC1Space.lift γ (Z₀ i) = refCircle (r i)) (g : ι → ℝ)
    (Z : ι → LittleContourSpace γ) (hZ : IsPhaseAdmissibleLittleContourFamily Z₀ r Z) (n : ℕ) :
    ∃ ρ > 0, ∃ τ > 0, ∃ X : (ι → LittleContourSpace γ) → ℝ → ι → LittleContourSpace γ,
      IsBanachFlowOn (finiteContourPhaseFieldTotal hγ hγ1 Z₀ r hr href g)
        {W | IsPhaseAdmissibleLittleContourFamily Z₀ r W} (ball Z ρ) τ X ∧
      (∀ t ∈ Icc 0 τ, ContDiffOn ℝ n (fun W => X W t) (ball Z ρ)) ∧
      ∀ W ∈ ball Z ρ, ∀ t ∈ Icc 0 τ, ∀ i θ,
        HasDerivAt (fun s => LittleContourSpace.lift γ (X W s i) θ)
          (contourBoundaryField g (fun j => LittleContourSpace.lift γ (X W t j)) i θ) t := by
  obtain ⟨ρ, hρ, τ, hτ, X, hX, hs⟩ := exists_local_smooth_banachFlow n
    (isOpen_phaseAdmissibleLittleContourFamilies Z₀ r)
    (contDiffOn_finiteContourPhaseFieldTotal hγ hγ1 Z₀ r hr href g (⊤ : ℕ∞)) hZ
  refine ⟨ρ, hρ, τ, hτ, X, hX, hs, ?_⟩
  intro W hW t ht i θ
  have hd := ((LittleContourSpace.eval γ (θ : ContourCircle)).comp
    (ContinuousLinearMap.proj i)).hasFDerivAt.comp_hasDerivAt t (hX.hasDerivAt W hW t ht)
  change HasDerivAt (fun s => LittleContourSpace.lift γ (X W s i) θ)
    (LittleContourSpace.lift γ (finiteContourPhaseFieldTotal hγ hγ1 Z₀ r hr href g (X W t) i) θ) t at hd
  rw [lift_finiteContourPhaseFieldTotal hγ hγ1 Z₀ r hr href g (X W t) (hX.mem W hW t ht)] at hd
  exact hd

end Euler2D

end
