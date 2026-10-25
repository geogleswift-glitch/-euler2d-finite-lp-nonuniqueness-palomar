module

public import RequestProject.Euler.CircularPhaseArea

/-! A genuine smooth full-T flow of the unchanged circular field,
with actual conservation of each interface area and of fourfold symmetry. -/

@[expose] public section

noncomputable section

open Set Filter Topology Metric
open scoped NNReal ContDiff

namespace Euler2D

local instance (priority := 2000) constrainedIntervalLittle_group (γ : ℝ≥0) :
    NormedAddCommGroup (LittleContourSpace γ) := Submodule.normedAddCommGroup (LittleContourSpace γ)
local instance (priority := 2000) constrainedIntervalLittle_space (γ : ℝ≥0) :
    NormedSpace ℝ (LittleContourSpace γ) := Submodule.normedSpace (LittleContourSpace γ)

set_option maxHeartbeats 600000 in
theorem exists_circularContour_constrained_interval_flow {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1) (n : ℕ) {T : ℝ} (hT : 0 < T) :
    ∃ ρ > 0, ∃ X : (Fin 2 → LittleContourSpace γ) → ℝ → Fin 2 → LittleContourSpace γ,
      IsBanachFlowOn (circularBanachField hγ hγ1) (circularBanachDomain hγ hγ1)
        (ball (littleCircularReference hγ hγ1) ρ) T X ∧
      (∀ t ∈ Icc 0 T, ContDiffOn ℝ n (fun W => X W t)
        (ball (littleCircularReference hγ hγ1) ρ)) ∧
      X (littleCircularReference hγ hγ1) T = littleCircularMaterialContours hγ hγ1 T ∧
      (∀ W ∈ ball (littleCircularReference hγ hγ1) ρ, ∀ t ∈ Icc 0 T,
        X W t ∈ circularQuarterPhaseDomain hγ hγ1) ∧
      (∀ W ∈ ball (littleCircularReference hγ hγ1) ρ, ∀ t ∈ Icc 0 T, ∀ i,
        littleContourArea γ (X W t i) = littleContourArea γ (W i)) ∧
      (∀ W ∈ ball (littleCircularReference hγ hγ1) ρ,
        (∀ i, W i ∈ fourfoldLittleContourSubmodule γ) →
          ∀ t ∈ Icc 0 T, ∀ i, X W t i ∈ fourfoldLittleContourSubmodule γ) := by
  have hf : ContDiffOn ℝ ∞ (circularBanachField hγ hγ1) (circularQuarterPhaseDomain hγ hγ1) :=
    (contDiffOn_finiteContourPhaseFieldTotal hγ hγ1 _ _ _ _ _ (⊤ : ℕ∞)).mono
      (fun _ hZ => hZ.1)
  have hp : 0 < T := hT
  obtain ⟨ρ, hρ, X, hX, hs, he⟩ := exists_smooth_banachFlow_along_reference n
    (isOpen_circularQuarterPhaseDomain hγ hγ1) hf
    (contDiff_littleCircularMaterialContours hγ hγ1).continuous
    (littleCircularMaterialContours_mem_quarterPhaseDomain hγ hγ1)
    (littleCircularMaterialContours_hasDerivAt hγ hγ1) hp
  rw [littleCircularMaterialContours_zero] at hX hs he
  have hXorig : IsBanachFlowOn (circularBanachField hγ hγ1) (circularBanachDomain hγ hγ1)
      (ball (littleCircularReference hγ hγ1) ρ) T X :=
    ⟨hX.initial, hX.continuous, hX.hasDerivAt, fun W hW t ht => (hX.mem W hW t ht).1⟩
  refine ⟨ρ, hρ, X, hXorig, hs, ?_, hX.mem, ?_, ?_⟩
  · exact he ⟨hp.le, le_rfl⟩
  · intro W hW t ht i
    exact circularBanachFlow_area hγ hγ1 hX hW ht i
  · intro W hW hfour t ht i
    exact circularBanachFlow_fourfold hγ hγ1 hXorig hW hfour ht i


end Euler2D

end

