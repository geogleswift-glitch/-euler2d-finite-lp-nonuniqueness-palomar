module

public import RequestProject.Euler.CircularPhaseArea

/-! A genuine smooth full-period flow of the unchanged circular field,
with actual conservation of each interface area and of fourfold symmetry. -/

@[expose] public section

noncomputable section

open Set Filter Topology Metric
open scoped NNReal ContDiff

namespace Euler2D

local instance (priority := 2000) constrainedPeriodLittle_group (γ : ℝ≥0) :
    NormedAddCommGroup (LittleContourSpace γ) := Submodule.normedAddCommGroup (LittleContourSpace γ)
local instance (priority := 2000) constrainedPeriodLittle_space (γ : ℝ≥0) :
    NormedSpace ℝ (LittleContourSpace γ) := Submodule.normedSpace (LittleContourSpace γ)

set_option maxHeartbeats 600000 in
theorem exists_circularContour_constrained_period_flow {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1) (n : ℕ) :
    ∃ ρ > 0, ∃ X : (Fin 2 → LittleContourSpace γ) → ℝ → Fin 2 → LittleContourSpace γ,
      IsBanachFlowOn (circularBanachField hγ hγ1) (circularBanachDomain hγ hγ1)
        (ball (littleCircularReference hγ hγ1) ρ) period X ∧
      (∀ t ∈ Icc 0 period, ContDiffOn ℝ n (fun W => X W t)
        (ball (littleCircularReference hγ hγ1) ρ)) ∧
      X (littleCircularReference hγ hγ1) period = littleCircularReference hγ hγ1 ∧
      (∀ W ∈ ball (littleCircularReference hγ hγ1) ρ, ∀ t ∈ Icc 0 period,
        X W t ∈ circularQuarterPhaseDomain hγ hγ1) ∧
      (∀ W ∈ ball (littleCircularReference hγ hγ1) ρ, ∀ t ∈ Icc 0 period, ∀ i,
        littleContourArea γ (X W t i) = littleContourArea γ (W i)) ∧
      (∀ W ∈ ball (littleCircularReference hγ hγ1) ρ,
        (∀ i, W i ∈ fourfoldLittleContourSubmodule γ) →
          ∀ t ∈ Icc 0 period, ∀ i, X W t i ∈ fourfoldLittleContourSubmodule γ) := by
  have hf : ContDiffOn ℝ ∞ (circularBanachField hγ hγ1) (circularQuarterPhaseDomain hγ hγ1) :=
    (contDiffOn_finiteContourPhaseFieldTotal hγ hγ1 _ _ _ _ _ (⊤ : ℕ∞)).mono
      (fun _ hZ => hZ.1)
  have hp : 0 < period := by unfold period; positivity
  obtain ⟨ρ, hρ, X, hX, hs, he⟩ := exists_smooth_banachFlow_along_reference n
    (isOpen_circularQuarterPhaseDomain hγ hγ1) hf
    (contDiff_littleCircularMaterialContours hγ hγ1).continuous
    (littleCircularMaterialContours_mem_quarterPhaseDomain hγ hγ1)
    (littleCircularMaterialContours_hasDerivAt hγ hγ1) hp
  rw [littleCircularMaterialContours_zero] at hX hs he
  have hXorig : IsBanachFlowOn (circularBanachField hγ hγ1) (circularBanachDomain hγ hγ1)
      (ball (littleCircularReference hγ hγ1) ρ) period X :=
    ⟨hX.initial, hX.continuous, hX.hasDerivAt, fun W hW t ht => (hX.mem W hW t ht).1⟩
  refine ⟨ρ, hρ, X, hXorig, hs, ?_, hX.mem, ?_, ?_⟩
  · calc
      X (littleCircularReference hγ hγ1) period = littleCircularMaterialContours hγ hγ1 period :=
        he ⟨hp.le, le_rfl⟩
      _ = littleCircularReference hγ hγ1 := by
        rw [littleCircularMaterialContours_period, littleCircularMaterialContours_zero]
  · intro W hW t ht i
    exact circularBanachFlow_area hγ hγ1 hX hW ht i
  · intro W hW hfour t ht i
    exact circularBanachFlow_fourfold hγ hγ1 hXorig hW hfour ht i

theorem exists_circularContour_constrained_C3_periodMap {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1) :
    ∃ ρ > 0, ∃ P : (Fin 2 → LittleContourSpace γ) → Fin 2 → LittleContourSpace γ,
      ContDiffOn ℝ 3 P (ball (littleCircularReference hγ hγ1) ρ) ∧
      P (littleCircularReference hγ hγ1) = littleCircularReference hγ hγ1 ∧
      ∀ W ∈ ball (littleCircularReference hγ hγ1) ρ,
        (∀ i, littleContourArea γ (P W i) = littleContourArea γ (W i)) ∧
        ((∀ i, W i ∈ fourfoldLittleContourSubmodule γ) →
          ∀ i, P W i ∈ fourfoldLittleContourSubmodule γ) ∧
        ∃ Z : ℝ → Fin 2 → LittleContourSpace γ,
          Z 0 = W ∧ Z period = P W ∧
          (∀ t ∈ Icc 0 period, Z t ∈ circularQuarterPhaseDomain hγ hγ1) ∧
          ∀ t ∈ Icc 0 period, ∀ i θ,
            HasDerivAt (fun s => LittleContourSpace.lift γ (Z s i) θ)
              (contourBoundaryField circularContourStrengths
                (fun j => LittleContourSpace.lift γ (Z t j)) i θ) t := by
  obtain ⟨ρ, hρ, X, hX, hs, hfix, hnear, harea, hfour⟩ :=
    exists_circularContour_constrained_period_flow hγ hγ1 3
  have hp : 0 ≤ period := by unfold period; positivity
  refine ⟨ρ, hρ, fun W => X W period, hs period ⟨hp, le_rfl⟩, hfix, ?_⟩
  intro W hW
  refine ⟨harea W hW period ⟨hp, le_rfl⟩,
    fun hsym => hfour W hW hsym period ⟨hp, le_rfl⟩,
    X W, hX.initial W hW, rfl, hnear W hW, ?_⟩
  intro t ht i θ
  have hd := ((LittleContourSpace.eval γ (θ : ContourCircle)).comp
    (ContinuousLinearMap.proj i)).hasFDerivAt.comp_hasDerivAt t (hX.hasDerivAt W hW t ht)
  change HasDerivAt (fun s => LittleContourSpace.lift γ (X W s i) θ)
    (LittleContourSpace.lift γ (circularBanachField hγ hγ1 (X W t) i) θ) t at hd
  rw [circularBanachField, lift_finiteContourPhaseFieldTotal hγ hγ1 _ _ _ _ _
    (X W t) (hX.mem W hW t ht)] at hd
  exact hd

end Euler2D

end
