module

public import RequestProject.Euler.CircularGrowingInitial
public import RequestProject.Euler.CircularConstrainedPeriodMap

/-! Concrete nonlinear one-period growth in an actual full-period
material flow, with the original interface areas and fourfold symmetry
preserved throughout. This does not yet construct an ancient orbit. -/

@[expose] public section

noncomputable section

open Set Filter Topology Metric
open scoped NNReal ContDiff

namespace Euler2D

local instance (priority := 2000) nonlinearPeriodLittle_group (γ : ℝ≥0) :
    NormedAddCommGroup (LittleContourSpace γ) := Submodule.normedAddCommGroup (LittleContourSpace γ)
local instance (priority := 2000) nonlinearPeriodLittle_space (γ : ℝ≥0) :
    NormedSpace ℝ (LittleContourSpace γ) := Submodule.normedSpace (LittleContourSpace γ)

set_option maxHeartbeats 800000 in
theorem exists_circularContour_constrained_one_period_growth {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1) :
    ∃ ρ > 0, ∃ X : (Fin 2 → LittleContourSpace γ) → ℝ → Fin 2 → LittleContourSpace γ,
      IsBanachFlowOn (circularBanachField hγ hγ1) (circularBanachDomain hγ hγ1)
        (ball (littleCircularReference hγ hγ1) ρ) period X ∧
      ContDiffOn ℝ 3 (fun W => X W period) (ball (littleCircularReference hγ hγ1) ρ) ∧
      X (littleCircularReference hγ hγ1) period = littleCircularReference hγ hγ1 ∧
      ∀ᶠ s : ℝ in 𝓝[≠] 0,
        circularGrowingInitial hγ hγ1 s ∈ ball (littleCircularReference hγ hγ1) ρ ∧
        (∀ i, littleContourArea γ (circularGrowingInitial hγ hγ1 s i) =
          Real.pi * circularContourRadii i ^ 2) ∧
        (∀ t ∈ Icc 0 period,
          X (circularGrowingInitial hγ hγ1 s) t ∈ circularQuarterPhaseDomain hγ hγ1 ∧
          ∀ i, littleContourArea γ (X (circularGrowingInitial hγ hγ1 s) t i) =
              Real.pi * circularContourRadii i ^ 2 ∧
            X (circularGrowingInitial hγ hγ1 s) t i ∈ fourfoldLittleContourSubmodule γ) ∧
        ‖circularGrowingInitial hγ hγ1 s - littleCircularReference hγ hγ1‖ <
          ‖X (circularGrowingInitial hγ hγ1 s) period - littleCircularReference hγ hγ1‖ := by
  obtain ⟨ρ, hρ, X, hX, hs, hfix, hnear, harea, hfour⟩ :=
    exists_circularContour_constrained_period_flow hγ hγ1 3
  have hp : period ∈ Icc (0 : ℝ) period := ⟨by unfold period; positivity, le_rfl⟩
  have hP : DifferentiableAt ℝ (fun W => X W period) (littleCircularReference hγ hγ1) :=
    ((hs period hp).contDiffAt (isOpen_ball.mem_nhds (mem_ball_self hρ))).differentiableAt
      (by norm_num)
  refine ⟨ρ, hρ, X, hX, hs period hp, hfix, ?_⟩
  have hm : ∀ᶠ s : ℝ in 𝓝[≠] 0, circularGrowingInitial hγ hγ1 s ∈
      ball (littleCircularReference hγ hγ1) ρ :=
    (eventually_circularGrowingInitial_mem_ball hγ hγ1 hρ).filter_mono nhdsWithin_le_nhds
  have ha : ∀ᶠ s : ℝ in 𝓝[≠] 0, ∀ i : Fin 2,
      loopArea (LittleContourSpace.lift γ (circularGrowingInitial hγ hγ1 s i)) =
        Real.pi * circularContourRadii i ^ 2 :=
    (eventually_circularGrowingInitial_area hγ hγ1).filter_mono nhdsWithin_le_nhds
  filter_upwards [hm, ha, eventually_circularGrowingInitial_return_growth hγ hγ1 hρ hX hP hfix]
    with s hmem hinit hgrowth
  have hinit' (i : Fin 2) : littleContourArea γ (circularGrowingInitial hγ hγ1 s i) =
      Real.pi * circularContourRadii i ^ 2 := hinit i
  refine ⟨hmem, hinit', ?_, hgrowth⟩
  intro t ht
  refine ⟨hnear _ hmem t ht, ?_⟩
  intro i
  exact ⟨(harea _ hmem t ht i).trans (hinit' i),
    hfour _ hmem (circularGrowingInitial_fourfold hγ hγ1 s) t ht i⟩

end Euler2D

end
