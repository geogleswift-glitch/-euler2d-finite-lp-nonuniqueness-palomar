module

public import RequestProject.Euler.CircularConstrainedIntervalFlow
public import RequestProject.Euler.BanachFlowGridIteration

@[expose] public section
set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
noncomputable section
open Set Filter Topology Metric
open scoped NNReal ContDiff
namespace Euler2D
local instance (priority := 2000) sameGridLittle_group (γ : ℝ≥0) :
    NormedAddCommGroup (LittleContourSpace γ) := Submodule.normedAddCommGroup (LittleContourSpace γ)
local instance (priority := 2000) sameGridLittle_space (γ : ℝ≥0) :
    NormedSpace ℝ (LittleContourSpace γ) := Submodule.normedSpace (LittleContourSpace γ)
local instance (priority := 2000) sameGridFamily_tower (γ : ℝ≥0) :
    IsScalarTower ℝ ℝ (Fin 2 → LittleContourSpace γ) where
  smul_assoc a b Z := by
    funext i
    change (a * b) • Z i = a • (b • Z i)
    exact (smul_smul a b (Z i)).symm
theorem exists_circular_material_block_of_same_period_flow {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1) {R : ℝ} (hR : 0 < R)
    {X : (Fin 2 → LittleContourSpace γ) → ℝ → Fin 2 → LittleContourSpace γ}
    (hX : IsBanachFlowOn (circularBanachField hγ hγ1) (circularBanachDomain hγ hγ1)
      (ball (littleCircularReference hγ hγ1) R) period X)
    (hd : ContinuousAt (fun W => X W period) (littleCircularReference hγ hγ1))
    (hfix : X (littleCircularReference hγ hγ1) period = littleCircularReference hγ hγ1)
    {m : ℕ} (hm : 0 < m) :
    ∃ δ > 0, ∃ Z : (Fin 2 → LittleContourSpace γ) → ℝ → Fin 2 → LittleContourSpace γ,
      IsBanachFlowOn (circularBanachField hγ hγ1) (circularBanachDomain hγ hγ1)
        (ball (littleCircularReference hγ hγ1) δ) ((m : ℝ) * period) Z ∧
      ∀ b ∈ ball (littleCircularReference hγ hγ1) δ, ∀ n ≤ m,
        Z b ((n : ℝ) * period) = (fun W => X W period)^[n] b := by
  have hp : 0 < period := by unfold period; positivity
  have hT : 0 < (m : ℝ) * period := mul_pos (Nat.cast_pos.mpr hm) hp
  obtain ⟨ρ, hρ, Z, hZ, _⟩ := exists_circularContour_constrained_interval_flow hγ hγ1 3 hT
  have hn : ∀ᶠ b : Fin 2 → LittleContourSpace γ in 𝓝 (littleCircularReference hγ hγ1),
      (∀ n ≤ m, (fun W => X W period)^[n] b ∈ ball (littleCircularReference hγ hγ1) R) ∧
      b ∈ ball (littleCircularReference hγ hγ1) ρ :=
    (eventually_fixedPoint_iterates_mem_ball hd hfix hR m).and (ball_mem_nhds _ hρ)
  obtain ⟨δ, hδ, hδprop⟩ := Metric.eventually_nhds_iff.mp hn
  have hZ' : IsBanachFlowOn (circularBanachField hγ hγ1) (circularBanachDomain hγ hγ1)
      (ball (littleCircularReference hγ hγ1) δ) ((m : ℝ) * period) Z :=
    ⟨fun b hb => hZ.initial b (hδprop hb).2, fun b hb => hZ.continuous b (hδprop hb).2,
      fun b hb => hZ.hasDerivAt b (hδprop hb).2, fun b hb => hZ.mem b (hδprop hb).2⟩
  refine ⟨δ, hδ, Z, hZ', ?_⟩
  intro b hb n hn
  exact banachFlow_grid_eq_iterate (isOpen_phaseAdmissibleLittleContourFamilies _ _)
    (contDiffOn_finiteContourPhaseFieldTotal hγ hγ1 _ _ _ _ _ 1) hp m hX hZ (hδprop hb).2
    (fun j hj => (hδprop hb).1 j hj.le) n hn


end Euler2D
end

