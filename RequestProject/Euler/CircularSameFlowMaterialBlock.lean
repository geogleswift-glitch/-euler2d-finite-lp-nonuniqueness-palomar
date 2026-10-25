module

public import RequestProject.Euler.CircularSameFlowMaterialGrid
public import RequestProject.Euler.CircularConstrainedReturnConjugacy
public import RequestProject.Euler.LocalConjugacyIterates
public import RequestProject.Euler.CircularChartEndpointRecovery

@[expose] public section
set_option maxHeartbeats 8000000
set_option maxRecDepth 4000

noncomputable section
open Set Filter Topology Metric
open scoped NNReal ContDiff
namespace Euler2D
attribute [local instance 2000] returnConjugacyLittle_group returnConjugacyLittle_space
  returnConjugacyFamily_tower returnConjugacyTangent_group returnConjugacyTangent_space
  returnConjugacyTangent_continuousAdd
attribute [local irreducible] circularConstrainedTangentSubmodule
  circularConstrainedReturnMap circularConstrainedChart circularConstraintProjectionToTangentCLM

theorem exists_circular_sameFlow_material_block_return {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1) {R : ℝ} (hR : 0 < R)
    {X : (Fin 2 → LittleContourSpace γ) → ℝ → Fin 2 → LittleContourSpace γ}
    (hX : IsBanachFlowOn (circularBanachField hγ hγ1) (circularBanachDomain hγ hγ1)
      (ball (littleCircularReference hγ hγ1) R) period X)
    (hd : ContDiffAt ℝ 2 (fun W => X W period) (littleCircularReference hγ hγ1))
    (hfix : X (littleCircularReference hγ hγ1) period = littleCircularReference hγ hγ1)
    (harea : ∀ W ∈ ball (littleCircularReference hγ hγ1) R, ∀ i,
      littleContourArea γ (X W period i) = littleContourArea γ (W i))
    {m : ℕ} (hm : 0 < m) :
    ∃ δ > 0, ∃ Z : (Fin 2 → LittleContourSpace γ) → ℝ → Fin 2 → LittleContourSpace γ,
      IsBanachFlowOn (circularBanachField hγ hγ1) (circularBanachDomain hγ hγ1)
        (ball (littleCircularReference hγ hγ1) δ) ((m : ℝ) * period) Z ∧
      ∀ᶠ v : CircularConstrainedTangentSpace γ in 𝓝 0,
        circularConstrainedReturnMap hγ hγ1 (fun W => Z W ((m : ℝ) * period)) v =
          (circularConstrainedReturnMap hγ hγ1 (fun W => X W period))^[m] v := by
  obtain ⟨δ, hδ, Z, hZ, hgrid⟩ :=
    exists_circular_material_block_of_same_period_flow hγ hγ1 hR hX hd.continuousAt hfix hm
  let F := circularConstrainedReturnMap hγ hγ1 (fun W => X W period)
  let Φ := circularConstrainedChart hγ hγ1
  have hF0 : F 0 = 0 := circularConstrainedReturnMap_zero hγ hγ1 _ hfix
  have hF : ContDiffAt ℝ 1 F 0 := contDiffAt_circularConstrainedReturnMap hγ hγ1 1 (hd.of_le (by norm_num))
  have hp : period ∈ Icc (0 : ℝ) period := ⟨by unfold period; positivity, le_rfl⟩
  have hconj : ∀ᶠ v : CircularConstrainedTangentSpace γ in 𝓝 0,
      Φ (F v) = X (Φ v) period :=
    eventually_circularConstrainedReturnMap_conjugacy hγ hγ1 hR hd.continuousAt hfix harea
      (fun W hW hfour i => circularBanachFlow_fourfold hγ hγ1 hX hW hfour hp i)
  have hiter := eventually_conjugacy_iterates (G := fun W => X W period) Φ hF0 hF hconj m
  have hinput : ∀ᶠ v : CircularConstrainedTangentSpace γ in 𝓝 0,
      Φ v ∈ ball (littleCircularReference hγ hγ1) δ :=
    (hasFDerivAt_circularConstrainedChart_zero hγ hγ1).continuousAt
      (by rw [circularConstrainedChart_zero]; exact ball_mem_nhds _ hδ)
  refine ⟨δ, hδ, Z, hZ, ?_⟩
  filter_upwards [hiter, hinput] with v hv hin
  have he : Φ (F^[m] v) = Z (Φ v) ((m : ℝ) * period) :=
    hv.trans (hgrid (Φ v) hin m le_rfl).symm
  exact circularConstrainedReturnMap_of_chart_endpoint hγ hγ1
    (fun W => Z W ((m : ℝ) * period)) v (F^[m] v) he.symm

end Euler2D

end


