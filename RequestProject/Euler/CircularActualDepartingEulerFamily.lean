module

public import RequestProject.Euler.CircularActualRootVelocityFamily
public import RequestProject.Euler.CircularFlattenedMaterialTransferProfile

/-! The actual captured cascade yields a genuine finite Euler family
with one positive velocity departure at each fixed coupled scale,
uniformly in the cutoff. No unrelated Euler systems are reselected. -/

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 24000000
set_option maxRecDepth 9000

noncomputable section

open Complex Set Filter Topology MeasureTheory Metric
open scoped NNReal ENNReal

namespace Euler2D

attribute [local instance 2000] rigidGaugeLittle_group rigidGaugeLittle_space rigidGaugeFamily_tower
attribute [local instance 2000] captureBlockTangent_group captureBlockTangent_space
  captureBlockTangent_continuousAdd captureBlockEndo_monoid captureBlockTangent_complete
attribute [local instance] LittleContourSpace.complexScalarNormedSpace LittleContourSpace.complexScalarTower
attribute [local instance 2000] valueScalarC1_group valueScalarC1_space
attribute [local instance] ContourC1Space.complexScalarNormedSpace ContourC1Space.complexScalarTower
attribute [local instance 2000] phaseDomainC1_group phaseDomainC1_space
attribute [local irreducible] contourC1GraphSubmodule holderGraphSubmodule circularCoRotationCLM
  circularConstrainedTangentSubmodule circularConstrainedUnstableProjectionCLM
  circularConstrainedReturnMap circularConstrainedChart circularConstraintProjectionToTangentCLM
  circularBanachField circularBanachDomain

namespace CircularMaterialTransferProfile

variable {γ : ℝ≥0} {hγ : 0 < γ} {hγ1 : (γ : ℝ) < 1}
    (P : CircularMaterialTransferProfile hγ hγ1)

theorem exists_actual_departing_Euler_family {Rflow r₀ : ℝ}
    (hRflow : 0 < Rflow) (hr₀ : 0 < r₀)
    {Xflow : (Fin 2 → LittleContourSpace γ) → ℝ → Fin 2 → LittleContourSpace γ}
    (hflow : IsBanachFlowOn (circularBanachField hγ hγ1) (circularBanachDomain hγ hγ1)
      (ball (littleCircularReference hγ hγ1) Rflow) period Xflow)
    (hd : ContDiffAt ℝ 2 (fun W => Xflow W period) (littleCircularReference hγ hγ1))
    (hfix : Xflow (littleCircularReference hγ hγ1) period = littleCircularReference hγ hγ1)
    (harea : ∀ W ∈ ball (littleCircularReference hγ hγ1) Rflow, ∀ i,
      littleContourArea γ (Xflow W period i) = littleContourArea γ (W i))
    {gseq : CircularConstrainedTangentSpace γ → ℕ → CircularConstrainedTangentSpace γ}
    (hg : IsLocalWeightedBackwardGraph
      (banachDoubleReturn (circularConstrainedReturnMap hγ hγ1 (fun W => Xflow W period)))
      (circularConstrainedUnstableProjectionCLM hγ hγ1.le) circularAncientBackwardWeight r₀ gseq)
    (hsamples : ∃ N : ℕ, ∀ n ≥ N, ∃ α : CircularConstrainedTangentSpace γ,
      circularConstrainedUnstableProjectionCLM hγ hγ1.le α = α ∧ ‖α‖ ≤ r₀ / 2 ∧
      P.ancient (-(n : ℝ) * (period + period)) = circularConstrainedChart hγ hγ1 (gseq α 0))
    {q T : ℝ} [Fact (1 ≤ ENNReal.ofReal q)]
    (hq : 0 < q) (hqE : 2 ≤ ENNReal.ofReal q) (hq2 : 2 ≤ q) (hT : 0 < T) :
    ∃ b : ℝ≥0, 0 < b ∧ b < 1 / 4 ∧
      ∀ nMin : ℕ, ∃ n ≥ nMin,
        let s := -(n : ℝ) * (period + period)
        ∃ hs : s ≤ 0, ∃ cA > 0,
          ∀ᶠ ξ : ℝ in atTop,
            P.HasActualRootVelocityDepartureFamilyAt (T := T) hq hqE b s hs cA ξ := by
  obtain ⟨b, hb, hbquarter, ℓ, hℓ, δ, hδ, η, hη, hηa, hηgap, Cb, hCb, m, hm, hfamily⟩ :=
    P.exists_actual_root_innerMoment_family hRflow hr₀ hflow hd hfix harea hg hsamples hq hqE hT
  refine ⟨b, hb, hbquarter, ?_⟩
  intro nMin
  obtain ⟨n, hn, hs, D₀, hD₀, cA, hcA, hmoment⟩ := hfamily nMin
  refine ⟨n, hn, hs, cA, hcA, ?_⟩
  filter_upwards [hmoment, P.eventually_actual_root_velocity_of_innerMoment hq hqE hq2 hT
    hs hcA ℓ b hb hδ hη hηa hCb.le hm] with ξ hξ hupgrade
  exact hupgrade hξ

end CircularMaterialTransferProfile

theorem exists_circular_actual_departing_Euler_family {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1) {q T : ℝ} [Fact (1 ≤ ENNReal.ofReal q)]
    (hq : 0 < q) (hqE : 2 ≤ ENNReal.ofReal q) (hq2 : 2 ≤ q) (hT : 0 < T) :
    ∃ P : CircularMaterialTransferProfile hγ hγ1,
      ∃ b : ℝ≥0, 0 < b ∧ b < 1 / 4 ∧
        ∀ nMin : ℕ, ∃ n ≥ nMin,
          let s := -(n : ℝ) * (period + period)
          ∃ hs : s ≤ 0, ∃ cA > 0,
            ∀ᶠ ξ : ℝ in atTop,
              P.HasActualRootVelocityDepartureFamilyAt (T := T) hq hqE b s hs cA ξ := by
  obtain ⟨P, hflat⟩ := exists_circularMaterialTransferProfile_with_flattenedGraph hγ hγ1
  obtain ⟨Rflow, hRflow, Y, hY, hd, hfix, harea, r₀, hr₀, gseq, hg,
    Cflat, hCflat, sflat, hsflat, hsr, hbounds, hsamples⟩ := hflat
  exact ⟨P, P.exists_actual_departing_Euler_family hRflow hr₀ hY hd hfix harea hg hsamples
    hq hqE hq2 hT⟩

end Euler2D

end
