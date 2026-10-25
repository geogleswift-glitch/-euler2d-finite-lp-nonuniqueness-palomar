module

public import RequestProject.Euler.CircularActualCapturedInnerMoment
public import RequestProject.Euler.CircularActualUniformCapturedCascade

public import RequestProject.Euler.CircularActualCapturedChildNextParent
public import RequestProject.Euler.CircularActualWarmupCaptureHandoff

public import RequestProject.Euler.CircularCoupledSharedSourceReadyFamily

public import RequestProject.Euler.CircularCoupledSelectedFirstParentWholePastMomentFamily

public import RequestProject.Euler.CircularCoupledCommonHistorySourceReady

public import RequestProject.Euler.CircularActualParentWholePastMoment
public import RequestProject.Euler.CircularCoupledSelectedFirstParentWholePastFamily

public import RequestProject.Euler.CircularActualParentWholePastHistory
public import RequestProject.Euler.CircularCoupledSelectedFirstParentLookbackFamily

public import RequestProject.Euler.CircularActualParentMatchedLookbackCapture
public import RequestProject.Euler.CircularCoupledSelectedFirstParentMatchedFamily

public import RequestProject.Euler.CircularActualParentMatchedCapture
public import RequestProject.Euler.CircularCoupledParentCaptureTargetRadiusBudget

public import RequestProject.Euler.CircularCoupledSelectedFirstParentSourceBudget
public import RequestProject.Euler.CircularActualCoupledParentCapture

/-! The real selected first-transfer family reaches a genuine parent
capture on its SAME Euler system. The old child, parent, literal history,
selected target and radius cap are retained in a joint witness. -/

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 96000000
set_option maxRecDepth 9500

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
attribute [local irreducible] contourC1GraphSubmodule holderGraphSubmodule circularCoRotationCLM
  circularConstrainedTangentSubmodule circularConstrainedUnstableProjectionCLM
  circularConstrainedReturnMap circularConstrainedChart circularConstraintProjectionToTangentCLM
  circularBanachField circularBanachDomain

namespace CircularMaterialTransferProfile

variable {γ : ℝ≥0} {hγ : 0 < γ} {hγ1 : (γ : ℝ) < 1}
    (P : CircularMaterialTransferProfile hγ hγ1)



def HasActualRootInnerMomentFamilyAt {q T : ℝ} [Fact (1 ≤ ENNReal.ofReal q)]
    (hq : 0 < q) (hqE : 2 ≤ ENNReal.ofReal q)
    (ℓcap : ℕ) (δ η Cb D₀ m : ℝ)
    (b : ℝ≥0) (s : ℝ) (hs : s ≤ 0) (cA ξ : ℝ) : Prop :=
  let ρ := Real.exp (-ξ)
  let hρ := Real.exp_pos (-ξ)
  let R := ρ ^ 10
  let hR := pow_pos hρ 10
  let A₀ := cA * (1 + ξ)
  ρ ≤ 1 / 2 ∧ ρ ^ 2 < (b : ℝ) ^ q ∧
  ∀ N : ℕ, 0 < N →
    let f := finiteBaseCurlL2 (A₀ := A₀) (b := (b : ℝ)) (ρ := ρ) hR hρ hq hqE
      (P.finiteBaseLp (A₀ := A₀) (b := (b : ℝ)) (ρ := ρ) (q := q) hs hR hρ) N
    ∃ S : BoundedEulerParticleSystem f T,
      IsFourfoldBoundedEulerParticleSystem S ∧
      IsWeakEulerSolution T (biotSavartL2 f) (particleVelocity f S.backward S.backward_area) ∧
      (∀ t ∈ Icc (0 : ℝ) T, MeasurePreserving (S.forward t) volume volume ∧
        MeasurePreserving (S.backward t) volume volume) ∧
      P.HasActualCapturedInnerMomentSection (s := s) (A₀ := A₀) (b := (b : ℝ))
        hR hρ (Nat.zero_le N) S ℓcap δ η Cb D₀ ξ m

theorem exists_actual_root_innerMoment_family {Rflow r₀ : ℝ}
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
    (hq : 0 < q) (hqE : 2 ≤ ENNReal.ofReal q) (hT : 0 < T) :
    ∃ b : ℝ≥0, 0 < b ∧ b < 1 / 4 ∧ ∃ ℓcap : ℕ, 0 < ℓcap ∧
      ∃ δ > 0, ∃ η > 0, η ≤ cellA / 16 ∧ η ≤ (1 - cellA) / 16 ∧ ∃ Cb > 0, ∃ m > 0,
      ∀ nMin : ℕ, ∃ n ≥ nMin,
        let s := -(n : ℝ) * (period + period)
        ∃ hs : s ≤ 0, ∃ D₀ > 0, ∃ cA > 0,
        ∀ᶠ ξ : ℝ in atTop,
          P.HasActualRootInnerMomentFamilyAt (T := T) hq hqE ℓcap δ η Cb D₀ m b s hs cA ξ := by
  obtain ⟨δmoment, hδmoment, m, hm, hMomentAll⟩ :=
    P.exists_uniform_actualCaptured_innerMoment hRflow hr₀ hflow hd hfix harea hg
  obtain ⟨Cmoment, hCmoment, b, hb, hbquarter, hnonzero, hslow,
    η, hη, hηa, hηgap, Cpre, hCpre, δ, hδ, hδbound, sCanon, hsCanon, hcanonδ,
    εtarget, hεtarget, Ctarget, hCtarget, htarget,
    Henv, hHenv, Chistory, hChistory, Lback, hLback, Dobs, hDobs, hLobs,
    κ, hκ, hresponse, hLead, hTail, ℓwarm, hℓwarm, qcwarm, hqc, hqgap,
    Ccomp, hCcomp, hready, nwarm, hnwarm, hDpre, hCone,
    ℓcap, hℓcap, Hcap, hHcap, Cb, hCb, hTargetRadius, hfamily⟩ :=
      P.exists_actual_uniform_captured_cascade_family hRflow hr₀ hflow hd hfix harea hg hsamples
        hq hqE hT δmoment 0 hδmoment (by norm_num)
  have hAncientEv := P.ancient_samples_tendsto.eventually
    (Metric.ball_mem_nhds (littleCircularReference hγ hγ1) hη)
  obtain ⟨nη, hnη⟩ := eventually_atTop.mp hAncientEv
  refine ⟨b, hb, hbquarter, ℓcap, hℓcap, δ, hδ, η, hη, hηa, hηgap, Cb, hCb, m, hm, ?_⟩
  intro nMin
  obtain ⟨n, hn, hdata⟩ := hfamily 1 (by norm_num) (max nMin nη)
  dsimp only at hdata
  obtain ⟨hs, D, hD, Cmatch, hCmatch, Cback, hCback, Ccur, hCcur, Cobs, hCobs,
    hseed, hterminal, D₀, hD₀, Cgraph, hCgraph, CbackParent, hCbackParent,
    Lentry, hLentry, Dentry, hDentry, hClockMargin, cA, hcA, hTimeBase, hDobsD, hfamilyEv⟩ := hdata
  let s := -(n : ℝ) * (period + period)
  have hAncientNorm : ‖P.ancient s - littleCircularReference hγ hγ1‖ < η := by
    simpa only [mem_ball, dist_eq_norm] using hnη n ((le_max_right nMin nη).trans hn)
  have hancient (i : Fin 2) : ‖(P.ancient s i).val - circularReferenceC1 hγ hγ1 i‖ ≤ η :=
    (norm_le_pi_norm (P.ancient s - littleCircularReference hγ hγ1) i).trans hAncientNorm.le
  have hηquarter : η ≤ cellA / 4 := hηa.trans (by linarith only [cellA_pos])
  have hMomentEv := hMomentAll b hb δ sCanon εtarget Ctarget η Hcap Cgraph ℓcap
    hℓcap hδ hδbound hη hηquarter hHcap hCgraph.le htarget hTargetRadius
    hs hcA hT hq hqE hancient Cb D₀ Lback CbackParent Cmoment
  refine ⟨n, (le_max_left nMin nη).trans hn, hs, D₀, hD₀, cA, hcA, ?_⟩
  filter_upwards [hfamilyEv, hMomentEv] with ξ hfamilyξ hMomentξ
  dsimp only [HasActualUniformCapturedCascadeFamilyAt, HasActualRootInnerMomentFamilyAt] at hfamilyξ ⊢
  obtain ⟨hhalf, hlp, hfinite⟩ := hfamilyξ
  refine ⟨hhalf, hlp, ?_⟩
  intro N hN
  obtain ⟨S, hS, hweak, hareaS, hall⟩ := hfinite N hN
  have hroot := hall 0 hN
  obtain ⟨entrance, he, hClock, Ypast, hcap⟩ := hroot
  exact ⟨S, hS, hweak, hareaS, hMomentξ N 0 (Nat.zero_le N) S hS entrance he Ypast hcap⟩

end CircularMaterialTransferProfile
end Euler2D

end
