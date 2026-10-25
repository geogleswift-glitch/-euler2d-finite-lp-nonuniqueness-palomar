module

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


def HasActualUniformCapturedState
    (gseq : CircularConstrainedTangentSpace γ → ℕ → CircularConstrainedTangentSpace γ)
    {s A₀ b R ρ T : ℝ} (hR : 0 < R) (hρ : 0 < ρ)
    {N k : ℕ} (hkN : k ≤ N) {f : Lp ℝ 2 μT}
    (S : BoundedEulerParticleSystem f T)
    (ℓcap : ℕ) (δ η Hcap Cbcap D₀ Cgraph ξ sCanon Ctarget Lback Cback Cmoment Lentry Dentry : ℝ) : Prop :=
  ∃ e : ℝ, 0 ≤ e ∧ ampScale A₀ b k * e ≤ Lentry * ξ + Dentry ∧
    ∃ Y : ℝ → FiniteCircularIndex k → LittleContourSpace γ,
      P.HasActualParentNextHandoffCaptureExtension gseq (s := s) (A₀ := A₀) (b := b)
        hR hρ hkN S e Y ℓcap δ η Hcap Cbcap D₀ Cgraph ξ sCanon Ctarget Lback Cback Cmoment

def HasActualUniformCapturedCascadeFamilyAt {q T : ℝ} [Fact (1 ≤ ENNReal.ofReal q)]
    (hq : 0 < q) (hqE : 2 ≤ ENNReal.ofReal q)
    (gseq : CircularConstrainedTangentSpace γ → ℕ → CircularConstrainedTangentSpace γ)
    (ℓcap : ℕ) (Hcap Cbcap D₀ Cgraph Cback Cmoment : ℝ)
    (b : ℝ≥0) (s : ℝ) (hs : s ≤ 0) (cA δ sCanon Ctarget η Lback Lentry Dentry ξ : ℝ) : Prop :=
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
      ∀ k : ℕ, ∀ hk : k < N,
        P.HasActualUniformCapturedState gseq (s := s) (A₀ := A₀) (b := (b : ℝ))
          hR hρ (Nat.le_of_lt hk) S ℓcap δ η Hcap Cbcap D₀ Cgraph ξ sCanon Ctarget
          Lback Cback Cmoment Lentry Dentry

theorem exists_actual_uniform_captured_cascade_family {Rflow r₀ : ℝ}
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
    (hq : 0 < q) (hqE : 2 ≤ ENNReal.ofReal q) (hT : 0 < T)
    (δmax Kextra : ℝ) (hδmax : 0 < δmax) (hKextra : 0 ≤ Kextra) :
    ∃ CmomentParent > 0, ∃ b : ℝ≥0, 0 < b ∧ b < 1 / 4 ∧
      bilateral P.moment (((b : ℝ) : ℂ) * (sigma + 5 / 4 * I)) ≠ 0 ∧
      (b : ℝ) * Kextra + (b : ℝ) *
        (finiteInnerLabelLittleRowCoefficient (γ : ℝ) (cellA / 2)
          (circularCanonicalCellNormBudget hγ hγ1) / (2 - 1)) < sigma / 4 ∧
      ∃ ηctrl > 0, ηctrl ≤ cellA / 16 ∧ ηctrl ≤ (1 - cellA) / 16 ∧ ∃ Cpre > 0, ∃ δ > 0, δ < δmax ∧ ∃ sCanon < 0,
      ‖P.coRotatedAncientGraphBase sCanon‖ = δ ∧
      ∃ εtarget > 0, ∃ Ctarget > 0,
      P.IsSelectedCanonicalCaptureTarget gseq δ sCanon εtarget Ctarget ∧
      ∃ Henv > 0, ∃ Chistory > 0, ∃ Lback > 0, ∃ Dobs > 0, Lback < Dobs ∧
      ∃ κ > 0,
        ‖retardedSol (((b : ℝ) : ℂ) * lamStar)
          (((b : ℝ) : ℂ) * (sigma + 5 / 4 * I)) Kstar P.moment (Dobs - Lback + sCanon)‖ = 2 * κ ∧
        (((‖Kstar‖ * max Chistory CmomentParent * ηctrl) / (sigma / 2 - (b : ℝ) * sigma) *
          Real.exp ((b : ℝ) * sigma * ((Dobs - Lback + sCanon) - sCanon))) *
            Real.exp (-(sigma / 2 - (b : ℝ) * sigma) * Lback) ≤ κ / 4) ∧
        (∀ ρ : ℝ, 0 ≤ ρ →
          ‖retardedSol (((b : ℝ) : ℂ) * lamStar) (((b : ℝ) : ℂ) * (sigma + 5 / 4 * I))
            ((ρ : ℂ) ^ 6 * Kstar) P.moment (sCanon - Lback)‖ *
              Real.exp ((b : ℝ) * sigma * (Lback + ((Dobs - Lback + sCanon) - sCanon))) ≤ (κ / 4) * ρ ^ 6) ∧
      ∃ ℓwarm : ℕ, 0 < ℓwarm ∧ ∃ qcwarm : ℝ, 1 < qcwarm ∧
      qcwarm ^ 2 < circularCaptureBlockMultiplier ℓwarm ∧ ∃ Ccomp > 0,
      P.ActualCanonicalCaptureReadyWitness gseq b ℓwarm qcwarm Ccomp Cpre ∧
      ∃ nwarm : ℕ, 0 < nwarm ∧ (b : ℝ) * Dobs = (nwarm : ℝ) * circularCaptureBlockTime ℓwarm ∧
      Ccomp * qcwarm ^ nwarm ≤ (κ * ‖circularConstrainedUnstableEmbeddingCLM hγ hγ1.le 1‖) / 32 ∧
      ∃ ℓcap : ℕ, 0 < ℓcap ∧ ∃ Hcap > 0, ∃ Cbcap > 0,
      (Hcap * (4 * circularCaptureBlockMultiplier ℓcap / 3)) * δ < εtarget ∧
      ∀ seedMax > 0, ∀ nMin : ℕ, ∃ n ≥ nMin,
        let s := -(n : ℝ) * (period + period)
        ∃ hs : s ≤ 0, ∃ D > 0, ∃ Cmatch : ℝ, 0 < Cmatch ∧ ∃ Cback : ℝ, 0 < Cback ∧
        ∃ Ccur : ℝ, 0 < Ccur ∧ ∃ Cobs : ℝ, 0 < Cobs ∧
          ‖circularConstrainedUnstableProjectionCLM hγ hγ1.le
            (circularConstraintProjectionToTangentCLM hγ hγ1.le
              (P.ancient s - littleCircularReference hγ hγ1))‖ < seedMax ∧
          Henv * ‖circularConstrainedUnstableProjectionCLM hγ hγ1.le
            (circularConstraintProjectionToTangentCLM hγ hγ1.le
              (P.ancient s - littleCircularReference hγ hγ1))‖ * Real.exp (sigma * D) ≤ ηctrl ∧
          ∃ D₀ > 0, ∃ Cgraph > 0, ∃ CbackParent > 0, ∃ Lentry ≥ 0, ∃ Dentry ≥ 0,
          sigma * (Lentry + 6 / sigma) < 8 ∧ ∃ cA > 0, D / cA < T ∧ Dobs < D ∧
          ∀ᶠ ξ : ℝ in atTop,
            P.HasActualUniformCapturedCascadeFamilyAt (T := T) hq hqE gseq
              ℓcap Hcap Cbcap D₀ Cgraph CbackParent CmomentParent b s hs cA δ sCanon Ctarget
              ηctrl Lback Lentry Dentry ξ := by
  obtain ⟨Kself, hKself, Cr, hCr, Cd, hCd, F, hF, ηctrl, hηctrl, hηa, hηgap,
    δcapture, hδcapture, ℓcap, hℓcap, Hcap, hHcap, hparent⟩ :=
    P.exists_uniform_actualCoupled_parent_capture_of_warmup hRflow hr₀ hflow hd hfix harea hg
  obtain ⟨Knext, hKnext, hnextAll⟩ := P.exists_actualCapturedChild_next_parent_warmup_setup
  have hηquarter : ηctrl ≤ cellA / 4 := hηa.trans (by linarith only [cellA_pos])
  obtain ⟨CmomentParent, hCmomentParent, hUpgradeAll⟩ :=
    P.exists_uniform_actualWarmup_capture_handoff_upgrade gseq hηctrl hηquarter
  let targetFactor := Hcap * (4 * circularCaptureBlockMultiplier ℓcap / 3)
  have hTargetFactor : 0 ≤ targetFactor := by
    dsimp only [targetFactor]
    rw [circularCaptureBlockMultiplier_eq_exp]
    positivity
  let Ksum := Kextra + (Kself : ℝ) + (Knext : ℝ)
  let δbound := min δmax δcapture
  have hKsum : 0 ≤ Ksum := add_nonneg (add_nonneg hKextra (NNReal.coe_nonneg Kself)) (NNReal.coe_nonneg Knext)
  have hδbound : 0 < δbound := lt_min hδmax hδcapture
  obtain ⟨b, hb, hbquarter, hnonzero, hslowSum, Cpre, hCpre, δ, hδ, hδboundδ,
    sCanon, hsCanon, hcanonδ, εtarget, hεtarget, Ctarget, hCtarget, htarget, hTargetRadius,
    Henv, hHenv, Chistory, hChistory, c, hc, Lback, hLback, tmin, htmin,
    ℓpre, hℓpre, qc, hqc, hqgap, Ccomp, hCcomp, hwitness, hfamily⟩ :=
    P.exists_actual_coupled_shared_sourceReady_family
      hRflow hr₀ hflow hd hfix harea hg hsamples hq hqE hT hCr hCd.le hF.le
      (by norm_num : (0 : ℝ) ≤ 1) targetFactor hTargetFactor CmomentParent hCmomentParent.le δbound ηctrl Ksum hδbound hηctrl hKsum hηa hηgap
  have hbR : 0 < (b : ℝ) := hb
  have hb1 : b < 1 := hbquarter.trans (by norm_num)
  have hδmaxδ : δ < δmax := hδboundδ.trans_le (min_le_left _ _)
  have hδcapδ : δ < δcapture := hδboundδ.trans_le (min_le_right _ _)
  have hslowExtra : (b : ℝ) * Kextra + (b : ℝ) *
      (finiteInnerLabelLittleRowCoefficient (γ : ℝ) (cellA / 2)
        (circularCanonicalCellNormBudget hγ hγ1) / (2 - 1)) < sigma / 4 := by
    have hh := mul_nonneg hbR.le (NNReal.coe_nonneg Kself)
    have hhNext := mul_nonneg hbR.le (NNReal.coe_nonneg Knext)
    dsimp only [Ksum] at hslowSum
    nlinarith only [hslowSum, hh, hhNext]
  have hslowParent : (b : ℝ) * Kself + (b : ℝ) *
      (finiteInnerLabelLittleRowCoefficient (γ : ℝ) (cellA / 2)
        (circularCanonicalCellNormBudget hγ hγ1) / (2 - 1)) < sigma / 4 := by
    have hh := mul_nonneg hbR.le hKextra
    have hhNext := mul_nonneg hbR.le (NNReal.coe_nonneg Knext)
    dsimp only [Ksum] at hslowSum
    nlinarith only [hslowSum, hh, hhNext]
  have hslowNext : (b : ℝ) * Knext + (b : ℝ) *
      (finiteInnerLabelLittleRowCoefficient (γ : ℝ) (cellA / 2)
        (circularCanonicalCellNormBudget hγ hγ1) / (2 - 1)) < sigma / 4 := by
    have hhExtra := mul_nonneg hbR.le hKextra
    have hhParent := mul_nonneg hbR.le (NNReal.coe_nonneg Kself)
    dsimp only [Ksum] at hslowSum
    nlinarith only [hslowSum, hhExtra, hhParent]
  obtain ⟨nWarm, hnWarmMin, hnWarm, hstar, hDobs, hLobs, κ, hκ, hκlower,
    hconeBudget, hresponseEq, hcommonLead, hcommonTail, hsource, hdata⟩ := hfamily 0
  let Dobs := (nWarm : ℝ) * circularCaptureBlockTime ℓpre / (b : ℝ)
  let Dpre := (b : ℝ) * Dobs
  let Cw := Cpre * (1 + Dpre)
  let Cbcap := radialStageRadiusConstant Cr Cw b
  have hDpre : 0 ≤ Dpre := mul_nonneg hbR.le hDobs.le
  have hCw : 0 ≤ Cw := mul_nonneg hCpre.le (by linarith only [hDpre])
  have hCbcap : 0 < Cbcap := radialStageRadiusConstant_pos hCr hCw hbR hb1
  have hDpreEq : Dpre = (nWarm : ℝ) * circularCaptureBlockTime ℓpre := by
    dsimp only [Dpre, Dobs]
    field_simp [hbR.ne']
  have hsourceReady : F * (finiteCurrentPolynomialForcingCoefficient (γ : ℝ) (cellA / 2)
      (circularCanonicalCellNormBudget hγ hγ1) Cbcap b Cd + 1) ≤
      (κ * ‖circularConstrainedUnstableEmbeddingCLM hγ hγ1.le 1‖) / 32 := by
    dsimp only [Cbcap, Cw]
    rw [hDpreEq]
    exact hsource
  obtain ⟨CcurNext, hCcurNext, CobsNext, hCobsNext, hStepAll⟩ :=
    hnextAll b hb hbquarter hslowNext hDobs hηctrl hηa hηgap
  refine ⟨CmomentParent, hCmomentParent, b, hb, hbquarter, hnonzero, hslowExtra, ηctrl, hηctrl, hηa, hηgap, Cpre, hCpre,
    δ, hδ, hδmaxδ, sCanon, hsCanon, hcanonδ, εtarget, hεtarget, Ctarget, hCtarget,
    htarget, Henv, hHenv, Chistory, hChistory, Lback, hLback, Dobs, hDobs, hLobs,
    κ, hκ, hresponseEq, hcommonLead, hcommonTail, ℓpre, hℓpre, qc, hqc, hqgap, Ccomp, hCcomp, hwitness, nWarm, hnWarm, hDpreEq, hconeBudget, ℓcap, hℓcap, Hcap, hHcap, Cbcap, hCbcap, hTargetRadius, ?_⟩
  intro seedMax hseedMax nMin
  obtain ⟨n, hn, hdataN⟩ := hdata seedMax hseedMax nMin
  dsimp only at hdataN
  obtain ⟨hs, D, hD, Cmatch, hCmatch, Cback, hCback, CcurFirst, hCcurFirst,
    CobsFirst, hCobsFirst, hseed, hterminal, hDobsD, hfamilyEv⟩ := hdataN
  let s := -(n : ℝ) * (period + period)
  let cA₀ := 2 * (D + 1) / T
  have hcA₀ : 0 < cA₀ := div_pos (by linarith only [hD]) hT
  have htime₀ : D / cA₀ < T := by
    apply (div_lt_iff₀ hcA₀).mpr
    have heq : T * cA₀ = 2 * (D + 1) := by dsimp only [cA₀]; field_simp
    rw [heq]
    linarith only [hD]
  have hancient : ∀ i, ‖(P.ancient s i).val - circularReferenceC1 hγ hγ1 i‖ ≤ ηctrl := by
    obtain ⟨ξ₀, hfamily₀⟩ := (hfamilyEv cA₀ hcA₀ htime₀).exists
    exact P.actualCoupledFirstCaptureConeFamily_initial_ancient_bound hq hqE gseq b s hs
      cA₀ D δ sCanon ηctrl Lback Dobs Henv Chistory Cmatch Cback Cpre CcurFirst CobsFirst κ ξ₀ hD.le hfamily₀
  let Ccur := max CcurFirst CcurNext
  let Cobs := max CobsFirst CobsNext
  have hCcur : 0 < Ccur := hCcurFirst.trans_le (le_max_left _ _)
  have hCobs : 0 < Cobs := hCobsFirst.trans_le (le_max_left _ _)
  obtain ⟨D₀, hD₀, Cgraph, hCgraph, hcaptured⟩ :=
    hparent b hb hbquarter hslowParent Cpre Dpre Cobs Ccur κ δ
      hCpre.le hDpre hCobs.le hCcur.le hκ hδ hδcapδ hsourceReady
  have hηquarter : ηctrl ≤ cellA / 4 := hηa.trans (by linarith only [cellA_pos])

  let Lentry := (6 / sigma) * ((b : ℝ) / (1 - (b : ℝ)))
  let Dentry := (b : ℝ) * D + (Dpre + (b : ℝ) * D₀) / (1 - (b : ℝ))
  have hb1R : (b : ℝ) < 1 := hb1
  have hgap : 0 < 1 - (b : ℝ) := sub_pos.mpr hb1R
  have hLentry : 0 ≤ Lentry := mul_nonneg (div_nonneg (by norm_num) sigma_pos.le)
    (div_nonneg hbR.le hgap.le)
  have hDentry : 0 ≤ Dentry := add_nonneg (mul_nonneg hbR.le hD.le)
    (div_nonneg (add_nonneg hDpre (mul_nonneg hbR.le hD₀.le)) hgap.le)
  have hSlopeEq : Lentry + 6 / sigma = (6 / sigma) / (1 - (b : ℝ)) := by
    dsimp only [Lentry]
    field_simp [sigma_pos.ne', hgap.ne'] <;> ring
  have hClockMargin : sigma * (Lentry + 6 / sigma) < 8 := by
    rw [hSlopeEq]
    exact (circularCapture_cascade_clock_log_margin hbR (show (b : ℝ) < 1 / 4 from hbquarter)).2
  have hLrec : (b : ℝ) * (Lentry + 6 / sigma) ≤ Lentry := by
    apply le_of_eq
    dsimp only [Lentry]
    field_simp [sigma_pos.ne', hgap.ne'] <;> ring
  have hDrec : (b : ℝ) * (Dentry + D₀) + Dpre ≤ Dentry := by
    have hid : Dentry - ((b : ℝ) * (Dentry + D₀) + Dpre) = (b : ℝ) * (1 - (b : ℝ)) * D := by
      dsimp only [Dentry]
      field_simp [hgap.ne'] <;> ring
    have hnonneg : 0 ≤ (b : ℝ) * (1 - (b : ℝ)) * D := by positivity
    linarith only [hid, hnonneg]
  have hDpreBound : Dpre ≤ (Dpre + (b : ℝ) * D₀) / (1 - (b : ℝ)) := by
    apply (le_div_iff₀ hgap).mpr
    nlinarith only [mul_nonneg hbR.le hDpre, mul_nonneg hbR.le hD₀.le]
  have hDentryFirst : (b : ℝ) * (D + Dobs) ≤ Dentry := by
    calc
      _ = (b : ℝ) * D + Dpre := by dsimp only [Dpre]; ring
      _ ≤ _ := add_le_add le_rfl hDpreBound
  obtain ⟨CbackParent, hCbackParent, hUpgrade⟩ := hUpgradeAll b hb hb1.le
    (Dpre := Dpre) (Cpre := Cpre) (Ccur := Ccur) (Cobs := Cobs) (D₀ := D₀)
    (Lentry := Lentry) (Dentry := Dentry)
    hDpre hCpre.le hCcur.le hCobs.le hδ hsCanon.le hCtarget.le hHcap hCbcap.le hCgraph.le
    hLback hℓcap htarget hTargetRadius hClockMargin
  obtain ⟨cA, hcA, hTimeBase, hcaptureEv⟩ :=
    hcaptured D Lentry Dentry hD.le hLentry hDentry hs hq hqE hT hancient
  have hUpgradeEv := hUpgrade hs hcA hq hqE hT hancient
  have hdiff : (Dobs - Lback + sCanon) - sCanon = Dobs - Lback := by ring
  have hStepEv := hStepAll gseq ℓpre qc Ccomp Cpre nWarm hwitness
    (sCanon := sCanon) (Lback := Lback) (d := Dobs - Lback)
    (Ccommon := max Chistory CmomentParent) (Cmoment := CmomentParent) (Cback := CbackParent)
    (κ := κ) (tstar := Dobs - Lback + sCanon) (Lentry := Lentry) (Dentry := Dentry) (D₀ := D₀)
    (by ring) hsCanon hLback (sub_pos.mpr hLobs) hκ
    (hChistory.le.trans (le_max_left _ _)) (le_max_right _ _) hClockMargin hLrec hDrec
    hDpreEq hconeBudget hresponseEq (by ring)
    (by simpa only [Dobs, add_sub_cancel_right] using hcommonLead)
    (by simpa only [Dobs, add_sub_cancel_right] using hcommonTail)
    hs hcA hq hqE hT hancient
  refine ⟨n, hn, hs, D, hD, Cmatch, hCmatch, Cback, hCback, Ccur, hCcur, Cobs, hCobs,
    hseed, hterminal, D₀, hD₀, Cgraph, hCgraph, CbackParent, hCbackParent,
    Lentry, hLentry, Dentry, hDentry, hClockMargin, cA, hcA, hTimeBase, hDobsD, ?_⟩
  filter_upwards [hfamilyEv cA hcA hTimeBase, hcaptureEv, hUpgradeEv, hStepEv,
    eventually_ge_atTop (1 : ℝ)] with ξ hfamilyξ hcaptureξ hUpgradeξ hStepξ hξOne
  have hξ : 0 ≤ ξ := (by norm_num : (0 : ℝ) ≤ 1).trans hξOne
  let ρ := Real.exp (-ξ)
  let R := ρ ^ 10
  let A₀ := cA * (1 + ξ)
  let h := 2 * ρ ^ 6
  have hρ : 0 < ρ := Real.exp_pos (-ξ)
  have hR : 0 < R := pow_pos hρ 10
  have hA : 0 < A₀ := mul_pos hcA (by linarith only [hξ])
  have hh : 0 ≤ h := by dsimp only [h]; positivity
  dsimp only [HasActualCoupledFirstCaptureConeFamilyAt, HasActualUniformCapturedCascadeFamilyAt] at hfamilyξ ⊢
  obtain ⟨hhalf, hlp, hfinite⟩ := hfamilyξ
  refine ⟨hhalf, hlp, ?_⟩
  intro N hN
  cases N with
  | zero => omega
  | succ k =>
    obtain ⟨htimeN, S, hS, hweak, hareaS, X, hX, hweighted, hcur, hforward,
      τ, hτ, hlong, angle, hvalue, hbefore, hhistory, hmomentHistory, hmatch, hback,
      Y, hY, hlower, hcone, hweightedY, hcurY, hparticlesY, hparticlesPast, hpast⟩ :=
        hfinite (k + 1) (Nat.succ_pos k)
    refine ⟨S, hS, hweak, hareaS, ?_⟩
    have hRecapture : ∀ j : ℕ, ∀ hjN : j ≤ k + 1,
        P.HasActualUniformParentWarmupState gseq (s := s) (A₀ := A₀) (b := (b : ℝ))
          hR hρ hjN S Dpre Cpre Ccur Cobs κ Lentry Dentry ξ →
        P.HasActualUniformCapturedState gseq (s := s) (A₀ := A₀) (b := (b : ℝ))
          hR hρ hjN S ℓcap δ ηctrl Hcap Cbcap D₀ Cgraph ξ sCanon Ctarget Lback
            CbackParent CmomentParent Lentry Dentry := by
      intro j hjN hwarm
      obtain ⟨a, ha, hEnd, hEntryClock, W, hW, hGrowing, hCone, hWeighted, hCur,
        hParticles, hParticlesPast, hPast⟩ := hwarm
      let H := a + Dpre / ampScale A₀ b j
      have hAmp : 0 < ampScale A₀ b j := div_pos hA (pow_pos hbR j)
      have hH : 0 ≤ H := add_nonneg ha (div_nonneg hDpre hAmp.le)
      have hClock : ampScale A₀ b j * H = ampScale A₀ b j * a + Dpre := by
        dsimp only [H]
        rw [mul_add, mul_div_cancel₀ Dpre hAmp.ne']
      have hGrowingAt : κ * ρ ^ 6 ≤ ‖canonicalPrefixMaterialGrowingCoordinate hγ hγ1 A₀ b R ρ j W
          (ampScale A₀ b j * H)‖ := by rw [hClock]; exact hGrowing
      have hCell : canonicalPrefixMaterialCurrentCell A₀ b R ρ j W
          (ampScale A₀ b j * a + Dpre) = canonicalPrefixAlignedCurrentCell A₀ b R ρ j H W 0 := by
        rw [← hClock]
        have hc := canonicalPrefixMaterialCurrentCell_eq_coRotatedAligned hA.ne' hbR.ne' R ρ j H 0 W
        simpa only [add_zero, circularCoRotationCLM_zero] using hc
      have hConeAt :
          let v := circularConstraintProjectionToTangentCLM hγ hγ1.le
            (canonicalPrefixAlignedCurrentCell A₀ b R ρ j H W 0 - littleCircularReference hγ hγ1)
          let α := circularConstrainedUnstableProjectionCLM hγ hγ1.le v
          ‖v - gseq α 0‖ ≤ ‖α‖ / 32 := by
        simpa only [hCell] using hCone.2.1
      have hPastSimple : ∀ t ∈ Icc (0 : ℝ) a,
          let x := canonicalPrefixStageDeviation hγ hγ1 A₀ b R ρ j 0 W (ampScale A₀ b j * t)
          weightedFamilyNorm h j x ≤ h ∧ ‖x j‖ ≤ h := by
        intro t ht
        exact ⟨(hPast t ht).1, (hPast t ht).2.1⟩
      have hActual := hcaptureξ (k + 1) j hjN S hS hH W hW a ha le_rfl hEntryClock
        hPastSimple hWeighted hCur hParticlesPast hParticles hGrowingAt hConeAt
      have hUpgraded := hUpgradeξ (k + 1) j hjN S hS a ha W hW hPastSimple
        hWeighted hCur hParticlesPast hParticles hEntryClock hActual
      exact ⟨H, hH, hEntryClock, W, hUpgraded⟩
    have hAmp : 0 < ampScale A₀ b k := div_pos hA (pow_pos hbR k)
    have hAmpChild : 0 < ampScale A₀ b (k + 1) := div_pos hA (pow_pos hbR (k + 1))
    let entrance := (τ - Lback) / ampScale A₀ b (k + 1)
    let Hparent := entrance + Dpre / ampScale A₀ b k
    have hentrance : 0 ≤ entrance := div_nonneg (by linarith only [hlong, hLobs]) hAmpChild.le
    have hclock : ampScale A₀ b k * Hparent = ampScale A₀ b k * entrance + Dpre := by
      dsimp only [Hparent]
      rw [mul_add, mul_div_cancel₀ Dpre hAmp.ne']
    have hclockEntrance : ampScale A₀ b k * entrance = (b : ℝ) * (τ - Lback) := by
      dsimp only [entrance]
      rw [ampScale_succ_eq_div]
      field_simp [hAmp.ne', hbR.ne'] <;> ring
    have hclockBound : ampScale A₀ b k * Hparent ≤ Dentry := by
      apply le_trans ?_ hDentryFirst
      rw [hclock, hclockEntrance]
      have hhτ := mul_le_mul_of_nonneg_left hτ.2 hbR.le
      have hc := mul_nonneg hbR.le hLback.le
      dsimp only [Dpre]
      nlinarith only [hhτ, hc]
    have hclockGlobal : ampScale A₀ b k * Hparent ≤ Lentry * ξ + Dentry :=
      hclockBound.trans (le_add_of_nonneg_left (mul_nonneg hLentry hξ))
    have hAmpChildLower : A₀ ≤ ampScale A₀ b (k + 1) := by
      change A₀ ≤ A₀ / (b : ℝ) ^ (k + 1)
      apply (le_div_iff₀ (pow_pos hbR (k + 1))).mpr
      exact mul_le_of_le_one_right hA.le (pow_le_one₀ hbR.le hb1R.le)
    have hChildClock : ampScale A₀ b (k + 1) * Hparent = τ - Lback + Dobs := by
      dsimp only [Hparent, entrance, Dpre]
      rw [ampScale_succ_eq_div]
      field_simp [hAmp.ne', hbR.ne'] <;> ring
    have hHparentT : Hparent < T := by
      have hDT : D < T * cA := (div_lt_iff₀ hcA).mp hTimeBase
      have hA2 : 2 * cA ≤ A₀ := by dsimp only [A₀]; nlinarith only [hξOne, hcA]
      have hTA := mul_le_mul_of_nonneg_left hA2 hT.le
      have hTAmp := mul_le_mul_of_nonneg_left hAmpChildLower hT.le
      have hmul : ampScale A₀ b (k + 1) * Hparent < ampScale A₀ b (k + 1) * T := by
        rw [hChildClock]
        nlinarith only [hτ.2, hLback, hDobsD, hDT, hTA, hTAmp]
      exact (mul_lt_mul_iff_right₀ hAmpChild).mp hmul
    have hBaseWarm : P.HasActualUniformParentWarmupState gseq
        (s := s) (A₀ := A₀) (b := (b : ℝ)) hR hρ (Nat.le_succ k) S
        Dpre Cpre Ccur Cobs κ Lentry Dentry ξ := by
      refine ⟨entrance, hentrance, hHparentT, hclockGlobal, Y, hY, hlower, hcone, ?_, ?_,
        hparticlesY, hparticlesPast, hpast⟩
      · intro u hu
        exact (hweightedY u hu).trans (mul_le_mul_of_nonneg_right (le_max_left CobsFirst CobsNext) hh)
      · intro u hu
        exact (hcurY u hu).trans (mul_le_mul_of_nonneg_right (le_max_left CcurFirst CcurNext) hh)
    have hBase := hRecapture k (Nat.le_succ k) hBaseWarm
    have hDown : ∀ m j : ℕ, j + m = k → ∀ hjN : j ≤ k + 1,
        P.HasActualUniformCapturedState gseq (s := s) (A₀ := A₀) (b := (b : ℝ))
          hR hρ hjN S ℓcap δ ηctrl Hcap Cbcap D₀ Cgraph ξ sCanon Ctarget Lback
            CbackParent CmomentParent Lentry Dentry := by
      intro m
      induction m with
      | zero =>
        intro j hj hjN
        have hjk : j = k := by omega
        subst j
        exact hBase
      | succ m ih =>
        intro j hj hjN
        have hchild : j + 1 ≤ k + 1 := by omega
        have hCapturedChild := ih (j + 1) (by omega) hchild
        obtain ⟨e, he, hEntryClock, W, hCapturedChild⟩ := hCapturedChild
        have hWarmNext := hStepξ (k + 1) j hjN hchild S hS hareaS e he W
          ℓcap δ Hcap Cbcap Cgraph Ctarget hEntryClock hCapturedChild
        have hWarmCommon : P.HasActualUniformParentWarmupState gseq
            (s := s) (A₀ := A₀) (b := (b : ℝ)) hR hρ hjN S
            Dpre Cpre Ccur Cobs κ Lentry Dentry ξ := by
          obtain ⟨a, ha, hEnd, hClock, Wnext, hWnext, hGrowing, hCone, hWeighted, hCur,
            hParticles, hParticlesPast, hPast⟩ := hWarmNext
          refine ⟨a, ha, hEnd, hClock, Wnext, hWnext, hGrowing, hCone, ?_, ?_,
            hParticles, hParticlesPast, hPast⟩
          · intro u hu
            exact (hWeighted u hu).trans (mul_le_mul_of_nonneg_right (le_max_right CobsFirst CobsNext) hh)
          · intro u hu
            exact (hCur u hu).trans (mul_le_mul_of_nonneg_right (le_max_right CcurFirst CcurNext) hh)
        exact hRecapture j hjN hWarmCommon
    intro j hj
    exact hDown (k - j) j (by omega) (Nat.le_of_lt hj)

end CircularMaterialTransferProfile
end Euler2D

end
