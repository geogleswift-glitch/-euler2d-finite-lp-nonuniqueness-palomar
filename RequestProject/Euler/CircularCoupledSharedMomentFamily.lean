module

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
set_option maxHeartbeats 48000000
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

theorem exists_actual_coupled_selected_shared_firstParent_whole_past_moment_family {Rflow r₀ : ℝ}
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
        ∃ hs : s ≤ 0, ∃ D > 0, ∃ Cmatch > 0, ∃ Cback > 0,
        ∃ Ccur > 0, ∃ Cobs > 0,
          ‖circularConstrainedUnstableProjectionCLM hγ hγ1.le
            (circularConstraintProjectionToTangentCLM hγ hγ1.le
              (P.ancient s - littleCircularReference hγ hγ1))‖ < seedMax ∧
          Henv * ‖circularConstrainedUnstableProjectionCLM hγ hγ1.le
            (circularConstraintProjectionToTangentCLM hγ hγ1.le
              (P.ancient s - littleCircularReference hγ hγ1))‖ * Real.exp (sigma * D) ≤ ηctrl ∧
          ∃ D₀ > 0, ∃ Cgraph > 0, ∃ CbackParent > 0, ∃ cA > 0, D / cA < T ∧ Dobs < D ∧
          ∀ᶠ ξ : ℝ in atTop,
            P.HasActualCoupledFirstParentWholePastMomentFamilyAt (T := T) hq hqE gseq
              ℓcap Hcap Cbcap D₀ Cgraph CbackParent CmomentParent b s hs cA D δ sCanon Ctarget ηctrl Lback Dobs
              Henv Chistory Cmatch Cback Cpre Ccur Cobs κ ξ := by
  obtain ⟨Kself, hKself, Cr, hCr, Cd, hCd, F, hF, ηctrl, hηctrl, hηa, hηgap,
    δcapture, hδcapture, ℓcap, hℓcap, Hcap, hHcap, hparent⟩ :=
    P.exists_uniform_actualCoupled_parent_capture_of_warmup hRflow hr₀ hflow hd hfix harea hg
  obtain ⟨CmomentParent, hCmomentParent, hMomentAll⟩ :=
    P.exists_eventually_actualParent_whole_past_boxed_moment gseq hηctrl.le
  let targetFactor := Hcap * (4 * circularCaptureBlockMultiplier ℓcap / 3)
  have hTargetFactor : 0 ≤ targetFactor := by
    dsimp only [targetFactor]
    rw [circularCaptureBlockMultiplier_eq_exp]
    positivity
  let Ksum := Kextra + (Kself : ℝ)
  let δbound := min δmax δcapture
  have hKsum : 0 ≤ Ksum := add_nonneg hKextra (NNReal.coe_nonneg Kself)
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
    dsimp only [Ksum] at hslowSum
    nlinarith only [hslowSum, hh]
  have hslowParent : (b : ℝ) * Kself + (b : ℝ) *
      (finiteInnerLabelLittleRowCoefficient (γ : ℝ) (cellA / 2)
        (circularCanonicalCellNormBudget hγ hγ1) / (2 - 1)) < sigma / 4 := by
    have hh := mul_nonneg hbR.le hKextra
    dsimp only [Ksum] at hslowSum
    nlinarith only [hslowSum, hh]
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
  refine ⟨CmomentParent, hCmomentParent, b, hb, hbquarter, hnonzero, hslowExtra, ηctrl, hηctrl, hηa, hηgap, Cpre, hCpre,
    δ, hδ, hδmaxδ, sCanon, hsCanon, hcanonδ, εtarget, hεtarget, Ctarget, hCtarget,
    htarget, Henv, hHenv, Chistory, hChistory, Lback, hLback, Dobs, hDobs, hLobs,
    κ, hκ, hresponseEq, hcommonLead, hcommonTail, ℓpre, hℓpre, qc, hqc, hqgap, Ccomp, hCcomp, hwitness, nWarm, hnWarm, hDpreEq, hconeBudget, ℓcap, hℓcap, Hcap, hHcap, Cbcap, hCbcap, hTargetRadius, ?_⟩
  intro seedMax hseedMax nMin
  obtain ⟨n, hn, hdataN⟩ := hdata seedMax hseedMax nMin
  dsimp only at hdataN
  obtain ⟨hs, D, hD, Cmatch, hCmatch, Cback, hCback, Ccur, hCcur,
    Cobs, hCobs, hseed, hterminal, hDobsD, hfamilyEv⟩ := hdataN
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
      cA₀ D δ sCanon ηctrl Lback Dobs Henv Chistory Cmatch Cback Cpre Ccur Cobs κ ξ₀ hD.le hfamily₀
  obtain ⟨D₀, hD₀, Cgraph, hCgraph, hcaptured⟩ :=
    hparent b hb hbquarter hslowParent Cpre Dpre Cobs Ccur κ δ
      hCpre.le hDpre hCobs.le hCcur.le hκ hδ hδcapδ hsourceReady
  have hηquarter : ηctrl ≤ cellA / 4 := hηa.trans (by linarith only [cellA_pos])
  let J := circularConstraintProjectionToTangentCLM hγ hγ1.le
  let Q := circularConstrainedUnstableProjectionCLM hγ hγ1.le
  let Cseed := 2 * ‖Q‖ * ‖J‖ * Ccur
  have hCseed : 0 ≤ Cseed := by dsimp only [Cseed]; positivity
  obtain ⟨CbackParent, hCbackParent, hLookParent⟩ :=
    P.exists_eventually_actualCoupled_parentMatchedCapture_with_lookback
      hsCanon.le hδ hηctrl hηquarter hHcap.le hCtarget.le hCgraph.le hLback hℓcap gseq
  let Kpast := 2 * max (1 : ℝ) Ccur
  have hKpast : 0 ≤ Kpast := by dsimp only [Kpast]; positivity
  let Lentry := (6 / sigma) * ((b : ℝ) / (1 - (b : ℝ)))
  let Dentry := (b : ℝ) * D + (Dpre + (b : ℝ) * D₀) / (1 - (b : ℝ))
  have hgap : 0 < 1 - (b : ℝ) := sub_pos.mpr (show (b : ℝ) < 1 from hb1)
  have hLentry : 0 ≤ Lentry := mul_nonneg (div_nonneg (by norm_num) sigma_pos.le)
    (div_nonneg hbR.le hgap.le)
  have hDentry : 0 ≤ Dentry := add_nonneg (mul_nonneg hbR.le hD.le)
    (div_nonneg (add_nonneg hDpre (mul_nonneg hbR.le hD₀.le)) hgap.le)
  have hSlopeEq : Lentry + 6 / sigma = (6 / sigma) / (1 - (b : ℝ)) := by
    dsimp only [Lentry]
    field_simp [sigma_pos.ne', hgap.ne']
    <;> ring
  have hClockMargin : sigma * (Lentry + 6 / sigma) < 8 := by
    rw [hSlopeEq]
    exact (circularCapture_cascade_clock_log_margin hbR (show (b : ℝ) < 1 / 4 from hbquarter)).2
  have hDpreBound : Dpre ≤ (Dpre + (b : ℝ) * D₀) / (1 - (b : ℝ)) := by
    apply (le_div_iff₀ hgap).mpr
    nlinarith only [mul_nonneg hbR.le hDpre, mul_nonneg hbR.le hD₀.le]
  have hDentryFirst : (b : ℝ) * (D + Dobs) ≤ Dentry := by
    calc
      _ = (b : ℝ) * D + Dpre := by dsimp only [Dpre]; ring
      _ ≤ _ := add_le_add le_rfl hDpreBound
  obtain ⟨cA, hcA, hTimeBase, hcaptureEv⟩ :=
    hcaptured D Lentry Dentry hD.le hLentry hDentry hs hq hqE hT hancient
  have hmatchEv := P.eventually_actualCoupled_parentCapture_matches_selected_target
    hs hb hcA hT hq hqE hℓcap hδ hηctrl hηquarter hHcap htarget hTargetRadius hancient
  have hLookEv := hLookParent b hb hb1.le Cbcap D₀ Cseed hCbcap.le hCseed
    hs hcA hq hqE hT.le hancient
  have hWholeEv := P.eventually_actualParentCapture_whole_past_history
    (δ := δ) (ηcur := ηctrl) (Hcap := Hcap) (Cb := Cbcap) (D₀ := D₀) (Cgraph := Cgraph)
    (sCanon := sCanon) (Ctarget := Ctarget) (Lback := Lback) (Cback := CbackParent)
    (Kpast := Kpast) (Lentry := Lentry) (Dentry := Dentry)
    hηctrl hKpast hℓcap hClockMargin gseq
  have hMomentEv := hMomentAll (s := s) (cA := cA) (b := (b : ℝ)) (q := q) (T := T)
    hs hcA hbR hq hqE hT.le
  refine ⟨n, hn, hs, D, hD, Cmatch, hCmatch, Cback, hCback, Ccur, hCcur, Cobs, hCobs,
    hseed, hterminal, D₀, hD₀, Cgraph, hCgraph, CbackParent, hCbackParent, cA, hcA, hTimeBase, hDobsD, ?_⟩
  filter_upwards [hfamilyEv cA hcA hTimeBase, hcaptureEv, hmatchEv, hLookEv, hWholeEv, hMomentEv, eventually_ge_atTop (0 : ℝ)]
    with ξ hfamilyξ hcaptureξ hmatchξ hlookξ hwholeξ hmomentξ hξ
  let ρ := Real.exp (-ξ)
  let R := ρ ^ 10
  let A₀ := cA * (1 + ξ)
  have hρ : 0 < ρ := Real.exp_pos (-ξ)
  have hR : 0 < R := pow_pos hρ 10
  have hA : 0 < A₀ := mul_pos hcA (by linarith only [hξ])
  dsimp only [HasActualCoupledFirstCaptureConeFamilyAt, HasActualCoupledFirstParentWholePastMomentFamilyAt] at hfamilyξ ⊢
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
    have hAmp : 0 < ampScale A₀ b k := div_pos hA (pow_pos hbR k)
    have hAmpChild : 0 < ampScale A₀ b (k + 1) := div_pos hA (pow_pos hbR (k + 1))
    let entrance := (τ - Lback) / ampScale A₀ b (k + 1)
    let Hparent := entrance + Dpre / ampScale A₀ b k
    have hentrance : 0 ≤ entrance := div_nonneg (by linarith only [hlong, hLobs]) hAmpChild.le
    have hHparent : 0 ≤ Hparent := add_nonneg hentrance (div_nonneg hDpre hAmp.le)
    have hclock : ampScale A₀ b k * Hparent = ampScale A₀ b k * entrance + Dpre := by
      dsimp only [Hparent]
      rw [mul_add, mul_div_cancel₀ Dpre hAmp.ne']
    have hclockEntrance : ampScale A₀ b k * entrance = (b : ℝ) * (τ - Lback) := by
      dsimp only [entrance]
      rw [ampScale_succ_eq_div]
      field_simp [hAmp.ne', hbR.ne']
      <;> ring
    have hclockBound : ampScale A₀ b k * Hparent ≤ Dentry := by
      apply le_trans ?_ hDentryFirst
      rw [hclock, hclockEntrance]
      have hh := mul_le_mul_of_nonneg_left hτ.2 hbR.le
      have hc := mul_nonneg hbR.le hLback.le
      dsimp only [Dpre]
      nlinarith only [hh, hc]
    have hclockGlobal : ampScale A₀ b k * Hparent ≤ Lentry * ξ + Dentry :=
      hclockBound.trans (le_add_of_nonneg_left (mul_nonneg hLentry hξ))
    have hGrowing : κ * ρ ^ 6 ≤ ‖canonicalPrefixMaterialGrowingCoordinate hγ hγ1 A₀ b R ρ k Y
        (ampScale A₀ b k * Hparent)‖ := by
      rw [hclock]
      exact hlower
    have hcell : canonicalPrefixMaterialCurrentCell A₀ b R ρ k Y
        (ampScale A₀ b k * entrance + Dpre) =
          canonicalPrefixAlignedCurrentCell A₀ b R ρ k Hparent Y 0 := by
      rw [← hclock]
      have hh := canonicalPrefixMaterialCurrentCell_eq_coRotatedAligned hA.ne' hbR.ne' R ρ k Hparent 0 Y
      simpa only [add_zero, circularCoRotationCLM_zero] using hh
    let Zold := canonicalPrefixMaterialCurrentCell A₀ b R ρ k Y
      (ampScale A₀ b k * entrance + Dpre)
    let vold := circularConstraintProjectionToTangentCLM hγ hγ1.le
      (Zold - littleCircularReference hγ hγ1)
    let αold := circularConstrainedUnstableProjectionCLM hγ hγ1.le vold
    have hconeOld : ‖vold - gseq αold 0‖ ≤ ‖αold‖ / 32 := hcone.2.1
    have hconeEntry :
        let v := circularConstraintProjectionToTangentCLM hγ hγ1.le
          (canonicalPrefixAlignedCurrentCell A₀ b R ρ k Hparent Y 0 - littleCircularReference hγ hγ1)
        let α := circularConstrainedUnstableProjectionCLM hγ hγ1.le v
        ‖v - gseq α 0‖ ≤ ‖α‖ / 32 := by
      simpa only [vold, αold, Zold, hcell] using hconeOld
    have hActual := hcaptureξ (k + 1) k (Nat.le_succ k) S hS hHparent Y hY entrance hentrance
      le_rfl hclockGlobal
      (by intro t ht; exact ⟨(hpast t ht).1, (hpast t ht).2.1⟩)
      hweightedY hcurY hparticlesPast hparticlesY hGrowing hconeEntry
    have hMatchedActual := hmatchξ (k + 1) k (Nat.le_succ k) S hS Hparent hHparent
      Y Cbcap D₀ Cgraph hActual
    have hZnorm : ‖Zold - littleCircularReference hγ hγ1‖ ≤ Ccur * (2 * ρ ^ 6) := by
      dsimp only [Zold]
      rw [canonicalPrefixMaterialCurrentCell_eq_coRotatedAligned hA.ne' hbR.ne' R ρ k entrance Dpre Y,
        norm_circularCoRotationCLM_sub_reference hγ hγ1,
        norm_canonicalPrefixAlignedCurrentCell_sub_reference hγ hγ1]
      exact hcurY Dpre ⟨hDpre, le_rfl⟩
    have hZnormEntry : ‖canonicalPrefixAlignedCurrentCell A₀ b R ρ k Hparent Y 0 -
        littleCircularReference hγ hγ1‖ ≤ Ccur * (2 * ρ ^ 6) := by
      rw [← hcell]
      exact hZnorm
    have hSeedEntry : ‖Q (J (canonicalPrefixAlignedCurrentCell A₀ b R ρ k Hparent Y 0 -
        littleCircularReference hγ hγ1))‖ ≤ Cseed * ρ ^ 6 := by
      calc
        _ ≤ ‖Q‖ * ‖J (canonicalPrefixAlignedCurrentCell A₀ b R ρ k Hparent Y 0 -
            littleCircularReference hγ hγ1)‖ := Q.le_opNorm _
        _ ≤ ‖Q‖ * (‖J‖ * ‖canonicalPrefixAlignedCurrentCell A₀ b R ρ k Hparent Y 0 -
            littleCircularReference hγ hγ1‖) :=
          mul_le_mul_of_nonneg_left (J.le_opNorm _) (norm_nonneg _)
        _ ≤ ‖Q‖ * (‖J‖ * (Ccur * (2 * ρ ^ 6))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hZnormEntry (norm_nonneg _)) (norm_nonneg _)
        _ = _ := by dsimp only [Cseed]; ring
    have hLookActual := hlookξ (k + 1) k (Nat.le_succ k) S hS Hparent hHparent
      Y hSeedEntry hMatchedActual
    have hEarlyPast := canonicalPrefixMaterialCurrentCell_past_warmup_bound hγ hγ1
      (A₀ := A₀) (b := (b : ℝ)) (R := R) (ρ := ρ) (entrance := entrance) (Dpre := Dpre) (Kcur := Ccur)
      hA hbR hρ.le hentrance hDpre hCcur.le k Y
      (by intro t ht; exact (hpast t ht).2.1) hcurY
    have hWholeActual := hwholeξ (s := s) (A₀ := A₀) (b := (b : ℝ)) (R := R) (T := T)
      hA hbR hR (k + 1) k (Nat.le_succ k) S Hparent hHparent Y hclockGlobal hEarlyPast hLookActual
    have hMomentActual := hmomentξ (k + 1) k (Nat.le_succ k) S Hparent hHparent Y
      ℓcap δ Hcap Cbcap D₀ Cgraph sCanon Ctarget Lback CbackParent hWholeActual
    exact ⟨htimeN, S, hS, hweak, hareaS, X, hX, hweighted, hcur, hforward,
      τ, hτ, hlong, angle, hvalue, hbefore, hhistory, hmomentHistory, hmatch, hback,
      Y, hY, hlower, hcone, hMomentActual, hweightedY, hcurY, hparticlesY, hparticlesPast, hpast⟩

end CircularMaterialTransferProfile
end Euler2D

end
