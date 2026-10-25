module

public import RequestProject.Euler.CircularFirstParentSourceBudget
public import RequestProject.Euler.CircularSelectedFirstParentCaptureCone

/-! Retain the SAME selected canonical target and a prescribed radius cap through the original actual Euler family construction. -/

@[expose] public section

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

theorem exists_actual_firstTransfer_selected_sourceReady_captureCone_family {Rflow r₀ : ℝ}
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
    {Cr Cd F Δ : ℝ} (hCr : 0 < Cr) (hCd : 0 ≤ Cd) (hF : 0 ≤ F) (hΔ : 0 ≤ Δ)
    (δmax ηctrl Kextra : ℝ) (hδmax : 0 < δmax) (hηctrl : 0 < ηctrl) (hKextra : 0 ≤ Kextra)
    (hηa : ηctrl ≤ cellA / 16) (hηgap : ηctrl ≤ (1 - cellA) / 16) :
    ∃ b : ℝ≥0, 0 < b ∧ b < 1 / 4 ∧
      bilateral P.moment (((b : ℝ) : ℂ) * (sigma + 5 / 4 * I)) ≠ 0 ∧
      (b : ℝ) * Kextra + (b : ℝ) *
        (finiteInnerLabelLittleRowCoefficient (γ : ℝ) (cellA / 2)
          (circularCanonicalCellNormBudget hγ hγ1) / (2 - 1)) < sigma / 4 ∧
      ∃ Cpre > 0, ∃ δ > 0, δ < δmax ∧ ∃ sCanon < 0, ‖P.coRotatedAncientGraphBase sCanon‖ = δ ∧
      ∃ εtarget > 0, ∃ Ctarget > 0, P.IsSelectedCanonicalCaptureTarget gseq δ sCanon εtarget Ctarget ∧
      ∃ Henv > 0, ∃ Chistory > 0, ∃ c > 0, ∃ Lback > 0, ∃ tmin ≥ 0,
      ∃ ℓ : ℕ, 0 < ℓ ∧ ∃ qc : ℝ, 1 < qc ∧ qc ^ 2 < circularCaptureBlockMultiplier ℓ ∧
      ∀ nWarmMin : ℕ, ∃ nWarm ≥ nWarmMin, 0 < nWarm ∧
        let Dobs := (nWarm : ℝ) * circularCaptureBlockTime ℓ / (b : ℝ)
        let tstar := Dobs - Lback + sCanon
        tmin ≤ tstar ∧ 0 < Dobs ∧ Lback < Dobs ∧ ∃ κ > 0,
        c * Real.exp ((b : ℝ) * sigma * tstar) ≤ κ ∧
        F * (finiteCurrentPolynomialForcingCoefficient (γ : ℝ) (cellA / 2)
          (circularCanonicalCellNormBudget hγ hγ1)
          (radialStageRadiusConstant Cr (Cpre * (1 + (nWarm : ℝ) * circularCaptureBlockTime ℓ)) b)
          b Cd + Δ) ≤ (κ * ‖circularConstrainedUnstableEmbeddingCLM hγ hγ1.le 1‖) / 32 ∧
        ∀ seedMax > 0, ∀ nMin : ℕ, ∃ n ≥ nMin,
          let s := -(n : ℝ) * (period + period)
          ∃ hs : s ≤ 0, ∃ A₀ > 0, ∃ D > 0, ∃ Cmatch > 0, ∃ Cback > 0,
          ∃ Ccur > 0, ∃ Cobs > 0,
            ‖circularConstrainedUnstableProjectionCLM hγ hγ1.le
              (circularConstraintProjectionToTangentCLM hγ hγ1.le
                (P.ancient s - littleCircularReference hγ hγ1))‖ < seedMax ∧
            Henv * ‖circularConstrainedUnstableProjectionCLM hγ hγ1.le
              (circularConstraintProjectionToTangentCLM hγ hγ1.le
                (P.ancient s - littleCircularReference hγ hγ1))‖ * Real.exp (sigma * D) ≤ ηctrl ∧
            D / A₀ < T ∧ Dobs < D ∧
            ∀ᶠ ξ : ℝ in atTop,
              P.HasActualFirstCaptureConeFamilyAt (T := T) hq hqE gseq
                b s hs A₀ D δ sCanon ηctrl Lback Dobs Henv Chistory Cmatch Cback Cpre Ccur Cobs κ ξ := by
  obtain ⟨b, hb, hbquarter, hnonzero, hslow, δ, hδ, hδmaxBound, sCanon, hsCanon, hcanonδ,
    εtarget, hεtarget, Ctarget, hCtarget, htarget, Henv, hHenv, Chistory, hChistory, c, hc, Lback, hLback, tmin, htmin,
    ℓ, hℓ, qc, hqc, hgap, hfamily⟩ :=
    P.exists_actual_firstTransfer_selected_captureCone_family hRflow hr₀ hflow hd hfix harea hg hsamples
      hq hqE hT δmax ηctrl Kextra hδmax hηctrl hKextra hηa hηgap
  have hbR : 0 < (b : ℝ) := hb
  have hb1 : b < 1 := hbquarter.trans (by norm_num)
  have hbR1 : (b : ℝ) < 1 := hb1
  obtain ⟨Cpre, hCpre, hstrengthen⟩ :=
    P.exists_eventually_actualFirstParent_uniform_particle_strengthening hb hb1
  let L := circularCanonicalCellNormBudget hγ hγ1
  have hL : 0 < L := circularCanonicalCellNormBudget_pos hγ hγ1
  obtain ⟨Bcapture, hBcapture, hBbudget⟩ :=
    exists_parentCapture_polynomial_warmup_budget (η := (γ : ℝ))
      (e := cellA / 2) (L := L) (Cr := Cr) (Cw := Cpre) (b := (b : ℝ))
      (Cd := Cd) (Δ := Δ) (F := F)
      (half_pos cellA_pos) hL.le hCr hCpre.le hbR hbR1 hCd hΔ hF
  have hηquarter : ηctrl ≤ cellA / 4 := hηa.trans (by linarith only [cellA_pos])
  refine ⟨b, hb, hbquarter, hnonzero, hslow, Cpre, hCpre, δ, hδ, hδmaxBound, sCanon, hsCanon, hcanonδ,
    εtarget, hεtarget, Ctarget, hCtarget, htarget, Henv, hHenv, Chistory, hChistory, c, hc, Lback, hLback, tmin, htmin,
    ℓ, hℓ, qc, hqc, hgap, ?_⟩
  intro nWarmMin
  obtain ⟨nWarm, hnMin, hnWarm, hstar, hDobs, hLobs, κ, hκ, hκlower, hsource, hdata⟩ :=
    hfamily Bcapture hBcapture nWarmMin
  let Dobs := (nWarm : ℝ) * circularCaptureBlockTime ℓ / (b : ℝ)
  have hW0 : 0 ≤ Cpre * (1 + (nWarm : ℝ) * circularCaptureBlockTime ℓ) := by
    positivity [circularCaptureBlockTime_pos hℓ]
  have hWbudget := hBbudget (circularCaptureBlockTime ℓ) (circularCaptureBlockTime_pos hℓ).le
    nWarm (Cpre * (1 + (nWarm : ℝ) * circularCaptureBlockTime ℓ)) hW0 le_rfl
  have hsourceReady := hWbudget.trans hsource
  refine ⟨nWarm, hnMin, hnWarm, hstar, hDobs, hLobs, κ, hκ, hκlower, hsourceReady, ?_⟩
  intro seedMax hseedMax nMin
  obtain ⟨n, hn, hdataN⟩ := hdata seedMax hseedMax nMin
  dsimp only at hdataN
  obtain ⟨hs, A₀, hA, D, hD, Cmatch, hCmatch, Cback, hCback, Cb, hCb, Ccur, hCcur,
    Cobs, hCobs, hseed, hterminal, htime, hDobsD, hfamilyEv⟩ := hdataN
  let s := -(n : ℝ) * (period + period)
  have hstrengthEv := hstrengthen hq hqE gseq
    (s := s) (A₀ := A₀) (D := D) (δ := δ) (sCanon := sCanon) (ηctrl := ηctrl)
    (Lback := Lback) (Dobs := Dobs) (Henv := Henv) (Chistory := Chistory)
    (Cmatch := Cmatch) (Cback := Cback) (Cb := Cb) (Ccur := Ccur) (Cobs := Cobs) (κ := κ)
    hs hA hT.le hD.le hηctrl.le hηquarter hLobs hDobs.le hCcur.le hCobs.le
  refine ⟨n, hn, hs, A₀, hA, D, hD, Cmatch, hCmatch, Cback, hCback, Ccur, hCcur,
    Cobs, hCobs, hseed, hterminal, htime, hDobsD, ?_⟩
  filter_upwards [hfamilyEv, hstrengthEv] with ξ hfamilyξ hstrengthξ
  exact hstrengthξ hfamilyξ

end CircularMaterialTransferProfile
end Euler2D

end
