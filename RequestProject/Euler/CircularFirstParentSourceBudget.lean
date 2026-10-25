module

public import RequestProject.Euler.CircularFirstParentCaptureCone
public import RequestProject.Euler.CircularParentCaptureWarmupBudget

/-! The first-parent entrance family has an actual particle radius with
a coefficient fixed before the warmup. Its future capture source budget
is therefore obtained from the same physical particles without a circular
choice of the observation time. -/

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

theorem actualFirstCaptureConeFamily_initial_ancient_bound
    {q T : ℝ} [Fact (1 ≤ ENNReal.ofReal q)] (hq : 0 < q) (hqE : 2 ≤ ENNReal.ofReal q)
    (gseq : CircularConstrainedTangentSpace γ → ℕ → CircularConstrainedTangentSpace γ)
    (b : ℝ≥0) (s : ℝ) (hs : s ≤ 0)
    (A₀ D δ sCanon ηctrl Lback Dobs Henv Chistory Cmatch Cback Cb Ccur Cobs κ ξ : ℝ)
    (hD : 0 ≤ D)
    (hfamily : P.HasActualFirstCaptureConeFamilyAt (T := T) hq hqE gseq
      b s hs A₀ D δ sCanon ηctrl Lback Dobs Henv Chistory Cmatch Cback Cb Ccur Cobs κ ξ) :
    ∀ i, ‖(P.ancient s i).val - circularReferenceC1 hγ hγ1 i‖ ≤ ηctrl := by
  dsimp only [HasActualFirstCaptureConeFamilyAt] at hfamily
  obtain ⟨hhalf, hlp, hfinite⟩ := hfamily
  obtain ⟨htime, S, hS, hweak, harea, X, hX, hweighted, hcur, hrest⟩ := hfinite 1 (by decide)
  have hcur0 := hcur 0 ⟨le_rfl, hD⟩
  rw [P.actualCanonicalPrefix_initial_deepest_deviation (Real.exp_pos (-ξ)) (Real.exp_pos (-ξ))
    1 S X hX] at hcur0
  intro i
  exact (norm_le_pi_norm (P.ancient s - littleCircularReference hγ hγ1) i).trans hcur0

theorem exists_eventually_actualFirstParent_uniform_particle_strengthening
    {b : ℝ≥0} (hb : 0 < b) (hb1 : b < 1) :
    ∃ Cpre > 0,
      ∀ {q T : ℝ}, ∀ [Fact (1 ≤ ENNReal.ofReal q)],
      ∀ (hq : 0 < q) (hqE : 2 ≤ ENNReal.ofReal q)
        (gseq : CircularConstrainedTangentSpace γ → ℕ → CircularConstrainedTangentSpace γ),
      ∀ {s A₀ D δ sCanon ηctrl Lback Dobs Henv Chistory Cmatch Cback Cb Ccur Cobs κ : ℝ},
      ∀ (hs : s ≤ 0) (hA : 0 < A₀), 0 ≤ T → 0 ≤ D →
      0 ≤ ηctrl → ηctrl ≤ cellA / 4 → Lback < Dobs → 0 ≤ Dobs →
      0 ≤ Ccur → 0 ≤ Cobs →
      ∀ᶠ ξ : ℝ in atTop,
        P.HasActualFirstCaptureConeFamilyAt (T := T) hq hqE gseq
          b s hs A₀ D δ sCanon ηctrl Lback Dobs Henv Chistory Cmatch Cback Cb Ccur Cobs κ ξ →
        P.HasActualFirstCaptureConeFamilyAt (T := T) hq hqE gseq
          b s hs A₀ D δ sCanon ηctrl Lback Dobs Henv Chistory Cmatch Cback Cpre Ccur Cobs κ ξ := by
  have hbR : 0 < (b : ℝ) := hb
  have hbR1 : (b : ℝ) < 1 := hb1
  obtain ⟨Cpre, hCpre, Bpoly, hBpoly, Ktorus, hKtorus, εchart, hεchart, hforcing⟩ :=
    P.exists_eventually_actualFirstParent_preCapture_forcing hbR hbR1
  refine ⟨Cpre, hCpre, ?_⟩
  intro q T _ hq hqE gseq s A₀ D δ sCanon ηctrl Lback Dobs Henv Chistory
    Cmatch Cback Cb Ccur Cobs κ hs hA hT hD hη hηa hLobs hDobs hCcur hCobs
  by_cases hancient : ∀ i, ‖(P.ancient s i).val - circularReferenceC1 hγ hγ1 i‖ ≤ ηctrl
  · have hDparent : 0 ≤ (b : ℝ) * Dobs := mul_nonneg hbR.le hDobs
    have hforcingEv := hforcing (D := (b : ℝ) * Dobs) (Kw := Cobs) (Kcur := Ccur)
      hs hA hq hqE hDparent hCobs hCcur hT hη hηa hancient
    filter_upwards [hforcingEv] with ξ hforcingξ
    intro hfamily
    let ρ := Real.exp (-ξ)
    have hρ : 0 < ρ := Real.exp_pos (-ξ)
    dsimp only [HasActualFirstCaptureConeFamilyAt] at hfamily ⊢
    obtain ⟨hhalf, hlp, hfinite⟩ := hfamily
    refine ⟨hhalf, hlp, ?_⟩
    intro N hN
    cases N with
    | zero => omega
    | succ k =>
      obtain ⟨htimeN, S, hS, hweak, hareaS, X, hX, hweighted, hcur, hforward,
        τ, hτ, hlong, angle, hvalue, hbefore, hhistory, hmomentHistory, hmatch, hback,
        Y, hY, hlower, hcone, hweightedY, hcurY, hparticlesY, hparticlesPast, hpast⟩ :=
          hfinite (k + 1) (Nat.succ_pos k)
      have hAmp : 0 < ampScale A₀ b (k + 1) := div_pos hA (pow_pos hbR (k + 1))
      have hAmpParent : 0 < ampScale A₀ b k := div_pos hA (pow_pos hbR k)
      let entrance := (τ - Lback) / ampScale A₀ b (k + 1)
      let Hparent := entrance + ((b : ℝ) * Dobs) / ampScale A₀ b k
      have hτL : 0 ≤ τ - Lback := by linarith only [hlong, hLobs]
      have hentrance : 0 ≤ entrance := div_nonneg hτL hAmp.le
      have hHparent : 0 ≤ Hparent :=
        hentrance.trans (le_add_of_nonneg_right (div_nonneg hDparent hAmpParent.le))
      have hstart := hparticlesPast entrance ⟨hentrance, le_rfl⟩
      obtain ⟨p, hp, hpure⟩ := hforcingξ k S hS hHparent Y hY entrance hentrance
        le_rfl hweightedY hcurY hstart
      exact ⟨htimeN, S, hS, hweak, hareaS, X, hX, hweighted, hcur, hforward,
        τ, hτ, hlong, angle, hvalue, hbefore, hhistory, hmomentHistory, hmatch, hback,
        Y, hY, hlower, hcone, hweightedY, hcurY, hpure, hparticlesPast, hpast⟩
  · exact Eventually.of_forall fun ξ hfamily => False.elim (hancient
      (P.actualFirstCaptureConeFamily_initial_ancient_bound hq hqE gseq b s hs
        A₀ D δ sCanon ηctrl Lback Dobs Henv Chistory Cmatch Cback Cb Ccur Cobs κ ξ hD hfamily))

theorem exists_actual_firstTransfer_sourceReady_captureCone_family {Rflow r₀ : ℝ}
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
    (ηctrl Kextra : ℝ) (hηctrl : 0 < ηctrl) (hKextra : 0 ≤ Kextra)
    (hηa : ηctrl ≤ cellA / 16) (hηgap : ηctrl ≤ (1 - cellA) / 16) :
    ∃ b : ℝ≥0, 0 < b ∧ b < 1 / 4 ∧
      bilateral P.moment (((b : ℝ) : ℂ) * (sigma + 5 / 4 * I)) ≠ 0 ∧
      (b : ℝ) * Kextra + (b : ℝ) *
        (finiteInnerLabelLittleRowCoefficient (γ : ℝ) (cellA / 2)
          (circularCanonicalCellNormBudget hγ hγ1) / (2 - 1)) < sigma / 4 ∧
      ∃ Cpre > 0, ∃ δ > 0, ∃ sCanon < 0, ‖P.coRotatedAncientGraphBase sCanon‖ = δ ∧
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
  obtain ⟨b, hb, hbquarter, hnonzero, hslow, δ, hδ, sCanon, hsCanon, hcanonδ,
    Henv, hHenv, Chistory, hChistory, c, hc, Lback, hLback, tmin, htmin,
    ℓ, hℓ, qc, hqc, hgap, hfamily⟩ :=
    P.exists_actual_firstTransfer_captureCone_family hRflow hr₀ hflow hd hfix harea hg hsamples
      hq hqE hT ηctrl Kextra hηctrl hKextra hηa hηgap
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
  refine ⟨b, hb, hbquarter, hnonzero, hslow, Cpre, hCpre, δ, hδ, sCanon, hsCanon, hcanonδ,
    Henv, hHenv, Chistory, hChistory, c, hc, Lback, hLback, tmin, htmin,
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
