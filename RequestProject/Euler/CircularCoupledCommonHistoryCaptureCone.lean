module

public import RequestProject.Euler.CircularCoupledCommonHistoryLateChoice

public import RequestProject.Euler.CircularCoupledSelectedFirstParentCaptureCone
public import RequestProject.Euler.CircularCoupledLateTransferTargetRadiusBudget

public import RequestProject.Euler.CircularCoupledFirstParentCaptureCone
public import RequestProject.Euler.CircularCoupledSelectedFirstTransferLateChoice

/-! Retain the SAME selected canonical target and a prescribed radius cap through the original actual Euler family construction. -/

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 64000000
set_option maxRecDepth 11000

noncomputable section

open Complex Set Filter Topology MeasureTheory Metric
open scoped NNReal ENNReal ContDiff BigOperators

namespace Euler2D

attribute [local instance 2000] rigidGaugeLittle_group rigidGaugeLittle_space rigidGaugeFamily_tower
attribute [local instance 2000] captureBlockTangent_group captureBlockTangent_space
  captureBlockTangent_continuousAdd captureBlockEndo_monoid captureBlockTangent_complete
attribute [local instance] LittleContourSpace.complexScalarNormedSpace LittleContourSpace.complexScalarTower
attribute [local irreducible] circularConstrainedTangentSubmodule circularConstrainedUnstableProjectionCLM
  circularConstrainedReturnMap circularConstrainedChart circularConstraintProjectionToTangentCLM
  circularBanachField circularBanachDomain

namespace CircularMaterialTransferProfile

variable {γ : ℝ≥0} {hγ : 0 < γ} {hγ1 : (γ : ℝ) < 1}
    (P : CircularMaterialTransferProfile hγ hγ1)

theorem exists_actual_coupled_common_history_captureCone_family {Rflow r₀ : ℝ}
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
    (targetFactor : ℝ) (hTargetFactor : 0 ≤ targetFactor)
    (Cextra : ℝ) (hCextra : 0 ≤ Cextra)
    (δmax ηctrl Kextra : ℝ) (hδmax : 0 < δmax) (hηctrl : 0 < ηctrl) (hKextra : 0 ≤ Kextra)
    (hηa : ηctrl ≤ cellA / 16) (hηgap : ηctrl ≤ (1 - cellA) / 16) :
    ∃ b : ℝ≥0, 0 < b ∧ b < 1 / 4 ∧
      bilateral P.moment (((b : ℝ) : ℂ) * (sigma + 5 / 4 * I)) ≠ 0 ∧
      (b : ℝ) * Kextra + (b : ℝ) *
        (finiteInnerLabelLittleRowCoefficient (γ : ℝ) (cellA / 2)
          (circularCanonicalCellNormBudget hγ hγ1) / (2 - 1)) < sigma / 4 ∧
      ∃ δ > 0, δ < δmax ∧ ∃ sCanon < 0, ‖P.coRotatedAncientGraphBase sCanon‖ = δ ∧
      ∃ εtarget > 0, ∃ Ctarget > 0, P.IsSelectedCanonicalCaptureTarget gseq δ sCanon εtarget Ctarget ∧
      targetFactor * δ < εtarget ∧
      ∃ Henv > 0, ∃ Chistory > 0, ∃ c > 0, ∃ Lback > 0, ∃ tmin ≥ 0,
      ∃ ℓ : ℕ, 0 < ℓ ∧ ∃ qc : ℝ, 1 < qc ∧ qc ^ 2 < circularCaptureBlockMultiplier ℓ ∧
      ∀ Bcapture : ℝ, 0 ≤ Bcapture → ∀ nWarmMin : ℕ,
      ∃ nWarm ≥ nWarmMin, 0 < nWarm ∧
        let Dobs := (nWarm : ℝ) * circularCaptureBlockTime ℓ / (b : ℝ)
        let tstar := Dobs - Lback + sCanon
        tmin ≤ tstar ∧ 0 < Dobs ∧ Lback < Dobs ∧ ∃ κ > 0,
        c * Real.exp ((b : ℝ) * sigma * tstar) ≤ κ ∧
        ‖retardedSol (((b : ℝ) : ℂ) * lamStar)
          (((b : ℝ) : ℂ) * (sigma + 5 / 4 * I)) Kstar P.moment tstar‖ = 2 * κ ∧
        (((‖Kstar‖ * max Chistory Cextra * ηctrl) / (sigma / 2 - (b : ℝ) * sigma) *
          Real.exp ((b : ℝ) * sigma * (tstar - sCanon))) *
            Real.exp (-(sigma / 2 - (b : ℝ) * sigma) * Lback) ≤ κ / 4) ∧
        (∀ ρ : ℝ, 0 ≤ ρ →
          ‖retardedSol (((b : ℝ) : ℂ) * lamStar) (((b : ℝ) : ℂ) * (sigma + 5 / 4 * I))
            ((ρ : ℂ) ^ 6 * Kstar) P.moment (sCanon - Lback)‖ *
              Real.exp ((b : ℝ) * sigma * (Lback + (tstar - sCanon))) ≤ (κ / 4) * ρ ^ 6) ∧
        Bcapture * (1 + (nWarm : ℝ) * circularCaptureBlockTime ℓ) ^ 4 ≤
          (κ * ‖circularConstrainedUnstableEmbeddingCLM hγ hγ1.le 1‖) / 32 ∧
        ∀ seedMax > 0, ∀ nMin : ℕ, ∃ n ≥ nMin,
          let s := -(n : ℝ) * (period + period)
          ∃ hs : s ≤ 0, ∃ D > 0, ∃ Cmatch > 0, ∃ Cback > 0,
          ∃ Cb > 0, ∃ Ccur > 0, ∃ Cobs > 0,
            ‖circularConstrainedUnstableProjectionCLM hγ hγ1.le
              (circularConstraintProjectionToTangentCLM hγ hγ1.le
                (P.ancient s - littleCircularReference hγ hγ1))‖ < seedMax ∧
            Henv * ‖circularConstrainedUnstableProjectionCLM hγ hγ1.le
              (circularConstraintProjectionToTangentCLM hγ hγ1.le
                (P.ancient s - littleCircularReference hγ hγ1))‖ * Real.exp (sigma * D) ≤ ηctrl ∧
            Dobs < D ∧
            ∀ cA > 0, D / cA < T →
            ∀ᶠ ξ : ℝ in atTop,
              P.HasActualCoupledFirstCaptureConeFamilyAt (T := T) hq hqE gseq
                b s hs cA D δ sCanon ηctrl Lback Dobs Henv Chistory Cmatch Cback Cb Ccur Cobs κ ξ := by
  obtain ⟨b, hb, hbquarter, hnonzero, hslow, δ, hδ, hδmaxBound, sCanon, hsCanon, hcanonδ,
    εtarget, hεtarget, Ctarget, hCtarget, htarget, hTargetRadius, Henv, hHenv, Chistory, hChistory, c, hc, Lback, hLback, tmin, htmin, hlate⟩ :=
    P.exists_actual_late_coupled_firstTransfer_with_common_half_rate_history_budget hRflow hr₀ hflow hd hfix harea hg hsamples
      hq hqE hT targetFactor hTargetFactor Cextra hCextra δmax ηctrl Kextra hδmax hηctrl hKextra hηa hηgap
  have hbR : 0 < (b : ℝ) := hb
  have hb1 : b < 1 := hbquarter.trans (by norm_num)
  obtain ⟨ℓ, hℓ, qc, hqc, hgap, Ccomp, hCcomp, hstrengthen⟩ :=
    P.exists_eventually_actualFirstParent_coupled_captureCone_strengthening hRflow hr₀ hflow hd hfix harea hg hb hb1
  let m := ‖circularConstrainedUnstableEmbeddingCLM hγ hγ1.le 1‖
  have hm : 0 < m := norm_circularConstrainedUnstableEmbedding_one_pos hγ hγ1.le
  let Hseed := c * m * Real.exp ((b : ℝ) * sigma * (sCanon - Lback))
  have hHseed : 0 < Hseed := mul_pos (mul_pos hc hm) (Real.exp_pos _)
  have hηquarter : ηctrl ≤ cellA / 4 := hηa.trans (by linarith only [cellA_pos])
  refine ⟨b, hb, hbquarter, hnonzero, hslow, δ, hδ, hδmaxBound, sCanon, hsCanon, hcanonδ,
    εtarget, hεtarget, Ctarget, hCtarget, htarget, hTargetRadius, Henv, hHenv, Chistory, hChistory, c, hc, Lback, hLback, tmin, htmin,
    ℓ, hℓ, qc, hqc, hgap, ?_⟩
  intro Bcapture hBcapture nWarmMin
  obtain ⟨nWarm, hnWarmMin, hnWarm, hstar, hconeBudget, hforcingBudget⟩ :=
    exists_firstParent_return_grid_cone_budget hℓ hqc hgap hbR hHseed hCcomp.le hBcapture nWarmMin
  let Dobs := (nWarm : ℝ) * circularCaptureBlockTime ℓ / (b : ℝ)
  let tstar := Dobs - Lback + sCanon
  have hDobs : 0 < Dobs := div_pos
    (mul_pos (Nat.cast_pos.mpr hnWarm) (circularCaptureBlockTime_pos hℓ)) hbR
  have hstar0 : 0 ≤ tstar := htmin.trans hstar
  have hLobs : Lback < Dobs := by dsimp only [tstar] at hstar0; linarith only [hstar0, hsCanon]
  obtain ⟨hκ, hκlower, hcommonLead, hcommonTail, hsamplesLate⟩ := hlate tstar hstar
  let κ := ‖retardedSol (((b : ℝ) : ℂ) * lamStar)
    (((b : ℝ) : ℂ) * (sigma + 5 / 4 * I)) Kstar P.moment tstar‖ / 2
  have hresponseEq : ‖retardedSol (((b : ℝ) : ℂ) * lamStar)
      (((b : ℝ) : ℂ) * (sigma + 5 / 4 * I)) Kstar P.moment tstar‖ = 2 * κ := by
    dsimp only [κ]
    ring
  have hexp : Real.exp ((b : ℝ) * sigma * tstar) =
      Real.exp ((b : ℝ) * sigma * (sCanon - Lback)) * circularCaptureBlockMultiplier ℓ ^ nWarm := by
    rw [circularCaptureBlockMultiplier_eq_exp, ← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    dsimp only [tstar, Dobs]
    field_simp [hbR.ne'] <;> ring
  have hgrowth : Hseed * circularCaptureBlockMultiplier ℓ ^ nWarm ≤ κ * m := by
    have hh := mul_le_mul_of_nonneg_right hκlower hm.le
    rw [hexp] at hh
    convert hh using 1 <;> dsimp only [Hseed] <;> ring
  have hbudget : Ccomp * qc ^ nWarm ≤ (κ * m) / 32 := by
    calc
      _ ≤ (Hseed / 32) * circularCaptureBlockMultiplier ℓ ^ nWarm := hconeBudget
      _ = (Hseed * circularCaptureBlockMultiplier ℓ ^ nWarm) / 32 := by ring
      _ ≤ _ := div_le_div_of_nonneg_right hgrowth (by norm_num)
  have hforcing : Bcapture * (1 + (nWarm : ℝ) * circularCaptureBlockTime ℓ) ^ 4 ≤ (κ * m) / 32 := by
    calc
      _ ≤ (Hseed / 32) * circularCaptureBlockMultiplier ℓ ^ nWarm := hforcingBudget
      _ = (Hseed * circularCaptureBlockMultiplier ℓ ^ nWarm) / 32 := by ring
      _ ≤ _ := div_le_div_of_nonneg_right hgrowth (by norm_num)
  have hWarm : (b : ℝ) * Dobs = (nWarm : ℝ) * circularCaptureBlockTime ℓ := by
    dsimp only [Dobs]
    field_simp [hbR.ne']
  have hobsEq : Lback + (tstar - sCanon) = Dobs := by dsimp only [tstar]; ring
  refine ⟨nWarm, hnWarmMin, hnWarm, hstar, hDobs, hLobs, κ, hκ, hκlower, hresponseEq, hcommonLead, hcommonTail, hforcing, ?_⟩
  intro seedMax hseedMax nMin
  obtain ⟨n, hn, hdata⟩ := hsamplesLate seedMax hseedMax nMin
  dsimp only at hdata
  obtain ⟨hs, D, hD, Cmatch, hCmatch, Cback, hCback, Cb, hCb, Ccur, hCcur,
    Cobs, hCobs, hseed, hterminal, hDobsD, hfamily⟩ := hdata
  rw [hobsEq] at hDobsD hfamily
  let s := -(n : ℝ) * (period + period)
  refine ⟨n, hn, hs, D, hD, Cmatch, hCmatch, Cback, hCback, Cb, hCb, Ccur, hCcur,
    Cobs, hCobs, hseed, hterminal, hDobsD, ?_⟩
  intro cA hcA htime
  have hstrengthenEv := hstrengthen nWarm hq hqE
    (s := s) (cA := cA) (D := D) (δ := δ) (sCanon := sCanon) (ηctrl := ηctrl)
    (Lback := Lback) (Dobs := Dobs) (Henv := Henv) (Chistory := Chistory)
    (Cmatch := Cmatch) (Cback := Cback) (Cb := Cb) (Ccur := Ccur) (Cobs := Cobs) (κ := κ)
    hs hcA hT.le hD.le hηctrl.le hηquarter hLback.le hLobs hDobs hCcur.le hCobs.le hκ hWarm hbudget
  filter_upwards [hfamily cA hcA htime, hstrengthenEv] with ξ hfamilyξ hstrengthenξ
  exact hstrengthenξ hfamilyξ

end CircularMaterialTransferProfile
end Euler2D

end
