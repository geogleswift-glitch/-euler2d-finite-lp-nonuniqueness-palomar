module

public import RequestProject.Euler.CircularFirstTransferLateChoice
public import RequestProject.Euler.CircularCoupledActualFirstNonzeroTransfer

/-! Retain the SAME selected canonical target and a prescribed radius cap through the original actual Euler family construction. -/

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 20000000
set_option maxRecDepth 7500

noncomputable section

open Complex Set Filter Topology MeasureTheory Metric
open scoped NNReal ENNReal

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

theorem exists_actual_late_coupled_firstTransfer_selected_nonzero_family {Rflow r₀ : ℝ}
    (hRflow : 0 < Rflow) (hr₀ : 0 < r₀)
    {Y : (Fin 2 → LittleContourSpace γ) → ℝ → Fin 2 → LittleContourSpace γ}
    (hY : IsBanachFlowOn (circularBanachField hγ hγ1) (circularBanachDomain hγ hγ1)
      (ball (littleCircularReference hγ hγ1) Rflow) period Y)
    (hd : ContDiffAt ℝ 2 (fun W => Y W period) (littleCircularReference hγ hγ1))
    (hfix : Y (littleCircularReference hγ hγ1) period = littleCircularReference hγ hγ1)
    (harea : ∀ W ∈ ball (littleCircularReference hγ hγ1) Rflow, ∀ i,
      littleContourArea γ (Y W period i) = littleContourArea γ (W i))
    {gseq : CircularConstrainedTangentSpace γ → ℕ → CircularConstrainedTangentSpace γ}
    (hg : IsLocalWeightedBackwardGraph
      (banachDoubleReturn (circularConstrainedReturnMap hγ hγ1 (fun W => Y W period)))
      (circularConstrainedUnstableProjectionCLM hγ hγ1.le) circularAncientBackwardWeight r₀ gseq)
    (hsamples : ∃ N : ℕ, ∀ n ≥ N, ∃ α : CircularConstrainedTangentSpace γ,
      circularConstrainedUnstableProjectionCLM hγ hγ1.le α = α ∧ ‖α‖ ≤ r₀ / 2 ∧
      P.ancient (-(n : ℝ) * (period + period)) = circularConstrainedChart hγ hγ1 (gseq α 0))
    {q T : ℝ} [Fact (1 ≤ ENNReal.ofReal q)]
    (hq : 0 < q) (hqE : 2 ≤ ENNReal.ofReal q) (hT : 0 < T)
    (δmax ηctrl Kextra : ℝ) (hδmax : 0 < δmax) (hηctrl : 0 < ηctrl) (hKextra : 0 ≤ Kextra)
    (hηa : ηctrl ≤ cellA / 16) (hηgap : ηctrl ≤ (1 - cellA) / 16) :
    ∃ b : ℝ≥0, 0 < b ∧ b < 1 / 4 ∧
      bilateral P.moment (((b : ℝ) : ℂ) * (sigma + 5 / 4 * I)) ≠ 0 ∧
      (b : ℝ) * Kextra + (b : ℝ) *
        (finiteInnerLabelLittleRowCoefficient (γ : ℝ) (cellA / 2)
          (circularCanonicalCellNormBudget hγ hγ1) / (2 - 1)) < sigma / 4 ∧
      ∃ δ > 0, δ < δmax ∧ ∃ sCanon < 0, ‖P.coRotatedAncientGraphBase sCanon‖ = δ ∧
      ∃ εtarget > 0, ∃ Ctarget > 0, P.IsSelectedCanonicalCaptureTarget gseq δ sCanon εtarget Ctarget ∧
      ∃ Henv > 0, ∃ Chistory > 0, ∃ c > 0, ∃ Lback > 0, ∃ tmin ≥ 0,
      ∀ tstar ≥ tmin,
        let κ := ‖retardedSol (((b : ℝ) : ℂ) * lamStar)
          (((b : ℝ) : ℂ) * (sigma + 5 / 4 * I)) Kstar P.moment tstar‖ / 2
        let d := tstar - sCanon
        0 < κ ∧ c * Real.exp ((b : ℝ) * sigma * tstar) ≤ κ ∧
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
            Lback + d < D ∧
            ∀ cA > 0, D / cA < T →
            ∀ᶠ ξ : ℝ in atTop,
              P.HasActualCoupledFirstNonzeroTransferFamilyAt (T := T) hq hqE
                b s hs cA D δ sCanon ηctrl Lback (Lback + d) Henv Chistory Cmatch Cback Cb Ccur Cobs κ ξ := by
  obtain ⟨b, hb, hbquarter, hnonzero, hslow, δ, hδ, hδmaxBound, sCanon, hsCanon, hcanonδ,
    εtarget, hεtarget, Ctarget, hCtarget, htarget, Henv, hHenv, Chistory, hChistory, hfamilies⟩ :=
    P.exists_actual_coupled_firstTransfer_selected_input_family hRflow hr₀ hY hd hfix harea hg hsamples
      hq hqE hT δmax ηctrl Kextra hδmax hηctrl hKextra hηa hηgap
  have hbI : (b : ℝ) ∈ Ioo (0 : ℝ) (1 / 4) := ⟨hb, hbquarter⟩
  obtain ⟨c₀, hc₀, Lback, hLback, tmin, htmin, hlate⟩ :=
    P.exists_firstTransfer_uniform_late_response_and_lookback hbI hnonzero hsCanon hChistory.le hηctrl.le
  refine ⟨b, hb, hbquarter, hnonzero, hslow, δ, hδ, hδmaxBound, sCanon, hsCanon, hcanonδ,
    εtarget, hεtarget, Ctarget, hCtarget, htarget, Henv, hHenv, Chistory, hChistory, c₀ / 2, half_pos hc₀,
    Lback, hLback, tmin, htmin, ?_⟩
  intro tstar htstar
  obtain ⟨hdpos, hresponseLower, hlead, htail⟩ := hlate tstar htstar
  let κ₀ := ‖retardedSol (((b : ℝ) : ℂ) * lamStar)
    (((b : ℝ) : ℂ) * (sigma + 5 / 4 * I)) Kstar P.moment tstar‖
  let d := tstar - sCanon
  have hκ₀ : 0 < κ₀ :=
    (mul_pos hc₀ (Real.exp_pos _)).trans_le hresponseLower
  have hhalf : (c₀ / 2) * Real.exp ((b : ℝ) * sigma * tstar) ≤ κ₀ / 2 := by
    convert div_le_div_of_nonneg_right hresponseLower (by norm_num : (0 : ℝ) ≤ 2) using 1 <;> ring
  refine ⟨half_pos hκ₀, hhalf, ?_⟩
  intro seedMax hseedMax nMin
  obtain ⟨n, hn, hdata⟩ := hfamilies Lback hLback d hdpos seedMax hseedMax nMin
  dsimp only at hdata
  obtain ⟨hs, D, hD, Cmatch, hCmatch, Cback, hCback, Cb, hCb, Ccur, hCcur,
    Cobs, hCobs, hseed, hterminal, hDobs, hfamily⟩ := hdata
  let s := -(n : ℝ) * (period + period)
  refine ⟨n, hn, hs, D, hD, Cmatch, hCmatch, Cback, hCback, Cb, hCb, Ccur, hCcur,
    Cobs, hCobs, hseed, hterminal, hDobs, ?_⟩
  intro cA hcA htime
  have hstrengthen := P.eventually_actual_coupled_firstTransfer_nonzero_of_input
    (b := b) (s := s) (cA := cA) (D := D) (δ := δ) (sCanon := sCanon) (ηctrl := ηctrl)
    (Lback := Lback) (d := d) (Henv := Henv) (Chistory := Chistory) (Cmatch := Cmatch)
    (Cback := Cback) (Cb := Cb) (Ccur := Ccur) (Cobs := Cobs) (κ := κ₀) (tstar := tstar)
    hq hqE hb hbquarter hs hcA hT.le hD.le hsCanon hLback hdpos hκ₀ hChistory.le hηctrl.le
    hCb.le hCcur.le hCobs.le rfl (by dsimp only [d]; ring) hlead htail
  filter_upwards [hfamily cA hcA htime, hstrengthen] with ξ hfamilyξ hstrengthenξ
  exact hstrengthenξ hfamilyξ

end CircularMaterialTransferProfile
end Euler2D

end
