module

public import RequestProject.Euler.CircularCoupledSelectedFirstTransferFamily
public import RequestProject.Euler.CircularCoupledSelectedTargetRadiusBudget

public import RequestProject.Euler.CircularSelectedFirstTransferFamily
public import RequestProject.Euler.CircularCoupledSelectedDeepestMatchedLookbackFamily
public import RequestProject.Euler.CircularCoupledDeepestEarlierEntry
public import RequestProject.Euler.CircularCoupledFirstParentWindow

/-! The original selected target and SAME-S first transfer input family
with A0=cA*(1+xi), R=rho^10. Every normalized matching, current, ancestor
and particle constant is selected BEFORE cA. Literal whole-past moment
history and the h^2 cross-prefix floor are retained. -/

@[expose] public section

set_option maxHeartbeats 32000000
set_option maxRecDepth 7500

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

theorem exists_actual_coupled_firstTransfer_selected_input_family_with_target_radius_budget {Rflow r₀ : ℝ}
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
    (targetFactor : ℝ) (hTargetFactor : 0 ≤ targetFactor)
    (δmax ηctrl Kextra : ℝ) (hδmax : 0 < δmax) (hηctrl : 0 < ηctrl) (hKextra : 0 ≤ Kextra)
    (hηa : ηctrl ≤ cellA / 16) (hηgap : ηctrl ≤ (1 - cellA) / 16) :
    ∃ b : ℝ≥0, 0 < b ∧ b < 1 / 4 ∧
      bilateral P.moment (((b : ℝ) : ℂ) * (sigma + 5 / 4 * I)) ≠ 0 ∧
      (b : ℝ) * Kextra + (b : ℝ) *
        (finiteInnerLabelLittleRowCoefficient (γ : ℝ) (cellA / 2)
          (circularCanonicalCellNormBudget hγ hγ1) / (2 - 1)) < sigma / 4 ∧
      ∃ δ > 0, δ < δmax ∧ ∃ sCanon < 0, ‖P.coRotatedAncientGraphBase sCanon‖ = δ ∧
      ∃ εtarget > 0, ∃ Ctarget > 0, P.IsSelectedCanonicalCaptureTarget gseq δ sCanon εtarget Ctarget ∧
      targetFactor * δ < εtarget ∧ ∃ Henv > 0, ∃ Chistory > 0,
        ∀ Lback > 0, ∀ d > 0, ∀ seedMax > 0, ∀ nMin : ℕ, ∃ n ≥ nMin,
          let s := -(n : ℝ) * (period + period);
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
              P.HasActualCoupledFirstTransferInputFamilyAt (T := T) hq hqE
                b s hs cA D δ sCanon ηctrl Lback (Lback + d) Henv Chistory Cmatch Cback Cb Ccur Cobs ξ := by
  obtain ⟨Kself, hKself, hparentSetup⟩ := P.exists_actualCoupledDeepest_parent_window_setup
  let Ksum := Kextra + (Kself : ℝ)
  have hKsum : 0 ≤ Ksum := add_nonneg hKextra (NNReal.coe_nonneg Kself)
  obtain ⟨b, hb, hbquarter, hnonzero, hslowSum, δ, hδ, hδmaxBound, sCanon, hsCanon, hcanonδ,
    εtarget, hεtarget, Ctarget, hCtarget, htarget, hTargetRadius, Henv, hHenv, Chistory, hChistory, hfamilies⟩ :=
    P.exists_actual_coupled_deepest_matched_family_with_selected_target_with_target_radius_budget
      hRflow hr₀ hY hd hfix harea hg hsamples hq hqE hT targetFactor hTargetFactor δmax ηctrl Ksum hδmax hηctrl hKsum
  have hbR : 0 < (b : ℝ) := hb
  have hb1 : b < 1 := hbquarter.trans (by norm_num)
  have hslowExtra : (b : ℝ) * Kextra + (b : ℝ) *
      (finiteInnerLabelLittleRowCoefficient (γ : ℝ) (cellA / 2)
        (circularCanonicalCellNormBudget hγ hγ1) / (2 - 1)) < sigma / 4 := by
    have hp := mul_nonneg hbR.le (NNReal.coe_nonneg Kself)
    dsimp only [Ksum] at hslowSum
    nlinarith only [hslowSum, hp]
  have hslowParent : (b : ℝ) * Kself + (b : ℝ) *
      (finiteInnerLabelLittleRowCoefficient (γ : ℝ) (cellA / 2)
        (circularCanonicalCellNormBudget hγ hγ1) / (2 - 1)) < sigma / 4 := by
    have hp := mul_nonneg hbR.le hKextra
    dsimp only [Ksum] at hslowSum
    nlinarith only [hslowSum, hp]
  refine ⟨b, hb, hbquarter, hnonzero, hslowExtra, δ, hδ, hδmaxBound, sCanon, hsCanon, hcanonδ,
    εtarget, hεtarget, Ctarget, hCtarget, htarget, hTargetRadius, Henv, hHenv, Chistory, hChistory, ?_⟩
  intro Lback hLback d hd seedMax hseedMax nMin
  obtain ⟨n, hn, hdata⟩ := hfamilies (Lback + d) seedMax hseedMax nMin
  dsimp only at hdata
  obtain ⟨hs, D, hD, Cmatch, hCmatch, hseed, hterminal, hfamily⟩ := hdata
  let s := -(n : ℝ) * (period + period)
  let cA₀ := 2 * (D + 1) / T
  have hcA₀ : 0 < cA₀ := div_pos (by linarith only [hD]) hT
  have htime₀ : D / cA₀ < T := by
    have heq : cA₀ * T = 2 * (D + 1) := by dsimp only [cA₀]; field_simp
    apply (div_lt_iff₀ hcA₀).mpr
    nlinarith only [heq, hD]
  have hDobs : Lback + d < D := by
    obtain ⟨ξ₀, hfamily₀⟩ := (hfamily cA₀ hcA₀ htime₀).exists
    dsimp only [HasActualCoupledDeepestMatchedLookbackFamilyAt] at hfamily₀
    obtain ⟨_hρ₀, _hlp₀, hfinite₀⟩ := hfamily₀
    obtain ⟨_htime₀, S₀, _hS₀, _hweak₀, _harea₀, X₀, _hX₀, _hZ₀, _hcur₀, _hforward₀,
      τ₀, hτ₀, hlong₀, _hrest₀⟩ := hfinite₀ 0
    exact hlong₀.trans_le hτ₀.2
  have hηquarter : ηctrl ≤ cellA / 4 := by linarith only [hηa, cellA_pos]
  obtain ⟨Cback, hCback, hearlier⟩ := P.exists_eventually_actualCoupledDeepest_earlier_section_match
    hsCanon.le hbR hb1.le hD.le hηctrl hηquarter hCmatch.le hLback
  obtain ⟨Cb, hCb, Ccur, hCcur, Cobs, hCobs, hparent⟩ :=
    hparentSetup b hb hbquarter hslowParent hD (add_pos hLback hd) hDobs.le
      hηctrl hηa hηgap
  refine ⟨n, hn, hs, D, hD, Cmatch, hCmatch, Cback, hCback,
    Cb, hCb, Ccur, hCcur, Cobs, hCobs, hseed, hterminal, hDobs, ?_⟩
  intro cA hcA hTimeBase
  filter_upwards [hfamily cA hcA hTimeBase,
    hearlier hs hcA hq hqE hT.le, hparent hs hcA hq hqE hTimeBase] with ξ hfamilyξ hearlierξ hparentξ
  let ρ := Real.exp (-ξ)
  change ρ ≤ 1 / 2 ∧ ρ ^ 2 < (b : ℝ) ^ q ∧ _ at hfamilyξ
  obtain ⟨hρhalf, hlp, hfinite⟩ := hfamilyξ
  change ρ ≤ 1 / 2 ∧ ρ ^ 2 < (b : ℝ) ^ q ∧ _
  refine ⟨hρhalf, hlp, ?_⟩
  intro N hN
  obtain ⟨htimeN, S, hS, hweak, hareaS, X, hX, hweighted, hcur, hforward,
    τ, hτ, hlong, angle, hvalue, hbefore, hhistory, hmomentHistory, hmatch⟩ := hfinite N
  have hτL : τ ∈ Icc Lback D := ⟨by linarith only [hlong, hd], hτ.2⟩
  have hback := hearlierξ N S hS X hX hweighted hcur τ angle hτL hmatch
  have he : τ - Lback ∈ Ioc (0 : ℝ) D := by
    constructor
    · linarith only [hlong, hd]
    · linarith only [hτ.2, hLback]
  obtain ⟨Y, hY, hweightedY, hcurY, hparticlesY, hparticlesPast, hpast⟩ :=
    hparentξ N hN S hS X hX hweighted hcur (τ - Lback) he
  exact ⟨htimeN, S, hS, hweak, hareaS, X, hX, hweighted, hcur, hforward,
    τ, hτ, hlong, angle, hvalue, hbefore, hhistory, hmomentHistory, hmatch, hback,
    Y, hY, hweightedY, hcurY, hparticlesY, hparticlesPast, hpast⟩

end CircularMaterialTransferProfile
end Euler2D

end
