module

public import RequestProject.Euler.CircularCoupledFirstParentCaptureCone
public import RequestProject.Euler.CircularParentCaptureWarmupBudget

/-! The first-parent entrance family has an actual particle radius with
a coefficient fixed before the warmup. Its future capture source budget
is therefore obtained from the same physical particles without a circular
choice of the observation time. -/

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
  circularBanachField circularBanachDomain finiteBaseCurlL2
  CircularMaterialTransferProfile.finiteBaseLp

namespace CircularMaterialTransferProfile

variable {γ : ℝ≥0} {hγ : 0 < γ} {hγ1 : (γ : ℝ) < 1}
    (P : CircularMaterialTransferProfile hγ hγ1)

theorem actualCoupledFirstCaptureConeFamily_initial_ancient_bound
    {q T : ℝ} [Fact (1 ≤ ENNReal.ofReal q)] (hq : 0 < q) (hqE : 2 ≤ ENNReal.ofReal q)
    (gseq : CircularConstrainedTangentSpace γ → ℕ → CircularConstrainedTangentSpace γ)
    (b : ℝ≥0) (s : ℝ) (hs : s ≤ 0)
    (cA D δ sCanon ηctrl Lback Dobs Henv Chistory Cmatch Cback Cb Ccur Cobs κ ξ : ℝ)
    (hD : 0 ≤ D)
    (hfamily : P.HasActualCoupledFirstCaptureConeFamilyAt (T := T) hq hqE gseq
      b s hs cA D δ sCanon ηctrl Lback Dobs Henv Chistory Cmatch Cback Cb Ccur Cobs κ ξ) :
    ∀ i, ‖(P.ancient s i).val - circularReferenceC1 hγ hγ1 i‖ ≤ ηctrl := by
  dsimp only [HasActualCoupledFirstCaptureConeFamilyAt] at hfamily
  obtain ⟨hhalf, hlp, hfinite⟩ := hfamily
  obtain ⟨htime, S, hS, hweak, harea, X, hX, hweighted, hcur, hrest⟩ := hfinite 1 (by decide)
  have hcur0 := hcur 0 ⟨le_rfl, hD⟩
  rw [P.actualCanonicalPrefix_initial_deepest_deviation (pow_pos (Real.exp_pos (-ξ)) 10) (Real.exp_pos (-ξ))
    1 S X hX] at hcur0
  intro i
  exact (norm_le_pi_norm (P.ancient s - littleCircularReference hγ hγ1) i).trans hcur0

theorem exists_eventually_actualFirstParent_coupled_uniform_particle_strengthening
    {b : ℝ≥0} (hb : 0 < b) (hb1 : b < 1) :
    ∃ Cpre > 0,
      ∀ {q T : ℝ}, ∀ [Fact (1 ≤ ENNReal.ofReal q)],
      ∀ (hq : 0 < q) (hqE : 2 ≤ ENNReal.ofReal q)
        (gseq : CircularConstrainedTangentSpace γ → ℕ → CircularConstrainedTangentSpace γ),
      ∀ {s cA D δ sCanon ηctrl Lback Dobs Henv Chistory Cmatch Cback Cb Ccur Cobs κ : ℝ},
      ∀ (hs : s ≤ 0) (hcA : 0 < cA), 0 ≤ T → 0 ≤ D →
      0 ≤ ηctrl → ηctrl ≤ cellA / 4 → Lback < Dobs → 0 ≤ Dobs →
      0 ≤ Ccur → 0 ≤ Cobs →
      ∀ᶠ ξ : ℝ in atTop,
        P.HasActualCoupledFirstCaptureConeFamilyAt (T := T) hq hqE gseq
          b s hs cA D δ sCanon ηctrl Lback Dobs Henv Chistory Cmatch Cback Cb Ccur Cobs κ ξ →
        P.HasActualCoupledFirstCaptureConeFamilyAt (T := T) hq hqE gseq
          b s hs cA D δ sCanon ηctrl Lback Dobs Henv Chistory Cmatch Cback Cpre Ccur Cobs κ ξ := by
  have hbR : 0 < (b : ℝ) := hb
  have hbR1 : (b : ℝ) < 1 := hb1
  obtain ⟨Cpre, hCpre, Bpoly, hBpoly, Ktorus, hKtorus, εchart, hεchart, hforcing⟩ :=
    P.exists_eventually_actualFirstParent_coupled_preCapture_forcing hbR hbR1
  refine ⟨Cpre, hCpre, ?_⟩
  intro q T _ hq hqE gseq s cA D δ sCanon ηctrl Lback Dobs Henv Chistory
    Cmatch Cback Cb Ccur Cobs κ hs hcA hT hD hη hηa hLobs hDobs hCcur hCobs
  by_cases hancient : ∀ i, ‖(P.ancient s i).val - circularReferenceC1 hγ hγ1 i‖ ≤ ηctrl
  · have hDparent : 0 ≤ (b : ℝ) * Dobs := mul_nonneg hbR.le hDobs
    have hforcingEv := hforcing (D := (b : ℝ) * Dobs) (Kw := Cobs) (Kcur := Ccur)
      hs hcA hq hqE hDparent hCobs hCcur hT hη hηa hancient
    filter_upwards [hforcingEv, eventually_ge_atTop (0 : ℝ)] with ξ hforcingξ hξ
    intro hfamily
    let ρ := Real.exp (-ξ)
    let R := ρ ^ 10
    let A₀ := cA * (1 + ξ)
    have hρ : 0 < ρ := Real.exp_pos (-ξ)
    have hA : 0 < A₀ := mul_pos hcA (by linarith only [hξ])
    dsimp only [HasActualCoupledFirstCaptureConeFamilyAt] at hfamily ⊢
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
      (P.actualCoupledFirstCaptureConeFamily_initial_ancient_bound hq hqE gseq b s hs
        cA D δ sCanon ηctrl Lback Dobs Henv Chistory Cmatch Cback Cb Ccur Cobs κ ξ hD hfamily))


end CircularMaterialTransferProfile
end Euler2D

end
