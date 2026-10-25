module

public import RequestProject.Euler.CircularCoupledFirstParentCaptureCone
public import RequestProject.Euler.CircularCoupledCanonicalCaptureReady

/-! The real arbitrary-cutoff parent produced by the nonzero-window
construction has a genuine graph-cone entrance after a long warmup.
The improved particle coefficient is chosen BEFORE that warmup length,
so its later capture forcing budget has no circular duration choice. -/

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 64000000
set_option maxRecDepth 10000

noncomputable section

open Complex Set Filter Topology MeasureTheory Metric
open scoped NNReal ENNReal ContDiff BigOperators

namespace Euler2D

attribute [local instance 2000] rigidGaugeLittle_group rigidGaugeLittle_space rigidGaugeFamily_tower
attribute [local instance 2000] captureBlockTangent_group captureBlockTangent_space
  captureBlockTangent_continuousAdd captureBlockTangent_space captureBlockEndo_monoid captureBlockTangent_complete
attribute [local instance] LittleContourSpace.complexScalarNormedSpace LittleContourSpace.complexScalarTower
attribute [local irreducible] circularConstrainedTangentSubmodule circularConstrainedUnstableProjectionCLM
  circularConstrainedReturnMap circularConstrainedChart circularConstraintProjectionToTangentCLM
  circularBanachField circularBanachDomain

namespace CircularMaterialTransferProfile

variable {γ : ℝ≥0} {hγ : 0 < γ} {hγ1 : (γ : ℝ) < 1}
    (P : CircularMaterialTransferProfile hγ hγ1)

def ActualCanonicalCaptureReadyWitness
    (gseq : CircularConstrainedTangentSpace γ → ℕ → CircularConstrainedTangentSpace γ)
    (b : ℝ) (ℓ : ℕ) (qc Ccomp Cpre : ℝ) : Prop :=
      ∀ nWarm : ℕ, ∀ {Kw Kcur κ : ℝ}, 0 ≤ Kw → 0 ≤ Kcur → 0 < κ →
      Ccomp * qc ^ nWarm ≤ (κ * ‖circularConstrainedUnstableEmbeddingCLM hγ hγ1.le 1‖) / 32 →
      ∀ {s cA q T η : ℝ}, ∀ [Fact (1 ≤ ENNReal.ofReal q)],
      ∀ (hs : s ≤ 0) (hcA : 0 < cA) (hq : 0 < q) (hqE : 2 ≤ ENNReal.ofReal q),
      0 ≤ T → 0 ≤ η → η ≤ cellA / 4 →
      (∀ i, ‖(P.ancient s i).val - circularReferenceC1 hγ hγ1 i‖ ≤ η) →
      ∀ᶠ ξ : ℝ in atTop,
        let ρ := Real.exp (-ξ)
        let hρ := Real.exp_pos (-ξ)
        let R := ρ ^ 10
        let hR := pow_pos hρ 10
        let A₀ := cA * (1 + ξ)
        let h := 2 * ρ ^ 6
        let D := (nWarm : ℝ) * circularCaptureBlockTime ℓ
        ∀ N k : ℕ, ∀ hkN : k ≤ N,
        ∀ S : BoundedEulerParticleSystem
          (finiteBaseCurlL2 (A₀ := A₀) (b := b) (ρ := ρ) hR hρ hq hqE
            (P.finiteBaseLp (A₀ := A₀) (b := b) (ρ := ρ) (q := q) hs hR hρ) N) T,
        IsFourfoldBoundedEulerParticleSystem S →
        ∀ {H : ℝ}, 0 ≤ H → ∀ Y : ℝ → FiniteCircularIndex k → LittleContourSpace γ,
        P.ActualCanonicalPrefixTrajectory s A₀ b R ρ (1 / 16) T hR hρ hkN S H Y →
        ∀ entrance : ℝ, 0 ≤ entrance → entrance + D / ampScale A₀ b k ≤ H →
        (∀ u ∈ Icc (0 : ℝ) D,
          weightedFamilyNorm h k (canonicalPrefixStageDeviation hγ hγ1 A₀ b R ρ k entrance Y u) ≤ Kw * h) →
        (∀ u ∈ Icc (0 : ℝ) D,
          ‖canonicalPrefixStageDeviation hγ hγ1 A₀ b R ρ k entrance Y u k‖ ≤ Kcur * h) →
        ‖canonicalPrefixStageDeviation hγ hγ1 A₀ b R ρ k entrance Y 0 k‖ ≤ h →
        (∀ z ∈ P.finiteInnerActiveInitialLabels s A₀ b R ρ N k,
          ‖S.forward entrance z - torusCenter‖ ≤ 2 * ρ * radScale R ρ k) →
        κ * ρ ^ 6 ≤ ‖canonicalPrefixMaterialGrowingCoordinate hγ hγ1 A₀ b R ρ k Y
          (ampScale A₀ b k * entrance + D)‖ →
        let Z := canonicalPrefixMaterialCurrentCell A₀ b R ρ k Y (ampScale A₀ b k * entrance + D)
        let v := circularConstraintProjectionToTangentCLM hγ hγ1.le (Z - littleCircularReference hγ hγ1)
        let α := circularConstrainedUnstableProjectionCLM hγ hγ1.le v
        0 < ‖α‖ ∧ ‖v - gseq α 0‖ ≤ ‖α‖ / 32 ∧ circularConstrainedChart hγ hγ1 v = Z ∧
          ∀ u ∈ Icc (0 : ℝ) D, ∀ z ∈ P.finiteInnerActiveInitialLabels s A₀ b R ρ N k,
            ‖S.forward (physicalTimeFromNormalized (ampScale A₀ b k) entrance u) z - torusCenter‖ ≤
              Cpre * ρ * radScale R ρ k * (1 + u)

theorem exists_actualCanonical_captureReady_witness {Rflow r₀ : ℝ}
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
    {b : ℝ} (hb : 0 < b) (hb1 : b < 1) :
    ∃ ℓ : ℕ, 0 < ℓ ∧ ∃ qc : ℝ, 1 < qc ∧
      qc ^ 2 < circularCaptureBlockMultiplier ℓ ∧ ∃ Ccomp > 0, ∃ Cpre > 0,
      P.ActualCanonicalCaptureReadyWitness gseq b ℓ qc Ccomp Cpre := by
  obtain ⟨ℓ, hℓ, qc, hqc, hgap, Ccomp, hCcomp, Cpre, hCpre, hwitness⟩ :=
    P.exists_eventually_actualCanonical_coupled_capture_ready hRflow hr₀ hflow hd hfix harea hg hb hb1
  exact ⟨ℓ, hℓ, qc, hqc, hgap, Ccomp, hCcomp, Cpre, hCpre, hwitness⟩

theorem eventually_actualCoupledFirstNonzero_captureReady_of_witness
    {b : ℝ≥0} (hb : 0 < b)
    {gseq : CircularConstrainedTangentSpace γ → ℕ → CircularConstrainedTangentSpace γ}
    {ℓ : ℕ} {qc Ccomp Cpre : ℝ}
    (hwitness : P.ActualCanonicalCaptureReadyWitness gseq b ℓ qc Ccomp Cpre)
    (nWarm : ℕ) {q T : ℝ} [Fact (1 ≤ ENNReal.ofReal q)]
    (hq : 0 < q) (hqE : 2 ≤ ENNReal.ofReal q)
    {s cA D δ sCanon ηctrl Lback Dobs Henv Chistory Cmatch Cback Cb Ccur Cobs κ : ℝ}
    (hs : s ≤ 0) (hcA : 0 < cA) (hT : 0 ≤ T) (hD : 0 ≤ D)
    (hηctrl : 0 ≤ ηctrl) (hηa : ηctrl ≤ cellA / 4)
    (hLobs : Lback < Dobs) (hDobs : 0 < Dobs)
    (hCcur : 0 ≤ Ccur) (hCobs : 0 ≤ Cobs) (hκ : 0 < κ)
    (hWarm : (b : ℝ) * Dobs = (nWarm : ℝ) * circularCaptureBlockTime ℓ)
    (hbudget : Ccomp * qc ^ nWarm ≤ (κ * ‖circularConstrainedUnstableEmbeddingCLM hγ hγ1.le 1‖) / 32) :
    ∀ᶠ ξ : ℝ in atTop,
      P.HasActualCoupledFirstNonzeroTransferFamilyAt (T := T) hq hqE
        b s hs cA D δ sCanon ηctrl Lback Dobs Henv Chistory Cmatch Cback Cb Ccur Cobs κ ξ →
      P.HasActualCoupledFirstCaptureConeFamilyAt (T := T) hq hqE gseq
        b s hs cA D δ sCanon ηctrl Lback Dobs Henv Chistory Cmatch Cback Cpre Ccur Cobs κ ξ := by
  have hbR : 0 < (b : ℝ) := hb
  by_cases hancient : ∀ i, ‖(P.ancient s i).val - circularReferenceC1 hγ hγ1 i‖ ≤ ηctrl
  · have hreadyEv := hwitness nWarm (Kw := Cobs) (Kcur := Ccur) (κ := κ)
      hCobs hCcur hκ hbudget hs hcA hq hqE hT hηctrl hηa hancient
    filter_upwards [hreadyEv, eventually_ge_atTop (0 : ℝ)] with ξ hreadyξ hξ
    intro hfamily
    let ρ := Real.exp (-ξ)
    let R := ρ ^ 10
    let A₀ := cA * (1 + ξ)
    let h := 2 * ρ ^ 6
    have hρ : 0 < ρ := Real.exp_pos (-ξ)
    have hA : 0 < A₀ := mul_pos hcA (by linarith only [hξ])
    dsimp only [HasActualCoupledFirstNonzeroTransferFamilyAt, HasActualCoupledFirstCaptureConeFamilyAt] at hfamily ⊢
    obtain ⟨hhalf, hlp, hfinite⟩ := hfamily
    refine ⟨hhalf, hlp, ?_⟩
    intro N hN
    cases N with
    | zero => omega
    | succ k =>
      obtain ⟨htimeN, S, hS, hweak, hareaS, X, hX, hweighted, hcur, hforward,
        τ, hτ, hlong, angle, hvalue, hbefore, hhistory, hmomentHistory, hmatch, hback,
        Y, hY, hlower, hweightedY, hcurY, hparticlesY, hparticlesPast, hpast⟩ :=
          hfinite (k + 1) (Nat.succ_pos k)
      have hAmp : 0 < ampScale A₀ b (k + 1) := div_pos hA (pow_pos hbR (k + 1))
      have hAmpParent : 0 < ampScale A₀ b k := div_pos hA (pow_pos hbR k)
      let entrance := (τ - Lback) / ampScale A₀ b (k + 1)
      let Dparent := (b : ℝ) * Dobs
      let Hparent := entrance + Dparent / ampScale A₀ b k
      let σend := ampScale A₀ b k * entrance + Dparent
      let Z := canonicalPrefixMaterialCurrentCell A₀ b R ρ k Y σend
      let J := circularConstraintProjectionToTangentCLM hγ hγ1.le
      let Q := circularConstrainedUnstableProjectionCLM hγ hγ1.le
      let v := J (Z - littleCircularReference hγ hγ1)
      let α := Q v
      have hτL : 0 ≤ τ - Lback := by linarith only [hlong, hLobs]
      have hentrance : 0 ≤ entrance := div_nonneg hτL hAmp.le
      have hDparent : 0 ≤ Dparent := mul_nonneg hbR.le hDobs.le
      have hentranceH : entrance ≤ Hparent := le_add_of_nonneg_right (div_nonneg hDparent hAmpParent.le)
      have hHparent : 0 ≤ Hparent := hentrance.trans hentranceH
      have hDgrid : Dparent = (nWarm : ℝ) * circularCaptureBlockTime ℓ := hWarm
      have hclock (u : ℝ) : physicalTimeFromNormalized (ampScale A₀ b k) 0
          (ampScale A₀ b k * entrance + u) =
            physicalTimeFromNormalized (ampScale A₀ b k) entrance u := by
        unfold physicalTimeFromNormalized
        field_simp [hAmpParent.ne'] <;> ring
      have hown (u : ℝ) (j : ℕ) (hj : j ≤ k) :
          canonicalPrefixStageDeviation hγ hγ1 A₀ b R ρ k 0 Y (ampScale A₀ b k * entrance + u) j =
            canonicalPrefixStageDeviation hγ hγ1 A₀ b R ρ k entrance Y u j :=
        canonicalPrefixStageDeviation_crossPrefix_eq hγ hγ1 hA.ne' hbR.ne' R ρ le_rfl Y Y
          (physicalTimeFromNormalized (ampScale A₀ b k) entrance u)
          entrance u 0 (ampScale A₀ b k * entrance + u) rfl (hclock u) (fun _ => rfl) j hj
      have hownWeighted : weightedFamilyNorm h k
          (canonicalPrefixStageDeviation hγ hγ1 A₀ b R ρ k 0 Y σend) ≤ Cobs * h := by
        rw [weightedFamilyNorm_congr_prefix h k (fun j => hown Dparent j j.isLt.le)]
        exact hweightedY Dparent ⟨hDparent, le_rfl⟩
      have hownCur : ‖canonicalPrefixStageDeviation hγ hγ1 A₀ b R ρ k 0 Y σend k‖ ≤ Ccur * h := by
        rw [hown Dparent k le_rfl]
        exact hcurY Dparent ⟨hDparent, le_rfl⟩
      have hclockEnd : physicalTimeFromNormalized (ampScale A₀ b k) 0 σend = Hparent := hclock Dparent
      have hinitParent : ‖canonicalPrefixStageDeviation hγ hγ1 A₀ b R ρ k entrance Y 0 k‖ ≤ h := by
        rw [← hown 0 k le_rfl]
        have hh := (hpast entrance ⟨hentrance, le_rfl⟩).2.1
        simpa only [add_zero] using hh
      have hstartParent := hparticlesPast entrance ⟨hentrance, le_rfl⟩
      have htimeWarm : entrance + ((nWarm : ℝ) * circularCaptureBlockTime ℓ) / ampScale A₀ b k ≤ Hparent := by
        rw [← hDgrid]
      have hweightedWarm (u : ℝ) (hu : u ∈ Icc (0 : ℝ) ((nWarm : ℝ) * circularCaptureBlockTime ℓ)) :
          weightedFamilyNorm h k (canonicalPrefixStageDeviation hγ hγ1 A₀ b R ρ k entrance Y u) ≤ Cobs * h :=
        hweightedY u ⟨hu.1, hu.2.trans_eq hDgrid.symm⟩
      have hcurWarm (u : ℝ) (hu : u ∈ Icc (0 : ℝ) ((nWarm : ℝ) * circularCaptureBlockTime ℓ)) :
          ‖canonicalPrefixStageDeviation hγ hγ1 A₀ b R ρ k entrance Y u k‖ ≤ Ccur * h :=
        hcurY u ⟨hu.1, hu.2.trans_eq hDgrid.symm⟩
      have hreadyData := hreadyξ (k + 1) k (Nat.le_succ k) S hS hHparent Y hY entrance
        hentrance htimeWarm hweightedWarm hcurWarm hinitParent hstartParent
        (by simpa only [← hDgrid] using hlower)
      rw [← hDgrid] at hreadyData
      obtain ⟨hαpos, hcone, hchart, hpure⟩ := hreadyData
      exact ⟨htimeN, S, hS, hweak, hareaS, X, hX, hweighted, hcur, hforward,
        τ, hτ, hlong, angle, hvalue, hbefore, hhistory, hmomentHistory, hmatch, hback,
        Y, hY, hlower, ⟨hαpos, hcone, hchart⟩,
        hweightedY, hcurY, hpure, hparticlesPast, hpast⟩
  · exact Eventually.of_forall fun ξ hfamily => False.elim (hancient
      (P.actualCoupledFirstNonzeroFamily_initial_ancient_bound hq hqE b s hs
        cA D δ sCanon ηctrl Lback Dobs Henv Chistory Cmatch Cback Cb Ccur Cobs κ ξ hD hfamily))

end CircularMaterialTransferProfile
end Euler2D

end
