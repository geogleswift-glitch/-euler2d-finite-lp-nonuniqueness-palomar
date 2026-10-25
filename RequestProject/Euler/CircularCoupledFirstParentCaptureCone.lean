module

public import RequestProject.Euler.CircularFirstParentCaptureCone
public import RequestProject.Euler.CircularCoupledActualFirstNonzeroTransfer
public import RequestProject.Euler.CircularCoupledActualFirstParentSeed
public import RequestProject.Euler.CircularCoupledActualFirstParentComplement

/-! The original graph cone and chart identity at the end of the SAME
actual parent warmup, retaining R=rho^10 and A0=cA*(1+xi).
The slower complement coefficient precedes the warmup length. -/

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
  circularBanachField circularBanachDomain finiteBaseCurlL2
  CircularMaterialTransferProfile.finiteBaseLp

namespace CircularMaterialTransferProfile

variable {γ : ℝ≥0} {hγ : 0 < γ} {hγ1 : (γ : ℝ) < 1}
    (P : CircularMaterialTransferProfile hγ hγ1)
def HasActualCoupledFirstCaptureConeFamilyAt {q T : ℝ} [Fact (1 ≤ ENNReal.ofReal q)]
    (hq : 0 < q) (hqE : 2 ≤ ENNReal.ofReal q)
    (gseq : CircularConstrainedTangentSpace γ → ℕ → CircularConstrainedTangentSpace γ)
    (b : ℝ≥0) (s : ℝ) (hs : s ≤ 0) (cA D δ sCanon ηctrl Lback Dobs Henv Chistory Cmatch Cback Cb Ccur Cobs κ ξ : ℝ) : Prop :=
  let ρ := Real.exp (-ξ)
  let hρ := Real.exp_pos (-ξ)
  let R := ρ ^ 10
  let hR := pow_pos hρ 10
  let A₀ := cA * (1 + ξ)
  ρ ≤ 1 / 2 ∧ ρ ^ 2 < (b : ℝ) ^ q ∧
  ∀ N : ℕ, 0 < N → D / ampScale A₀ b N < T ∧
    let f := finiteBaseCurlL2 (A₀ := A₀) (b := (b : ℝ)) (ρ := ρ) hR hρ hq hqE
      (P.finiteBaseLp (A₀ := A₀) (b := (b : ℝ)) (ρ := ρ) (q := q) hs hR hρ) N
    ∃ S : BoundedEulerParticleSystem f T,
      IsFourfoldBoundedEulerParticleSystem S ∧
      IsWeakEulerSolution T (biotSavartL2 f) (particleVelocity f S.backward S.backward_area) ∧
      (∀ t ∈ Icc (0 : ℝ) T, MeasurePreserving (S.forward t) volume volume ∧
        MeasurePreserving (S.backward t) volume volume) ∧
      ∃ X : ℝ → FiniteCircularIndex N → LittleContourSpace γ,
        P.ActualCanonicalPrefixTrajectory s A₀ b R ρ (1 / 16) T hR hρ le_rfl S
          (D / ampScale A₀ b N) X ∧
        (∀ τ ∈ Icc (0 : ℝ) D,
          weightedFamilyNorm (2 * ρ ^ 6) N
            (canonicalPrefixStageDeviation hγ hγ1 A₀ b R ρ N 0 X τ) ≤ 1) ∧
        (∀ τ ∈ Icc (0 : ℝ) D,
          ‖canonicalPrefixStageDeviation hγ hγ1 A₀ b R ρ N 0 X τ N‖ ≤ ηctrl) ∧
        (∀ u ∈ Icc (0 : ℝ) D,
          ‖canonicalPrefixAlignedCurrentCell A₀ b R ρ N 0 X u - littleCircularMaterialContours hγ hγ1 u‖ ≤
            Henv * ‖circularConstrainedUnstableProjectionCLM hγ hγ1.le
              (circularConstraintProjectionToTangentCLM hγ hγ1.le
                (P.ancient s - littleCircularReference hγ hγ1))‖ * Real.exp (sigma * u)) ∧
        ∃ τ ∈ Ioc (0 : ℝ) D, Dobs < τ ∧ ∃ angle : ℝ,
          let y := canonicalPrefixAlignedCurrentCell A₀ b R ρ N 0 X
          ‖circularConstrainedUnstableProjectionCLM hγ hγ1.le
            (circularConstraintProjectionToTangentCLM hγ hγ1.le
              (circularCoRotationCLM γ τ (y τ) - littleCircularReference hγ hγ1))‖ = δ ∧
          (∀ u ∈ Ico (0 : ℝ) τ,
            ‖circularConstrainedUnstableProjectionCLM hγ hγ1.le
              (circularConstraintProjectionToTangentCLM hγ hγ1.le
                (circularCoRotationCLM γ u (y u) - littleCircularReference hγ hγ1))‖ < δ) ∧
          (∀ u ∈ Icc (0 : ℝ) τ,
            ‖y u - littleCircularMaterialContours hγ hγ1 u‖ ≤ ηctrl * Real.exp (-sigma * (τ - u))) ∧
          (∀ u ∈ Icc (0 : ℝ) τ,
            let t := physicalTimeFromNormalized (ampScale A₀ b N) 0 u;
            ‖momentN (boxedComplexDensity
              (S.transportedScalar (P.finitePeriodicLabel s A₀ b R ρ N N) t)) 4‖ ≤
              ampScale A₀ b N * radScale R ρ N ^ 6 * Chistory * ηctrl *
                Real.exp (-sigma * (τ - u))) ∧
          ‖circularCoRotationCLM γ τ (y τ) -
            contourRotationFamilyLittleCLM γ angle
              (circularCoRotationCLM γ sCanon (P.ancient sCanon))‖ ≤ Cmatch * ρ ^ 3 ∧
          ‖circularCoRotationCLM γ (τ - Lback) (y (τ - Lback)) -
            contourRotationFamilyLittleCLM γ angle
              (circularCoRotationCLM γ (sCanon - Lback) (P.ancient (sCanon - Lback)))‖ ≤ Cback * ρ ^ 3 ∧
          let entrance := (τ - Lback) / ampScale A₀ b N;
          let Dparent := (b : ℝ) * Dobs;
          let Hparent := entrance + Dparent / ampScale A₀ b (N - 1);
          let h := 2 * ρ ^ 6;
          ∃ Y : ℝ → FiniteCircularIndex (N - 1) → LittleContourSpace γ,
            P.ActualCanonicalPrefixTrajectory s A₀ b R ρ (1 / 16) T hR hρ
              (Nat.sub_le N 1) S Hparent Y ∧
            κ * ρ ^ 6 ≤ ‖canonicalPrefixMaterialGrowingCoordinate hγ hγ1 A₀ b R ρ (N - 1) Y
              (ampScale A₀ b (N - 1) * entrance + (b : ℝ) * Dobs)‖ ∧
            (let Z := canonicalPrefixMaterialCurrentCell A₀ b R ρ (N - 1) Y
                (ampScale A₀ b (N - 1) * entrance + (b : ℝ) * Dobs);
             let v := circularConstraintProjectionToTangentCLM hγ hγ1.le
                (Z - littleCircularReference hγ hγ1);
             let α := circularConstrainedUnstableProjectionCLM hγ hγ1.le v;
             0 < ‖α‖ ∧ ‖v - gseq α 0‖ ≤ ‖α‖ / 32 ∧ circularConstrainedChart hγ hγ1 v = Z) ∧
            (∀ u ∈ Icc (0 : ℝ) Dparent,
              weightedFamilyNorm h (N - 1)
                (canonicalPrefixStageDeviation hγ hγ1 A₀ b R ρ (N - 1) entrance Y u) ≤ Cobs * h) ∧
            (∀ u ∈ Icc (0 : ℝ) Dparent,
              ‖canonicalPrefixStageDeviation hγ hγ1 A₀ b R ρ (N - 1) entrance Y u (N - 1)‖ ≤ Ccur * h) ∧
            (∀ u ∈ Icc (0 : ℝ) Dparent, ∀ z ∈ P.finiteInnerActiveInitialLabels s A₀ b R ρ N (N - 1),
              ‖S.forward (physicalTimeFromNormalized (ampScale A₀ b (N - 1)) entrance u) z - torusCenter‖ ≤
                Cb * ρ * radScale R ρ (N - 1) * (1 + u)) ∧
            (∀ t ∈ Icc (0 : ℝ) entrance, ∀ z ∈ P.finiteInnerActiveInitialLabels s A₀ b R ρ N (N - 1),
              ‖S.forward t z - torusCenter‖ ≤ 2 * ρ * radScale R ρ (N - 1)) ∧
            ∀ t ∈ Icc (0 : ℝ) entrance,
              let x := canonicalPrefixStageDeviation hγ hγ1 A₀ b R ρ (N - 1) 0 Y
                (ampScale A₀ b (N - 1) * t);
              weightedFamilyNorm h (N - 1) x ≤ h ∧ ‖x (N - 1)‖ ≤ h ∧
                (2 ≤ N → ‖x (N - 2)‖ ≤ h ^ 2)

theorem actualCoupledFirstNonzeroFamily_initial_ancient_bound
    {q T : ℝ} [Fact (1 ≤ ENNReal.ofReal q)] (hq : 0 < q) (hqE : 2 ≤ ENNReal.ofReal q)
    (b : ℝ≥0) (s : ℝ) (hs : s ≤ 0)
    (cA D δ sCanon ηctrl Lback Dobs Henv Chistory Cmatch Cback Cb Ccur Cobs κ ξ : ℝ)
    (hD : 0 ≤ D)
    (hfamily : P.HasActualCoupledFirstNonzeroTransferFamilyAt (T := T) hq hqE
      b s hs cA D δ sCanon ηctrl Lback Dobs Henv Chistory Cmatch Cback Cb Ccur Cobs κ ξ) :
    ∀ i, ‖(P.ancient s i).val - circularReferenceC1 hγ hγ1 i‖ ≤ ηctrl := by
  dsimp only [HasActualCoupledFirstNonzeroTransferFamilyAt] at hfamily
  obtain ⟨hhalf, hlp, hfinite⟩ := hfamily
  obtain ⟨htime, S, hS, hweak, harea, X, hX, hweighted, hcur, hrest⟩ := hfinite 1 (by decide)
  have hcur0 := hcur 0 ⟨le_rfl, hD⟩
  rw [P.actualCanonicalPrefix_initial_deepest_deviation (pow_pos (Real.exp_pos (-ξ)) 10) (Real.exp_pos (-ξ))
    1 S X hX] at hcur0
  intro i
  exact (norm_le_pi_norm (P.ancient s - littleCircularReference hγ hγ1) i).trans hcur0

theorem exists_eventually_actualFirstParent_coupled_captureCone_strengthening {Rflow r₀ : ℝ}
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
    {b : ℝ≥0} (hb : 0 < b) (hb1 : b < 1) :
    ∃ ℓ : ℕ, 0 < ℓ ∧ ∃ qc : ℝ, 1 < qc ∧
      qc ^ 2 < circularCaptureBlockMultiplier ℓ ∧ ∃ Ccomp > 0,
      ∀ nWarm : ℕ, ∀ {q T : ℝ}, ∀ [Fact (1 ≤ ENNReal.ofReal q)],
      ∀ (hq : 0 < q) (hqE : 2 ≤ ENNReal.ofReal q),
      ∀ {s cA D δ sCanon ηctrl Lback Dobs Henv Chistory Cmatch Cback Cb Ccur Cobs κ : ℝ},
      ∀ (hs : s ≤ 0) (hcA : 0 < cA), 0 ≤ T → 0 ≤ D →
      0 ≤ ηctrl → ηctrl ≤ cellA / 4 → 0 ≤ Lback → Lback < Dobs →
      0 < Dobs → 0 ≤ Ccur → 0 ≤ Cobs → 0 < κ →
      (b : ℝ) * Dobs = (nWarm : ℝ) * circularCaptureBlockTime ℓ →
      Ccomp * qc ^ nWarm ≤ (κ * ‖circularConstrainedUnstableEmbeddingCLM hγ hγ1.le 1‖) / 32 →
      ∀ᶠ ξ : ℝ in atTop,
        P.HasActualCoupledFirstNonzeroTransferFamilyAt (T := T) hq hqE
          b s hs cA D δ sCanon ηctrl Lback Dobs Henv Chistory Cmatch Cback Cb Ccur Cobs κ ξ →
        P.HasActualCoupledFirstCaptureConeFamilyAt (T := T) hq hqE gseq
          b s hs cA D δ sCanon ηctrl Lback Dobs Henv Chistory Cmatch Cback Cb Ccur Cobs κ ξ := by
  have hbR : 0 < (b : ℝ) := hb
  have hbR1 : (b : ℝ) < 1 := hb1
  obtain ⟨ℓ, hℓ, qc, hqc, hgap, Ccomp, hCcomp, hcomplement⟩ :=
    P.exists_eventually_actualFirstParent_coupled_preCapture_complement
      hRflow hr₀ hflow hd hfix harea hg hbR hbR1
  refine ⟨ℓ, hℓ, qc, hqc, hgap, Ccomp, hCcomp, ?_⟩
  intro nWarm q T _ hq hqE s cA D δ sCanon ηctrl Lback Dobs Henv Chistory Cmatch Cback Cb Ccur Cobs κ
    hs hcA hT hD hηctrl hηa hLback hLobs hDobs hCcur hCobs hκ hWarm hbudget
  by_cases hancient : ∀ i, ‖(P.ancient s i).val - circularReferenceC1 hγ hγ1 i‖ ≤ ηctrl
  · obtain ⟨Cseed, hCseed, hseed⟩ := P.exists_eventually_actualFirstParent_coupled_seed_coordinates
      (Kw := Cobs) (Kcur := Ccur) hbR hCobs hCcur
    have hseedEv := hseed (η := ηctrl) hs hcA hq hqE hT hηctrl hηa hancient
    have hcompEv := hcomplement nWarm (Kw := Cobs) (Kcur := Ccur)
      hs hcA hq hqE hCobs hCcur hT hηctrl hηa hancient
    filter_upwards [hseedEv, hcompEv, eventually_ge_atTop (0 : ℝ)] with ξ hseedξ hcompξ hξ
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
      obtain ⟨hfourZ, hareaZ, hchart, hαrange, hvNorm, hαNorm, hcoordinate, hSeedLower⟩ :=
        hseedξ k S hS hHparent Y hY Hparent ⟨hHparent, le_rfl⟩ σend hclockEnd hownWeighted hownCur
      obtain ⟨hαpos, hαlower⟩ := hSeedLower κ hκ hlower
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
      have hcompAll := hcompξ k S hS hHparent Y hY entrance hentrance htimeWarm
        hweightedWarm hcurWarm hinitParent hstartParent
      have hcompEnd := hcompAll nWarm le_rfl
      have hZgrid : Z = canonicalPrefixAlignedCurrentCell A₀ b R ρ k entrance Y
          ((nWarm : ℝ) * circularCaptureBlockTime ℓ) := by
        dsimp only [Z, σend]
        rw [canonicalPrefixMaterialCurrentCell_eq_coRotatedAligned hA.ne' hbR.ne' R ρ k entrance Dparent Y,
          hDgrid, circularCoRotationCLM_capture_grid]
      have hcompZ : ‖v - gseq α 0‖ ≤ Ccomp * qc ^ nWarm * ρ ^ 6 := by
        dsimp only [v, α]
        rw [hZgrid]
        exact hcompEnd
      have hcone : ‖v - gseq α 0‖ ≤ ‖α‖ / 32 := by
        calc
          _ ≤ Ccomp * qc ^ nWarm * ρ ^ 6 := hcompZ
          _ ≤ ((κ * ‖circularConstrainedUnstableEmbeddingCLM hγ hγ1.le 1‖) / 32) * ρ ^ 6 :=
            mul_le_mul_of_nonneg_right hbudget (pow_nonneg hρ.le 6)
          _ = ((κ * ‖circularConstrainedUnstableEmbeddingCLM hγ hγ1.le 1‖) * ρ ^ 6) / 32 := by ring
          _ ≤ _ := div_le_div_of_nonneg_right hαlower (by norm_num)
      exact ⟨htimeN, S, hS, hweak, hareaS, X, hX, hweighted, hcur, hforward,
        τ, hτ, hlong, angle, hvalue, hbefore, hhistory, hmomentHistory, hmatch, hback,
        Y, hY, hlower, ⟨hαpos, hcone, hchart⟩,
        hweightedY, hcurY, hparticlesY, hparticlesPast, hpast⟩
  · exact Eventually.of_forall fun ξ hfamily => False.elim (hancient
      (P.actualCoupledFirstNonzeroFamily_initial_ancient_bound hq hqE b s hs
        cA D δ sCanon ηctrl Lback Dobs Henv Chistory Cmatch Cback Cb Ccur Cobs κ ξ hD hfamily))


end CircularMaterialTransferProfile
end Euler2D

end
