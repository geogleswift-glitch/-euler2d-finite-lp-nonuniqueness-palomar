module

public import RequestProject.Euler.CircularActualFirstParentComplement
public import RequestProject.Euler.FiniteCaptureEstimates

/-! Choose a true parent return-grid observation before rho so that
the slower original graph complement and the polynomial forcing are
small relative to the same growing seed. -/

@[expose] public section

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

theorem exists_firstParent_return_grid_cone_budget {ℓ : ℕ} (hℓ : 0 < ℓ)
    {qc b Hseed Ccomp Bcapture Lback sCanon tmin : ℝ}
    (hqc : 1 < qc) (hgap : qc ^ 2 < circularCaptureBlockMultiplier ℓ)
    (hb : 0 < b) (hHseed : 0 < Hseed) (hCcomp : 0 ≤ Ccomp) (hBcapture : 0 ≤ Bcapture)
    (nMin : ℕ) :
    ∃ nWarm ≥ nMin, 0 < nWarm ∧
      tmin ≤ (nWarm : ℝ) * circularCaptureBlockTime ℓ / b - Lback + sCanon ∧
      Ccomp * qc ^ nWarm ≤ (Hseed / 32) * circularCaptureBlockMultiplier ℓ ^ nWarm ∧
      Bcapture * (1 + (nWarm : ℝ) * circularCaptureBlockTime ℓ) ^ 4 ≤
        (Hseed / 32) * circularCaptureBlockMultiplier ℓ ^ nWarm := by
  let Tblock := circularCaptureBlockTime ℓ
  let lam := circularCaptureBlockMultiplier ℓ
  have hTblock : 0 < Tblock := circularCaptureBlockTime_pos hℓ
  have hlam : 1 < lam := by
    rw [show lam = Real.exp (sigma * Tblock) from circularCaptureBlockMultiplier_eq_exp ℓ]
    exact Real.one_lt_exp_iff.mpr (mul_pos sigma_pos hTblock)
  have hlam0 : 0 < lam := zero_lt_one.trans hlam
  have hqclam : qc < lam := by nlinarith only [hqc, hgap, sq_nonneg (qc - 1)]
  have hratio0 : 0 ≤ qc / lam := div_nonneg (zero_lt_one.trans hqc).le hlam0.le
  have hratio1 : qc / lam < 1 := (div_lt_one hlam0).mpr hqclam
  have hratio : ∀ᶠ n : ℕ in atTop, Ccomp * (qc / lam) ^ n ≤ Hseed / 32 := by
    have ht := (tendsto_pow_atTop_nhds_zero_of_lt_one hratio0 hratio1).const_mul Ccomp
    simp only [mul_zero] at ht
    exact (ht.eventually (gt_mem_nhds (div_pos hHseed (by norm_num)))).mono (fun _ h => h.le)
  have hpolyLimit := (capture_polynomial_weight_summable hlam 4).tendsto_atTop_zero
  have hpoly : ∀ᶠ n : ℕ in atTop,
      (Bcapture * (1 + Tblock) ^ 4 * lam) * ((1 + (n : ℝ)) ^ 4 / lam ^ (n + 1)) ≤ Hseed / 32 := by
    have ht := hpolyLimit.const_mul (Bcapture * (1 + Tblock) ^ 4 * lam)
    simp only [mul_zero] at ht
    exact (ht.eventually (gt_mem_nhds (div_pos hHseed (by norm_num)))).mono (fun _ h => h.le)
  obtain ⟨nTime, hnTimeBound⟩ := exists_nat_gt ((tmin + Lback - sCanon) * b / Tblock)
  obtain ⟨nWarm, hnMin, hnTime, hnWarm, hratioN, hpolyN⟩ :=
    ((eventually_ge_atTop nMin).and ((eventually_ge_atTop nTime).and
      ((eventually_gt_atTop (0 : ℕ)).and (hratio.and hpoly)))).exists
  have htimeMul : (tmin + Lback - sCanon) * b ≤ (nWarm : ℝ) * Tblock := by
    have h₁ := ((div_lt_iff₀ hTblock).mp hnTimeBound).le
    have h₂ := mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hnTime : (nTime : ℝ) ≤ nWarm) hTblock.le
    exact h₁.trans h₂
  have htimeDiv : tmin + Lback - sCanon ≤ (nWarm : ℝ) * Tblock / b :=
    (le_div_iff₀ hb).mpr htimeMul
  have hcone : Ccomp * qc ^ nWarm ≤ (Hseed / 32) * lam ^ nWarm := by
    apply (div_le_iff₀ (pow_pos hlam0 nWarm)).mp
    simpa only [div_pow, mul_div_assoc] using hratioN
  have hshape : (1 + (nWarm : ℝ) * Tblock) ^ 4 ≤
      (1 + Tblock) ^ 4 * (1 + (nWarm : ℝ)) ^ 4 := by
    have hn0 : 0 ≤ (nWarm : ℝ) := Nat.cast_nonneg _
    have hbase : 1 + (nWarm : ℝ) * Tblock ≤ (1 + Tblock) * (1 + (nWarm : ℝ)) := by
      nlinarith only [hn0, hTblock.le]
    exact (pow_le_pow_left₀ (by positivity) hbase 4).trans_eq (mul_pow _ _ _)
  have hforcing : Bcapture * (1 + (nWarm : ℝ) * Tblock) ^ 4 ≤ (Hseed / 32) * lam ^ nWarm := by
    apply (div_le_iff₀ (pow_pos hlam0 nWarm)).mp
    calc
      _ ≤ Bcapture * ((1 + Tblock) ^ 4 * (1 + (nWarm : ℝ)) ^ 4) / lam ^ nWarm :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hshape hBcapture) (pow_pos hlam0 nWarm).le
      _ = (Bcapture * (1 + Tblock) ^ 4 * lam) *
          ((1 + (nWarm : ℝ)) ^ 4 / lam ^ (nWarm + 1)) := by
        rw [pow_succ]
        field_simp [hlam0.ne']
        <;> ring
      _ ≤ _ := hpolyN
  exact ⟨nWarm, hnMin, hnWarm, by linarith only [htimeDiv], hcone, hforcing⟩

namespace CircularMaterialTransferProfile

variable {γ : ℝ≥0} {hγ : 0 < γ} {hγ1 : (γ : ℝ) < 1}
    (P : CircularMaterialTransferProfile hγ hγ1)
def HasActualFirstCaptureConeFamilyAt {q T : ℝ} [Fact (1 ≤ ENNReal.ofReal q)]
    (hq : 0 < q) (hqE : 2 ≤ ENNReal.ofReal q)
    (gseq : CircularConstrainedTangentSpace γ → ℕ → CircularConstrainedTangentSpace γ)
    (b : ℝ≥0) (s : ℝ) (hs : s ≤ 0) (A₀ D δ sCanon ηctrl Lback Dobs Henv Chistory Cmatch Cback Cb Ccur Cobs κ ξ : ℝ) : Prop :=
  let ρ := Real.exp (-ξ)
  let hρ := Real.exp_pos (-ξ)
  ρ ≤ 1 / 2 ∧ ρ ^ 2 < (b : ℝ) ^ q ∧
  ∀ N : ℕ, 0 < N → D / ampScale A₀ b N < T ∧
    let f := finiteBaseCurlL2 (A₀ := A₀) (b := (b : ℝ)) (ρ := ρ) hρ hρ hq hqE
      (P.finiteBaseLp (A₀ := A₀) (b := (b : ℝ)) (ρ := ρ) (q := q) hs hρ hρ) N
    ∃ S : BoundedEulerParticleSystem f T,
      IsFourfoldBoundedEulerParticleSystem S ∧
      IsWeakEulerSolution T (biotSavartL2 f) (particleVelocity f S.backward S.backward_area) ∧
      (∀ t ∈ Icc (0 : ℝ) T, MeasurePreserving (S.forward t) volume volume ∧
        MeasurePreserving (S.backward t) volume volume) ∧
      ∃ X : ℝ → FiniteCircularIndex N → LittleContourSpace γ,
        P.ActualCanonicalPrefixTrajectory s A₀ b ρ ρ (1 / 16) T hρ hρ le_rfl S
          (D / ampScale A₀ b N) X ∧
        (∀ τ ∈ Icc (0 : ℝ) D,
          weightedFamilyNorm (2 * ρ ^ 6) N
            (canonicalPrefixStageDeviation hγ hγ1 A₀ b ρ ρ N 0 X τ) ≤ 1) ∧
        (∀ τ ∈ Icc (0 : ℝ) D,
          ‖canonicalPrefixStageDeviation hγ hγ1 A₀ b ρ ρ N 0 X τ N‖ ≤ ηctrl) ∧
        (∀ u ∈ Icc (0 : ℝ) D,
          ‖canonicalPrefixAlignedCurrentCell A₀ b ρ ρ N 0 X u - littleCircularMaterialContours hγ hγ1 u‖ ≤
            Henv * ‖circularConstrainedUnstableProjectionCLM hγ hγ1.le
              (circularConstraintProjectionToTangentCLM hγ hγ1.le
                (P.ancient s - littleCircularReference hγ hγ1))‖ * Real.exp (sigma * u)) ∧
        ∃ τ ∈ Ioc (0 : ℝ) D, Dobs < τ ∧ ∃ angle : ℝ,
          let y := canonicalPrefixAlignedCurrentCell A₀ b ρ ρ N 0 X
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
              (S.transportedScalar (P.finitePeriodicLabel s A₀ b ρ ρ N N) t)) 4‖ ≤
              ampScale A₀ b N * radScale ρ ρ N ^ 6 * Chistory * ηctrl *
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
            P.ActualCanonicalPrefixTrajectory s A₀ b ρ ρ (1 / 16) T hρ hρ
              (Nat.sub_le N 1) S Hparent Y ∧
            κ * ρ ^ 6 ≤ ‖canonicalPrefixMaterialGrowingCoordinate hγ hγ1 A₀ b ρ ρ (N - 1) Y
              (ampScale A₀ b (N - 1) * entrance + (b : ℝ) * Dobs)‖ ∧
            (let Z := canonicalPrefixMaterialCurrentCell A₀ b ρ ρ (N - 1) Y
                (ampScale A₀ b (N - 1) * entrance + (b : ℝ) * Dobs);
             let v := circularConstraintProjectionToTangentCLM hγ hγ1.le
                (Z - littleCircularReference hγ hγ1);
             let α := circularConstrainedUnstableProjectionCLM hγ hγ1.le v;
             0 < ‖α‖ ∧ ‖v - gseq α 0‖ ≤ ‖α‖ / 32 ∧ circularConstrainedChart hγ hγ1 v = Z) ∧
            (∀ u ∈ Icc (0 : ℝ) Dparent,
              weightedFamilyNorm h (N - 1)
                (canonicalPrefixStageDeviation hγ hγ1 A₀ b ρ ρ (N - 1) entrance Y u) ≤ Cobs * h) ∧
            (∀ u ∈ Icc (0 : ℝ) Dparent,
              ‖canonicalPrefixStageDeviation hγ hγ1 A₀ b ρ ρ (N - 1) entrance Y u (N - 1)‖ ≤ Ccur * h) ∧
            (∀ u ∈ Icc (0 : ℝ) Dparent, ∀ z ∈ P.finiteInnerActiveInitialLabels s A₀ b ρ ρ N (N - 1),
              ‖S.forward (physicalTimeFromNormalized (ampScale A₀ b (N - 1)) entrance u) z - torusCenter‖ ≤
                Cb * ρ * radScale ρ ρ (N - 1) * (1 + u)) ∧
            (∀ t ∈ Icc (0 : ℝ) entrance, ∀ z ∈ P.finiteInnerActiveInitialLabels s A₀ b ρ ρ N (N - 1),
              ‖S.forward t z - torusCenter‖ ≤ 2 * ρ * radScale ρ ρ (N - 1)) ∧
            ∀ t ∈ Icc (0 : ℝ) entrance,
              let x := canonicalPrefixStageDeviation hγ hγ1 A₀ b ρ ρ (N - 1) 0 Y
                (ampScale A₀ b (N - 1) * t);
              weightedFamilyNorm h (N - 1) x ≤ h ∧ ‖x (N - 1)‖ ≤ h ∧
                (2 ≤ N → ‖x (N - 2)‖ ≤ h ^ 2)

theorem actualFirstNonzeroFamily_initial_ancient_bound
    {q T : ℝ} [Fact (1 ≤ ENNReal.ofReal q)] (hq : 0 < q) (hqE : 2 ≤ ENNReal.ofReal q)
    (b : ℝ≥0) (s : ℝ) (hs : s ≤ 0)
    (A₀ D δ sCanon ηctrl Lback Dobs Henv Chistory Cmatch Cback Cb Ccur Cobs κ ξ : ℝ)
    (hD : 0 ≤ D)
    (hfamily : P.HasActualFirstNonzeroTransferFamilyAt (T := T) hq hqE
      b s hs A₀ D δ sCanon ηctrl Lback Dobs Henv Chistory Cmatch Cback Cb Ccur Cobs κ ξ) :
    ∀ i, ‖(P.ancient s i).val - circularReferenceC1 hγ hγ1 i‖ ≤ ηctrl := by
  dsimp only [HasActualFirstNonzeroTransferFamilyAt] at hfamily
  obtain ⟨hhalf, hlp, hfinite⟩ := hfamily
  obtain ⟨htime, S, hS, hweak, harea, X, hX, hweighted, hcur, hrest⟩ := hfinite 1 (by decide)
  have hcur0 := hcur 0 ⟨le_rfl, hD⟩
  rw [P.actualCanonicalPrefix_initial_deepest_deviation (Real.exp_pos (-ξ)) (Real.exp_pos (-ξ))
    1 S X hX] at hcur0
  intro i
  exact (norm_le_pi_norm (P.ancient s - littleCircularReference hγ hγ1) i).trans hcur0

theorem exists_eventually_actualFirstParent_captureCone_strengthening {Rflow r₀ : ℝ}
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
      ∀ {s A₀ D δ sCanon ηctrl Lback Dobs Henv Chistory Cmatch Cback Cb Ccur Cobs κ : ℝ},
      ∀ (hs : s ≤ 0) (hA : 0 < A₀), 0 ≤ T → 0 ≤ D →
      0 ≤ ηctrl → ηctrl ≤ cellA / 4 → 0 ≤ Lback → Lback < Dobs →
      0 < Dobs → 0 ≤ Ccur → 0 ≤ Cobs → 0 < κ →
      (b : ℝ) * Dobs = (nWarm : ℝ) * circularCaptureBlockTime ℓ →
      Ccomp * qc ^ nWarm ≤ (κ * ‖circularConstrainedUnstableEmbeddingCLM hγ hγ1.le 1‖) / 32 →
      ∀ᶠ ξ : ℝ in atTop,
        P.HasActualFirstNonzeroTransferFamilyAt (T := T) hq hqE
          b s hs A₀ D δ sCanon ηctrl Lback Dobs Henv Chistory Cmatch Cback Cb Ccur Cobs κ ξ →
        P.HasActualFirstCaptureConeFamilyAt (T := T) hq hqE gseq
          b s hs A₀ D δ sCanon ηctrl Lback Dobs Henv Chistory Cmatch Cback Cb Ccur Cobs κ ξ := by
  have hbR : 0 < (b : ℝ) := hb
  have hbR1 : (b : ℝ) < 1 := hb1
  obtain ⟨ℓ, hℓ, qc, hqc, hgap, Ccomp, hCcomp, hcomplement⟩ :=
    P.exists_eventually_actualFirstParent_preCapture_complement
      hRflow hr₀ hflow hd hfix harea hg hbR hbR1
  refine ⟨ℓ, hℓ, qc, hqc, hgap, Ccomp, hCcomp, ?_⟩
  intro nWarm q T _ hq hqE s A₀ D δ sCanon ηctrl Lback Dobs Henv Chistory Cmatch Cback Cb Ccur Cobs κ
    hs hA hT hD hηctrl hηa hLback hLobs hDobs hCcur hCobs hκ hWarm hbudget
  by_cases hancient : ∀ i, ‖(P.ancient s i).val - circularReferenceC1 hγ hγ1 i‖ ≤ ηctrl
  · obtain ⟨Cseed, hCseed, hseed⟩ := P.exists_eventually_actualFirstParent_seed_coordinates
      (Kw := Cobs) (Kcur := Ccur) hbR hCobs hCcur
    have hseedEv := hseed (η := ηctrl) hs hA hq hqE hT hηctrl hηa hancient
    have hcompEv := hcomplement nWarm (Kw := Cobs) (Kcur := Ccur)
      hs hA hq hqE hCobs hCcur hT hηctrl hηa hancient
    filter_upwards [hseedEv, hcompEv] with ξ hseedξ hcompξ
    intro hfamily
    let ρ := Real.exp (-ξ)
    let h := 2 * ρ ^ 6
    have hρ : 0 < ρ := Real.exp_pos (-ξ)
    dsimp only [HasActualFirstNonzeroTransferFamilyAt, HasActualFirstCaptureConeFamilyAt] at hfamily ⊢
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
      let Z := canonicalPrefixMaterialCurrentCell A₀ b ρ ρ k Y σend
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
          canonicalPrefixStageDeviation hγ hγ1 A₀ b ρ ρ k 0 Y (ampScale A₀ b k * entrance + u) j =
            canonicalPrefixStageDeviation hγ hγ1 A₀ b ρ ρ k entrance Y u j :=
        canonicalPrefixStageDeviation_crossPrefix_eq hγ hγ1 hA.ne' hbR.ne' ρ ρ le_rfl Y Y
          (physicalTimeFromNormalized (ampScale A₀ b k) entrance u)
          entrance u 0 (ampScale A₀ b k * entrance + u) rfl (hclock u) (fun _ => rfl) j hj
      have hownWeighted : weightedFamilyNorm h k
          (canonicalPrefixStageDeviation hγ hγ1 A₀ b ρ ρ k 0 Y σend) ≤ Cobs * h := by
        rw [weightedFamilyNorm_congr_prefix h k (fun j => hown Dparent j j.isLt.le)]
        exact hweightedY Dparent ⟨hDparent, le_rfl⟩
      have hownCur : ‖canonicalPrefixStageDeviation hγ hγ1 A₀ b ρ ρ k 0 Y σend k‖ ≤ Ccur * h := by
        rw [hown Dparent k le_rfl]
        exact hcurY Dparent ⟨hDparent, le_rfl⟩
      have hclockEnd : physicalTimeFromNormalized (ampScale A₀ b k) 0 σend = Hparent := hclock Dparent
      obtain ⟨hfourZ, hareaZ, hchart, hαrange, hvNorm, hαNorm, hcoordinate, hSeedLower⟩ :=
        hseedξ k S hS hHparent Y hY Hparent ⟨hHparent, le_rfl⟩ σend hclockEnd hownWeighted hownCur
      obtain ⟨hαpos, hαlower⟩ := hSeedLower κ hκ hlower
      have hinitParent : ‖canonicalPrefixStageDeviation hγ hγ1 A₀ b ρ ρ k entrance Y 0 k‖ ≤ h := by
        rw [← hown 0 k le_rfl]
        have hh := (hpast entrance ⟨hentrance, le_rfl⟩).2.1
        change ‖canonicalPrefixStageDeviation hγ hγ1 A₀ b ρ ρ k 0 Y
          (ampScale A₀ b k * entrance) k‖ ≤ h at hh
        simpa only [add_zero] using hh
      have hstartParent := hparticlesPast entrance ⟨hentrance, le_rfl⟩
      have htimeWarm : entrance + ((nWarm : ℝ) * circularCaptureBlockTime ℓ) / ampScale A₀ b k ≤ Hparent := by
        rw [← hDgrid]
      have hweightedWarm (u : ℝ) (hu : u ∈ Icc (0 : ℝ) ((nWarm : ℝ) * circularCaptureBlockTime ℓ)) :
          weightedFamilyNorm h k (canonicalPrefixStageDeviation hγ hγ1 A₀ b ρ ρ k entrance Y u) ≤ Cobs * h :=
        hweightedY u ⟨hu.1, hu.2.trans_eq hDgrid.symm⟩
      have hcurWarm (u : ℝ) (hu : u ∈ Icc (0 : ℝ) ((nWarm : ℝ) * circularCaptureBlockTime ℓ)) :
          ‖canonicalPrefixStageDeviation hγ hγ1 A₀ b ρ ρ k entrance Y u k‖ ≤ Ccur * h :=
        hcurY u ⟨hu.1, hu.2.trans_eq hDgrid.symm⟩
      have hcompAll := hcompξ k S hS hHparent Y hY entrance hentrance htimeWarm
        hweightedWarm hcurWarm hinitParent hstartParent
      have hcompEnd := hcompAll nWarm le_rfl
      have hZgrid : Z = canonicalPrefixAlignedCurrentCell A₀ b ρ ρ k entrance Y
          ((nWarm : ℝ) * circularCaptureBlockTime ℓ) := by
        dsimp only [Z, σend]
        rw [canonicalPrefixMaterialCurrentCell_eq_coRotatedAligned hA.ne' hbR.ne' ρ ρ k entrance Dparent Y,
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
      (P.actualFirstNonzeroFamily_initial_ancient_bound hq hqE b s hs
        A₀ D δ sCanon ηctrl Lback Dobs Henv Chistory Cmatch Cback Cb Ccur Cobs κ ξ hD hfamily))

theorem exists_actual_firstTransfer_captureCone_family {Rflow r₀ : ℝ}
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
    (ηctrl Kextra : ℝ) (hηctrl : 0 < ηctrl) (hKextra : 0 ≤ Kextra)
    (hηa : ηctrl ≤ cellA / 16) (hηgap : ηctrl ≤ (1 - cellA) / 16) :
    ∃ b : ℝ≥0, 0 < b ∧ b < 1 / 4 ∧
      bilateral P.moment (((b : ℝ) : ℂ) * (sigma + 5 / 4 * I)) ≠ 0 ∧
      (b : ℝ) * Kextra + (b : ℝ) *
        (finiteInnerLabelLittleRowCoefficient (γ : ℝ) (cellA / 2)
          (circularCanonicalCellNormBudget hγ hγ1) / (2 - 1)) < sigma / 4 ∧
      ∃ δ > 0, ∃ sCanon < 0, ‖P.coRotatedAncientGraphBase sCanon‖ = δ ∧
      ∃ Henv > 0, ∃ Chistory > 0, ∃ c > 0, ∃ Lback > 0, ∃ tmin ≥ 0,
      ∃ ℓ : ℕ, 0 < ℓ ∧ ∃ qc : ℝ, 1 < qc ∧ qc ^ 2 < circularCaptureBlockMultiplier ℓ ∧
      ∀ Bcapture : ℝ, 0 ≤ Bcapture → ∀ nWarmMin : ℕ,
      ∃ nWarm ≥ nWarmMin, 0 < nWarm ∧
        let Dobs := (nWarm : ℝ) * circularCaptureBlockTime ℓ / (b : ℝ)
        let tstar := Dobs - Lback + sCanon
        tmin ≤ tstar ∧ 0 < Dobs ∧ Lback < Dobs ∧ ∃ κ > 0,
        c * Real.exp ((b : ℝ) * sigma * tstar) ≤ κ ∧
        Bcapture * (1 + (nWarm : ℝ) * circularCaptureBlockTime ℓ) ^ 4 ≤
          (κ * ‖circularConstrainedUnstableEmbeddingCLM hγ hγ1.le 1‖) / 32 ∧
        ∀ seedMax > 0, ∀ nMin : ℕ, ∃ n ≥ nMin,
          let s := -(n : ℝ) * (period + period)
          ∃ hs : s ≤ 0, ∃ A₀ > 0, ∃ D > 0, ∃ Cmatch > 0, ∃ Cback > 0,
          ∃ Cb > 0, ∃ Ccur > 0, ∃ Cobs > 0,
            ‖circularConstrainedUnstableProjectionCLM hγ hγ1.le
              (circularConstraintProjectionToTangentCLM hγ hγ1.le
                (P.ancient s - littleCircularReference hγ hγ1))‖ < seedMax ∧
            Henv * ‖circularConstrainedUnstableProjectionCLM hγ hγ1.le
              (circularConstraintProjectionToTangentCLM hγ hγ1.le
                (P.ancient s - littleCircularReference hγ hγ1))‖ * Real.exp (sigma * D) ≤ ηctrl ∧
            D / A₀ < T ∧ Dobs < D ∧
            ∀ᶠ ξ : ℝ in atTop,
              P.HasActualFirstCaptureConeFamilyAt (T := T) hq hqE gseq
                b s hs A₀ D δ sCanon ηctrl Lback Dobs Henv Chistory Cmatch Cback Cb Ccur Cobs κ ξ := by
  obtain ⟨b, hb, hbquarter, hnonzero, hslow, δ, hδ, sCanon, hsCanon, hcanonδ,
    Henv, hHenv, Chistory, hChistory, c, hc, Lback, hLback, tmin, htmin, hlate⟩ :=
    P.exists_actual_late_firstTransfer_nonzero_family hRflow hr₀ hflow hd hfix harea hg hsamples
      hq hqE hT ηctrl Kextra hηctrl hKextra hηa hηgap
  have hbR : 0 < (b : ℝ) := hb
  have hb1 : b < 1 := hbquarter.trans (by norm_num)
  obtain ⟨ℓ, hℓ, qc, hqc, hgap, Ccomp, hCcomp, hstrengthen⟩ :=
    P.exists_eventually_actualFirstParent_captureCone_strengthening hRflow hr₀ hflow hd hfix harea hg hb hb1
  let m := ‖circularConstrainedUnstableEmbeddingCLM hγ hγ1.le 1‖
  have hm : 0 < m := norm_circularConstrainedUnstableEmbedding_one_pos hγ hγ1.le
  let Hseed := c * m * Real.exp ((b : ℝ) * sigma * (sCanon - Lback))
  have hHseed : 0 < Hseed := mul_pos (mul_pos hc hm) (Real.exp_pos _)
  have hηquarter : ηctrl ≤ cellA / 4 := hηa.trans (by linarith only [cellA_pos])
  refine ⟨b, hb, hbquarter, hnonzero, hslow, δ, hδ, sCanon, hsCanon, hcanonδ,
    Henv, hHenv, Chistory, hChistory, c, hc, Lback, hLback, tmin, htmin,
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
  obtain ⟨hκ, hκlower, hsamplesLate⟩ := hlate tstar hstar
  let κ := ‖retardedSol (((b : ℝ) : ℂ) * lamStar)
    (((b : ℝ) : ℂ) * (sigma + 5 / 4 * I)) Kstar P.moment tstar‖ / 2
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
  refine ⟨nWarm, hnWarmMin, hnWarm, hstar, hDobs, hLobs, κ, hκ, hκlower, hforcing, ?_⟩
  intro seedMax hseedMax nMin
  obtain ⟨n, hn, hdata⟩ := hsamplesLate seedMax hseedMax nMin
  dsimp only at hdata
  obtain ⟨hs, A₀, hA, D, hD, Cmatch, hCmatch, Cback, hCback, Cb, hCb, Ccur, hCcur,
    Cobs, hCobs, hseed, hterminal, htime, hDobsD, hfamily⟩ := hdata
  rw [hobsEq] at hDobsD hfamily
  let s := -(n : ℝ) * (period + period)
  have hstrengthenEv := hstrengthen nWarm hq hqE
    (s := s) (A₀ := A₀) (D := D) (δ := δ) (sCanon := sCanon) (ηctrl := ηctrl)
    (Lback := Lback) (Dobs := Dobs) (Henv := Henv) (Chistory := Chistory)
    (Cmatch := Cmatch) (Cback := Cback) (Cb := Cb) (Ccur := Ccur) (Cobs := Cobs) (κ := κ)
    hs hA hT.le hD.le hηctrl.le hηquarter hLback.le hLobs hDobs hCcur.le hCobs.le hκ hWarm hbudget
  refine ⟨n, hn, hs, A₀, hA, D, hD, Cmatch, hCmatch, Cback, hCback, Cb, hCb, Ccur, hCcur,
    Cobs, hCobs, hseed, hterminal, htime, hDobsD, ?_⟩
  filter_upwards [hfamily, hstrengthenEv] with ξ hfamilyξ hstrengthenξ
  exact hstrengthenξ hfamilyξ

end CircularMaterialTransferProfile
end Euler2D

end
