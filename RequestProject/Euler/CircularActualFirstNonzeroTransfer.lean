module

public import RequestProject.Euler.CircularActualDeepestMatchedFamily
public import RequestProject.Euler.CircularActualFirstParentComparison
public import RequestProject.Euler.CircularRetardedLookbackTail
public import RequestProject.Euler.CircularCanonicalMomentHistory
public import RequestProject.Euler.CircularCanonicalPrefixConstraints
public import RequestProject.Euler.CircularActualCanonicalSectionMatching

/-! At the genuine first co-rotated section, the same finite Euler
trajectory is close to one fixed negative-time section of the original
ancient profile. The canonical section and error coefficient precede
the shrinking scale and every finite cutoff. -/

@[expose] public section

set_option maxHeartbeats 64000000
set_option maxRecDepth 10000

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

def HasActualFirstNonzeroTransferFamilyAt {q T : ℝ} [Fact (1 ≤ ENNReal.ofReal q)]
    (hq : 0 < q) (hqE : 2 ≤ ENNReal.ofReal q)
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


theorem exists_firstTransfer_response_and_lookback
    {b sCanon Chistory ηctrl : ℝ} (hb : b ∈ Ioo (0 : ℝ) (1 / 4))
    (hbilateral : bilateral P.moment ((b : ℂ) * (sigma + 5 / 4 * I)) ≠ 0)
    (hsCanon : sCanon < 0) (hChistory : 0 ≤ Chistory) (hηctrl : 0 ≤ ηctrl) :
    ∃ tstar ≥ 0, ∃ d > 0, sCanon + d = tstar ∧
      ∃ κ > 0,
        ‖retardedSol ((b : ℂ) * lamStar) ((b : ℂ) * (sigma + 5 / 4 * I)) Kstar P.moment tstar‖ = κ ∧
      ∃ Lback > 0,
        ((‖Kstar‖ * Chistory * ηctrl) / (sigma - b * sigma) * Real.exp (b * sigma * d)) *
          Real.exp (-(sigma - b * sigma) * Lback) ≤ κ / 8 ∧
        ∀ ρ : ℝ, 0 ≤ ρ →
          ‖retardedSol ((b : ℂ) * lamStar) ((b : ℂ) * (sigma + 5 / 4 * I))
            ((ρ : ℂ) ^ 6 * Kstar) P.moment (sCanon - Lback)‖ *
              Real.exp (b * sigma * (Lback + d)) ≤ (κ / 8) * ρ ^ 6 := by
  obtain ⟨tstar, htstar, hnonzero⟩ := P.exists_nonzero_retarded_time (ρ := 1) hb hbilateral (by norm_num)
  have hnonzero' : retardedSol ((b : ℂ) * lamStar) ((b : ℂ) * (sigma + 5 / 4 * I))
      Kstar P.moment tstar ≠ 0 := by
    simpa only [Complex.ofReal_one, one_pow, one_mul] using hnonzero
  let κ := ‖retardedSol ((b : ℂ) * lamStar) ((b : ℂ) * (sigma + 5 / 4 * I)) Kstar P.moment tstar‖
  have hκ : 0 < κ := norm_pos_iff.mpr hnonzero'
  let d := tstar - sCanon
  have hd : 0 < d := by dsimp only [d]; linarith only [htstar, hsCanon]
  have hb1 : b < 1 := hb.2.trans (by norm_num)
  have hgap : 0 < sigma - b * sigma := by
    rw [show sigma - b * sigma = sigma * (1 - b) by ring]
    exact mul_pos sigma_pos (sub_pos.mpr hb1)
  let Atail := ((‖Kstar‖ * Chistory * ηctrl) / (sigma - b * sigma)) * Real.exp (b * sigma * d)
  have harg : Tendsto (fun L : ℝ => (sigma - b * sigma) * L) atTop atTop :=
    (tendsto_const_mul_atTop_of_pos hgap).2 tendsto_id
  have hlim : Tendsto (fun L : ℝ => Atail * Real.exp (-(sigma - b * sigma) * L)) atTop (𝓝 0) := by
    have hh := (Real.tendsto_exp_neg_atTop_nhds_zero.comp harg).const_mul Atail
    simpa only [Function.comp_def, neg_mul, mul_zero] using hh
  have hsmall : ∀ᶠ L : ℝ in atTop, Atail * Real.exp (-(sigma - b * sigma) * L) ≤ κ / 8 :=
    (hlim.eventually (gt_mem_nhds (div_pos hκ (by norm_num)))).mono (fun _ h => h.le)
  have htail := P.eventually_retarded_lookback_tail_uniform_rho hb (div_pos hκ (by norm_num : (0 : ℝ) < 8)) sCanon d
  obtain ⟨Lback, hLback, hlead, htailL⟩ :=
    ((eventually_gt_atTop (0 : ℝ)).and (hsmall.and htail)).exists
  exact ⟨tstar, htstar, d, hd, by dsimp only [d]; ring, κ, hκ, rfl, Lback, hLback, hlead, htailL⟩

theorem eventually_actual_firstTransfer_nonzero_of_input
    {q T : ℝ} [Fact (1 ≤ ENNReal.ofReal q)]
    (hq : 0 < q) (hqE : 2 ≤ ENNReal.ofReal q)
    {b : ℝ≥0} (hb : 0 < b) (hbquarter : b < 1 / 4)
    {s A₀ D δ sCanon ηctrl Lback d Henv Chistory Cmatch Cback Cb Ccur Cobs κ tstar : ℝ}
    (hs : s ≤ 0) (hA : 0 < A₀) (hT : 0 ≤ T) (hD : 0 ≤ D)
    (hsCanon : sCanon < 0) (hLback : 0 < Lback) (hd : 0 < d) (hκ : 0 < κ)
    (hChistory : 0 ≤ Chistory) (hηctrl : 0 ≤ ηctrl)
    (hCb : 0 ≤ Cb) (hCcur : 0 ≤ Ccur) (hCobs : 0 ≤ Cobs)
    (hresponse : ‖retardedSol (((b : ℝ) : ℂ) * lamStar)
      (((b : ℝ) : ℂ) * (sigma + 5 / 4 * I)) Kstar P.moment tstar‖ = κ)
    (htarget : sCanon + d = tstar)
    (hlead : ((‖Kstar‖ * Chistory * ηctrl) / (sigma - (b : ℝ) * sigma) *
        Real.exp ((b : ℝ) * sigma * d)) * Real.exp (-(sigma - (b : ℝ) * sigma) * Lback) ≤ κ / 8)
    (htail : ∀ ρ : ℝ, 0 ≤ ρ →
      ‖retardedSol (((b : ℝ) : ℂ) * lamStar) (((b : ℝ) : ℂ) * (sigma + 5 / 4 * I))
        ((ρ : ℂ) ^ 6 * Kstar) P.moment (sCanon - Lback)‖ *
          Real.exp ((b : ℝ) * sigma * (Lback + d)) ≤ (κ / 8) * ρ ^ 6) :
    ∀ᶠ ξ : ℝ in atTop,
      P.HasActualFirstTransferInputFamilyAt (T := T) hq hqE b s hs A₀ D δ sCanon ηctrl
        Lback (Lback + d) Henv Chistory Cmatch Cback Cb Ccur Cobs ξ →
      P.HasActualFirstNonzeroTransferFamilyAt (T := T) hq hqE b s hs A₀ D δ sCanon ηctrl
        Lback (Lback + d) Henv Chistory Cmatch Cback Cb Ccur Cobs (κ / 2) ξ := by
  let br : ℝ := b
  let Dobs := Lback + d
  have hbR : 0 < br := hb
  have hbqR : br < 1 / 4 := hbquarter
  have hbI : br ∈ Ioo (0 : ℝ) (1 / 4) := ⟨hbR, hbqR⟩
  have hb1 : br < 1 := hbqR.trans (by norm_num)
  have hDobs : 0 < Dobs := add_pos hLback hd
  have hbsigma : 0 ≤ br * sigma := mul_nonneg hbR.le sigma_pos.le
  obtain ⟨Cpast, hCpast, hpastEstimate⟩ := P.exists_eventually_actualFirstParent_physical_lookback_history
    hbR hb1 hChistory hηctrl
  obtain ⟨Cfuture, hCfuture, hcomparison⟩ := P.exists_eventually_actualFirstParent_retarded_comparison
    (Cb := Cb) (Kw := Cobs) (Kcur := Ccur) hbI hCb hCobs hCcur
  let Eamp := Real.exp (br * sigma * Dobs)
  let Bobs := Cfuture * Dobs * Eamp
  let ηobs := (κ / 8) / (Bobs + 1)
  have hBobs : 0 ≤ Bobs := by dsimp only [Bobs, Eamp]; positivity
  have hηobs : 0 < ηobs := div_pos (div_pos hκ (by norm_num)) (by linarith only [hBobs])
  have hηeq : ηobs * (Bobs + 1) = κ / 8 := by
    dsimp only [ηobs]
    exact div_mul_cancel₀ _ (by positivity : Bobs + 1 ≠ 0)
  have hηbudget : Bobs * ηobs ≤ κ / 8 := by nlinarith only [hηeq, hηobs.le]
  have hsObs : sCanon - Lback ≤ 0 := by linarith only [hsCanon, hLback]
  have hobserve := P.eventually_actualFirstParent_observed_child_moment
    (sObs := sCanon - Lback) (Dobs := Dobs) (Cw := Cobs) (Ccur := Ccur) (Cback := Cback) (η := ηobs)
    hsObs hs hA hbR hb1.le hq hqE hT hDobs.le hCobs hCcur hηobs
  let Kpast := Cpast * D * Real.exp (br * sigma * (D + d))
  let Kfuture := Cfuture * (1 + br * Dobs) ^ 8 * Dobs * Eamp
  have hKpast : 0 ≤ Kpast := by dsimp only [Kpast]; positivity
  have hKfuture : 0 ≤ Kfuture := by dsimp only [Kfuture, Eamp]; positivity
  have hresidual : ∀ᶠ ξ : ℝ in atTop, (Kpast + Kfuture) * Real.exp (-ξ) ^ 2 ≤ κ / 8 := by
    have ht : Tendsto (fun ξ : ℝ => (Kpast + Kfuture) * Real.exp (-ξ) ^ 2) atTop (𝓝 0) := by
      simpa only [zero_pow (by decide : 2 ≠ 0), mul_zero] using
        (Real.tendsto_exp_neg_atTop_nhds_zero.pow 2).const_mul (Kpast + Kfuture)
    exact (ht.eventually (gt_mem_nhds (div_pos hκ (by norm_num)))).mono (fun _ h => h.le)
  filter_upwards [hpastEstimate hs hA hq hqE hT,
    hcomparison (Dobs := Dobs) hs hA hq hqE hT hDobs.le, hobserve, hresidual]
    with ξ hpastξ hcomparisonξ hobserveξ hresidualξ
  intro hbase
  let ρ := Real.exp (-ξ)
  let h := 2 * ρ ^ 6
  have hρ : 0 < ρ := Real.exp_pos (-ξ)
  dsimp only [HasActualFirstTransferInputFamilyAt, HasActualFirstNonzeroTransferFamilyAt] at hbase ⊢
  obtain ⟨hρhalf, hlp, hfinite⟩ := hbase
  refine ⟨hρhalf, hlp, ?_⟩
  intro N hN
  cases N with
  | zero => omega
  | succ k =>
    obtain ⟨htimeN, S, hS, hweak, hareaS, X, hX, hweighted, hcur, hforward,
      τ, hτ, hlong, angle, hvalue, hbefore, hhistory, hmomentHistory, hmatch, hback,
      Y, hY, hweightedY, hcurY, hparticlesY, hparticlesPast, hpast⟩ := hfinite (k + 1) (Nat.succ_pos k)
    have hAmp : 0 < ampScale A₀ br (k + 1) := div_pos hA (pow_pos hbR (k + 1))
    have hAmpParent : 0 < ampScale A₀ br k := div_pos hA (pow_pos hbR k)
    let entrance := (τ - Lback) / ampScale A₀ br (k + 1)
    let Hparent := entrance + br * Dobs / ampScale A₀ br k
    let σ₀ := ampScale A₀ br k * entrance
    let W := fun u : ℝ => canonicalPrefixMaterialGrowingCoordinate hγ hγ1 A₀ br ρ ρ k Y (σ₀ + br * u)
    let θp := entrance * finiteAncestorAngularVelocity A₀ br k
    let θc := entrance * finiteAncestorAngularVelocity A₀ br (k + 1) + angle
    let R := P.shiftedRetardedTransfer br ρ θp θc (sCanon - Lback)
    let ε := Cfuture * (ρ ^ 8 * (1 + br * Dobs) ^ 8 + ρ ^ 6 * ηobs)
    have hτL : 0 ≤ τ - Lback := by linarith only [hlong, hd]
    have hτLD : τ - Lback ≤ D := by linarith only [hτ.2, hLback]
    have hentrance : 0 ≤ entrance := div_nonneg hτL hAmp.le
    have hentranceH : entrance ≤ Hparent :=
      le_add_of_nonneg_right (div_nonneg (mul_nonneg hbR.le hDobs.le) hAmpParent.le)
    have hHparent : 0 ≤ Hparent := hentrance.trans hentranceH
    have hHchild : 0 ≤ D / ampScale A₀ br (k + 1) := div_nonneg hD hAmp.le
    have hentranceChild : entrance ∈ Icc (0 : ℝ) (D / ampScale A₀ br (k + 1)) :=
      ⟨hentrance, div_le_div_of_nonneg_right hτLD hAmp.le⟩
    have hclockEntrance : physicalTimeFromNormalized (ampScale A₀ br (k + 1)) 0 (τ - Lback) = entrance := by
      simp only [physicalTimeFromNormalized, zero_add, entrance]
    have hsigma0 : σ₀ = br * (τ - Lback) := by
      dsimp only [σ₀, entrance]
      rw [ampScale_succ_eq_div]
      field_simp [hAmpParent.ne', hbR.ne'] <;> ring
    have hW0 : W 0 = canonicalPrefixMaterialGrowingCoordinate hγ hγ1 A₀ br ρ ρ k Y (br * (τ - Lback)) := by
      dsimp only [W]
      rw [mul_zero, add_zero, hsigma0]
    have hwindowArg (u : ℝ) (hu : u ∈ Icc (0 : ℝ) Dobs) : br * u ∈ Icc (0 : ℝ) (br * Dobs) :=
      ⟨mul_nonneg hbR.le hu.1, mul_le_mul_of_nonneg_left hu.2 hbR.le⟩
    have hweightedObs (u : ℝ) (hu : u ∈ Icc (0 : ℝ) Dobs) :
        weightedFamilyNorm h k (canonicalPrefixStageDeviation hγ hγ1 A₀ br ρ ρ k entrance Y (br * u)) ≤ Cobs * h :=
      hweightedY (br * u) (hwindowArg u hu)
    have hcurObs (u : ℝ) (hu : u ∈ Icc (0 : ℝ) Dobs) :
        ‖canonicalPrefixStageDeviation hγ hγ1 A₀ br ρ ρ k entrance Y (br * u) k‖ ≤ Ccur * h :=
      hcurY (br * u) (hwindowArg u hu)
    have hparticlesObs (u : ℝ) (hu : u ∈ Icc (0 : ℝ) Dobs) :
        ∀ z ∈ P.finiteInnerActiveInitialLabels s A₀ br ρ ρ (k + 1) k,
        ‖S.forward (physicalTimeFromNormalized (ampScale A₀ br k) entrance (br * u)) z - torusCenter‖ ≤
          Cb * ρ * radScale ρ ρ k * (1 + br * u) :=
      hparticlesY (br * u) (hwindowArg u hu)
    have hmomentObs := hobserveξ k S hS hareaS (D / ampScale A₀ br (k + 1)) Hparent
      hHchild hHparent X hX Y hY (τ - Lback) entrance angle hclockEntrance hentranceChild hback
      le_rfl hweightedObs hcurObs
    have hcompareAll := hcomparisonξ k S hS hHparent Y hY entrance angle (sCanon - Lback) ηobs
      hentrance hηobs.le le_rfl hweightedObs hcurObs hparticlesObs hmomentObs
    have hcompare : ‖W Dobs - R Dobs‖ ≤ (‖W 0 - R 0‖ + ε * Dobs) * Eamp :=
      hcompareAll Dobs ⟨hDobs.le, le_rfl⟩
    have hpastBound := hpastξ k S hS hHparent Y hY τ Lback d hLback.le
      (by linarith only [hlong, hd]) hentranceH
      (by intro t ht; exact ⟨(hpast t ht).1, (hpast t ht).2.1⟩)
      hparticlesPast
      (by
        intro u hu
        exact hmomentHistory u ⟨hu.1, hu.2.trans (sub_le_self _ hLback.le)⟩)
    have hleadTerm : (ρ ^ 6 * ‖Kstar‖ * Chistory * ηctrl) / (sigma - br * sigma) *
        Real.exp (-(sigma - br * sigma) * Lback) * Real.exp (br * sigma * d) ≤ (κ / 8) * ρ ^ 6 := by
      calc
        _ = ρ ^ 6 * (((‖Kstar‖ * Chistory * ηctrl) / (sigma - br * sigma) *
            Real.exp (br * sigma * d)) * Real.exp (-(sigma - br * sigma) * Lback)) := by ring
        _ ≤ ρ ^ 6 * (κ / 8) := mul_le_mul_of_nonneg_left hlead (pow_nonneg hρ.le 6)
        _ = _ := by ring
    have htimeProduct : (τ - Lback) * Real.exp (br * sigma * (τ + d)) ≤
        D * Real.exp (br * sigma * (D + d)) := by
      calc
        _ ≤ D * Real.exp (br * sigma * (τ + d)) :=
          mul_le_mul_of_nonneg_right hτLD (Real.exp_pos _).le
        _ ≤ _ := mul_le_mul_of_nonneg_left
          (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (add_le_add hτ.2 le_rfl) hbsigma)) hD
    have hpastTerm : (Cpast * ρ ^ 8) * (τ - Lback) * Real.exp (br * sigma * (τ + d)) ≤ Kpast * ρ ^ 8 := by
      calc
        _ = (Cpast * ρ ^ 8) * ((τ - Lback) * Real.exp (br * sigma * (τ + d))) := by ring
        _ ≤ (Cpast * ρ ^ 8) * (D * Real.exp (br * sigma * (D + d))) :=
          mul_le_mul_of_nonneg_left htimeProduct (by positivity)
        _ = _ := by dsimp only [Kpast]; ring
    have hentryAmp : Eamp * ‖W 0‖ ≤ (κ / 8) * ρ ^ 6 + Kpast * ρ ^ 8 := by
      rw [hW0]
      exact hpastBound.trans (add_le_add hleadTerm hpastTerm)
    have hresponse0 : ‖R 0‖ * Eamp ≤ (κ / 8) * ρ ^ 6 := by
      dsimp only [R]
      rw [P.shiftedRetardedTransfer_norm, add_zero]
      exact htail ρ hρ.le
    have hresponseEnd : ‖R Dobs‖ = ρ ^ 6 * κ := by
      dsimp only [R]
      rw [P.shiftedRetardedTransfer_norm,
        show sCanon - Lback + Dobs = tstar by dsimp only [Dobs]; linarith only [htarget],
        P.norm_retarded_transfer_rho_factor hρ.le, hresponse]
    have hobsTerm : (Bobs * ηobs) * ρ ^ 6 ≤ (κ / 8) * ρ ^ 6 :=
      mul_le_mul_of_nonneg_right hηbudget (pow_nonneg hρ.le 6)
    have hresidualTerm : (Kpast + Kfuture) * ρ ^ 8 ≤ (κ / 8) * ρ ^ 6 := by
      calc
        _ = ((Kpast + Kfuture) * ρ ^ 2) * ρ ^ 6 := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right hresidualξ (pow_nonneg hρ.le 6)
    have herror : ‖W Dobs - R Dobs‖ ≤ (κ / 2) * ρ ^ 6 := by
      calc
        _ ≤ (‖W 0 - R 0‖ + ε * Dobs) * Eamp := hcompare
        _ ≤ (‖W 0‖ + ‖R 0‖ + ε * Dobs) * Eamp :=
          mul_le_mul_of_nonneg_right (add_le_add (norm_sub_le _ _) le_rfl) (Real.exp_pos _).le
        _ = Eamp * ‖W 0‖ + ‖R 0‖ * Eamp + Kfuture * ρ ^ 8 + (Bobs * ηobs) * ρ ^ 6 := by
          dsimp only [ε, Kfuture, Bobs]
          ring
        _ ≤ ((κ / 8) * ρ ^ 6 + Kpast * ρ ^ 8) + (κ / 8) * ρ ^ 6 +
            Kfuture * ρ ^ 8 + (κ / 8) * ρ ^ 6 :=
          add_le_add (add_le_add (add_le_add hentryAmp hresponse0) le_rfl) hobsTerm
        _ = 3 * ((κ / 8) * ρ ^ 6) + (Kpast + Kfuture) * ρ ^ 8 := by ring
        _ ≤ 3 * ((κ / 8) * ρ ^ 6) + (κ / 8) * ρ ^ 6 := add_le_add le_rfl hresidualTerm
        _ = _ := by ring
    have hlower : (κ / 2) * ρ ^ 6 ≤ ‖W Dobs‖ := by
      have htri := norm_sub_norm_le (R Dobs) (W Dobs)
      rw [norm_sub_rev, hresponseEnd] at htri
      nlinarith only [htri, herror]
    exact ⟨htimeN, S, hS, hweak, hareaS, X, hX, hweighted, hcur, hforward,
      τ, hτ, hlong, angle, hvalue, hbefore, hhistory, hmomentHistory, hmatch, hback,
      Y, hY, hlower, hweightedY, hcurY, hparticlesY, hparticlesPast, hpast⟩

theorem exists_actual_firstTransfer_nonzero_family {Rflow r₀ : ℝ}
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
    (ηctrl Kextra : ℝ) (hηctrl : 0 < ηctrl) (hKextra : 0 ≤ Kextra)
    (hηa : ηctrl ≤ cellA / 16) (hηgap : ηctrl ≤ (1 - cellA) / 16) :
    ∃ b : ℝ≥0, 0 < b ∧ b < 1 / 4 ∧
      bilateral P.moment (((b : ℝ) : ℂ) * (sigma + 5 / 4 * I)) ≠ 0 ∧
      (b : ℝ) * Kextra + (b : ℝ) *
        (finiteInnerLabelLittleRowCoefficient (γ : ℝ) (cellA / 2)
          (circularCanonicalCellNormBudget hγ hγ1) / (2 - 1)) < sigma / 4 ∧
      ∃ δ > 0, ∃ sCanon < 0, ‖P.coRotatedAncientGraphBase sCanon‖ = δ ∧ ∃ Henv > 0, ∃ Chistory > 0,
        ∃ Lback > 0, ∃ d > 0, ∃ κ > 0, ∀ seedMax > 0, ∀ nMin : ℕ, ∃ n ≥ nMin,
          let s := -(n : ℝ) * (period + period);
          ∃ hs : s ≤ 0, ∃ A₀ > 0, ∃ D > 0, ∃ Cmatch > 0, ∃ Cback > 0,
          ∃ Cb > 0, ∃ Ccur > 0, ∃ Cobs > 0,
            ‖circularConstrainedUnstableProjectionCLM hγ hγ1.le
              (circularConstraintProjectionToTangentCLM hγ hγ1.le
                (P.ancient s - littleCircularReference hγ hγ1))‖ < seedMax ∧
            Henv * ‖circularConstrainedUnstableProjectionCLM hγ hγ1.le
              (circularConstraintProjectionToTangentCLM hγ hγ1.le
                (P.ancient s - littleCircularReference hγ hγ1))‖ * Real.exp (sigma * D) ≤ ηctrl ∧
            D / A₀ < T ∧ Lback + d < D ∧
            ∀ᶠ ξ : ℝ in atTop,
              P.HasActualFirstNonzeroTransferFamilyAt (T := T) hq hqE
                b s hs A₀ D δ sCanon ηctrl Lback (Lback + d) Henv Chistory Cmatch Cback Cb Ccur Cobs κ ξ := by
  obtain ⟨b, hb, hbquarter, hnonzero, hslow, δ, hδ, sCanon, hsCanon, hcanonδ,
    Henv, hHenv, Chistory, hChistory, hfamilies⟩ :=
    P.exists_actual_firstTransfer_input_family hRflow hr₀ hY hd hfix harea hg hsamples
      hq hqE hT ηctrl Kextra hηctrl hKextra hηa hηgap
  have hbI : (b : ℝ) ∈ Ioo (0 : ℝ) (1 / 4) := ⟨hb, hbquarter⟩
  obtain ⟨tstar, htstar, d, hd, htarget, κ0, hκ0, hresponse, Lback, hLback, hlead, htail⟩ :=
    P.exists_firstTransfer_response_and_lookback hbI hnonzero hsCanon hChistory.le hηctrl.le
  refine ⟨b, hb, hbquarter, hnonzero, hslow, δ, hδ, sCanon, hsCanon, hcanonδ,
    Henv, hHenv, Chistory, hChistory, Lback, hLback, d, hd, κ0 / 2, half_pos hκ0, ?_⟩
  intro seedMax hseedMax nMin
  obtain ⟨n, hn, hdata⟩ := hfamilies Lback hLback d hd seedMax hseedMax nMin
  dsimp only at hdata
  obtain ⟨hs, A₀, hA, D, hD, Cmatch, hCmatch, Cback, hCback, Cb, hCb, Ccur, hCcur,
    Cobs, hCobs, hseed, hterminal, htime, hDobs, hfamily⟩ := hdata
  let s := -(n : ℝ) * (period + period)
  have hstrengthen := P.eventually_actual_firstTransfer_nonzero_of_input
    (b := b) (s := s) (A₀ := A₀) (D := D) (δ := δ) (sCanon := sCanon) (ηctrl := ηctrl)
    (Lback := Lback) (d := d) (Henv := Henv) (Chistory := Chistory) (Cmatch := Cmatch)
    (Cback := Cback) (Cb := Cb) (Ccur := Ccur) (Cobs := Cobs) (κ := κ0) (tstar := tstar)
    hq hqE hb hbquarter hs hA hT.le hD.le hsCanon hLback hd hκ0 hChistory.le hηctrl.le
    hCb.le hCcur.le hCobs.le hresponse htarget hlead htail
  refine ⟨n, hn, hs, A₀, hA, D, hD, Cmatch, hCmatch, Cback, hCback, Cb, hCb, Ccur, hCcur,
    Cobs, hCobs, hseed, hterminal, htime, hDobs, ?_⟩
  filter_upwards [hfamily, hstrengthen] with ξ hfamilyξ hstrengthenξ
  exact hstrengthenξ hfamilyξ

end CircularMaterialTransferProfile
end Euler2D

end
