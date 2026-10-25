module

public import RequestProject.Euler.CircularActualCapturedChildHandoff
public import RequestProject.Euler.CircularCoupledSharedCaptureReadyWitness

/-! One genuine subsequent transfer. A captured FORCED child's SAME
history constructs the next actual nonzero parent, upgrades it with the
SHARED graph/particle witness, and preserves the real clock invariant.
The Euler system, original scale parameters, target and time are retained. -/

@[expose] public section

set_option autoImplicit false
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
attribute [local irreducible] contourC1GraphSubmodule holderGraphSubmodule
  circularConstrainedTangentSubmodule circularConstrainedUnstableProjectionCLM
  circularConstrainedReturnMap circularConstrainedChart circularConstraintProjectionToTangentCLM
  circularBanachField circularBanachDomain

namespace CircularMaterialTransferProfile

variable {γ : ℝ≥0} {hγ : 0 < γ} {hγ1 : (γ : ℝ) < 1}
    (P : CircularMaterialTransferProfile hγ hγ1)

def HasActualUniformParentWarmupState
    (gseq : CircularConstrainedTangentSpace γ → ℕ → CircularConstrainedTangentSpace γ)
    {s A₀ b R ρ T : ℝ} (hR : 0 < R) (hρ : 0 < ρ)
    {N k : ℕ} (hkN : k ≤ N) {f : Lp ℝ 2 μT}
    (S : BoundedEulerParticleSystem f T)
    (Dpre Cpre Ccur Cobs κ Lentry Dentry ξ : ℝ) : Prop :=
  let h := 2 * ρ ^ 6
  ∃ entrance : ℝ, 0 ≤ entrance ∧
    let H := entrance + Dpre / ampScale A₀ b k
    H < T ∧ ampScale A₀ b k * H ≤ Lentry * ξ + Dentry ∧
    ∃ Y : ℝ → FiniteCircularIndex k → LittleContourSpace γ,
      P.ActualCanonicalPrefixTrajectory s A₀ b R ρ (1 / 16) T hR hρ hkN S H Y ∧
      κ * ρ ^ 6 ≤ ‖canonicalPrefixMaterialGrowingCoordinate hγ hγ1 A₀ b R ρ k Y
        (ampScale A₀ b k * entrance + Dpre)‖ ∧
      (let Z := canonicalPrefixMaterialCurrentCell A₀ b R ρ k Y (ampScale A₀ b k * entrance + Dpre)
       let v := circularConstraintProjectionToTangentCLM hγ hγ1.le (Z - littleCircularReference hγ hγ1)
       let α := circularConstrainedUnstableProjectionCLM hγ hγ1.le v
       0 < ‖α‖ ∧ ‖v - gseq α 0‖ ≤ ‖α‖ / 32 ∧ circularConstrainedChart hγ hγ1 v = Z) ∧
      (∀ u ∈ Icc (0 : ℝ) Dpre,
        weightedFamilyNorm h k (canonicalPrefixStageDeviation hγ hγ1 A₀ b R ρ k entrance Y u) ≤ Cobs * h) ∧
      (∀ u ∈ Icc (0 : ℝ) Dpre,
        ‖canonicalPrefixStageDeviation hγ hγ1 A₀ b R ρ k entrance Y u k‖ ≤ Ccur * h) ∧
      (∀ u ∈ Icc (0 : ℝ) Dpre, ∀ z ∈ P.finiteInnerActiveInitialLabels s A₀ b R ρ N k,
        ‖S.forward (physicalTimeFromNormalized (ampScale A₀ b k) entrance u) z - torusCenter‖ ≤
          Cpre * ρ * radScale R ρ k * (1 + u)) ∧
      (∀ t ∈ Icc (0 : ℝ) entrance, ∀ z ∈ P.finiteInnerActiveInitialLabels s A₀ b R ρ N k,
        ‖S.forward t z - torusCenter‖ ≤ 2 * ρ * radScale R ρ k) ∧
      ∀ t ∈ Icc (0 : ℝ) entrance,
        let x := canonicalPrefixStageDeviation hγ hγ1 A₀ b R ρ k 0 Y (ampScale A₀ b k * t)
        weightedFamilyNorm h k x ≤ h ∧ ‖x k‖ ≤ h ∧
          (2 ≤ k + 1 → ‖x (k + 1 - 2)‖ ≤ h ^ 2)

theorem exists_actualCapturedChild_next_parent_warmup_setup :
    ∃ Kself : ℝ≥0, 0 < Kself ∧
      ∀ b : ℝ≥0, 0 < b → b < 1 / 4 →
      (b : ℝ) * Kself + (b : ℝ) *
        (finiteInnerLabelLittleRowCoefficient (γ : ℝ) (cellA / 2)
          (circularCanonicalCellNormBudget hγ hγ1) / (2 - 1)) < sigma / 4 →
      ∀ {Dobs ηcur : ℝ}, 0 < Dobs →
      0 < ηcur → ηcur ≤ cellA / 16 → ηcur ≤ (1 - cellA) / 16 →
      ∃ Ccur > 0, ∃ Cobs > 0,
      ∀ (gseq : CircularConstrainedTangentSpace γ → ℕ → CircularConstrainedTangentSpace γ)
        (ℓwarm : ℕ) (qcwarm Ccomp Cpre : ℝ) (nwarm : ℕ),
      P.ActualCanonicalCaptureReadyWitness gseq b ℓwarm qcwarm Ccomp Cpre →
      ∀ {sCanon Lback d Ccommon Cmoment Cback κ tstar Lentry Dentry D₀ : ℝ},
      Dobs = Lback + d →
      sCanon < 0 → 0 < Lback → 0 < d → 0 < κ → 0 ≤ Ccommon → Cmoment ≤ Ccommon →
      sigma * (Lentry + 6 / sigma) < 8 →
      (b : ℝ) * (Lentry + 6 / sigma) ≤ Lentry →
      (b : ℝ) * (Dentry + D₀) + (b : ℝ) * Dobs ≤ Dentry →
      (b : ℝ) * Dobs = (nwarm : ℝ) * circularCaptureBlockTime ℓwarm →
      Ccomp * qcwarm ^ nwarm ≤ (κ * ‖circularConstrainedUnstableEmbeddingCLM hγ hγ1.le 1‖) / 32 →
      ‖retardedSol (((b : ℝ) : ℂ) * lamStar)
        (((b : ℝ) : ℂ) * (sigma + 5 / 4 * I)) Kstar P.moment tstar‖ = 2 * κ →
      sCanon + d = tstar →
      ((‖Kstar‖ * Ccommon * ηcur) / (sigma / 2 - (b : ℝ) * sigma) *
        Real.exp ((b : ℝ) * sigma * d)) *
          Real.exp (-(sigma / 2 - (b : ℝ) * sigma) * Lback) ≤ κ / 4 →
      (∀ ρ : ℝ, 0 ≤ ρ →
        ‖retardedSol (((b : ℝ) : ℂ) * lamStar) (((b : ℝ) : ℂ) * (sigma + 5 / 4 * I))
          ((ρ : ℂ) ^ 6 * Kstar) P.moment (sCanon - Lback)‖ *
            Real.exp ((b : ℝ) * sigma * (Lback + d)) ≤ (κ / 4) * ρ ^ 6) →
      ∀ {s cA q T : ℝ}, ∀ [Fact (1 ≤ ENNReal.ofReal q)],
      ∀ (hs : s ≤ 0) (hcA : 0 < cA) (hq : 0 < q) (hqE : 2 ≤ ENNReal.ofReal q),
      0 < T → (∀ i, ‖(P.ancient s i).val - circularReferenceC1 hγ hγ1 i‖ ≤ ηcur) →
      ∀ᶠ ξ : ℝ in atTop,
        let ρ := Real.exp (-ξ)
        let hρ := Real.exp_pos (-ξ)
        let R := ρ ^ 10
        let hR := pow_pos hρ 10
        let A₀ := cA * (1 + ξ)
        ∀ N k : ℕ, ∀ hkN : k ≤ N, ∀ hkchild : k + 1 ≤ N,
        ∀ S : BoundedEulerParticleSystem
          (finiteBaseCurlL2 (A₀ := A₀) (b := (b : ℝ)) (ρ := ρ) hR hρ hq hqE
            (P.finiteBaseLp (A₀ := A₀) (b := (b : ℝ)) (ρ := ρ) (q := q) hs hR hρ) N) T,
        IsFourfoldBoundedEulerParticleSystem S →
        (∀ t ∈ Icc (0 : ℝ) T, MeasurePreserving (S.forward t) volume volume ∧
          MeasurePreserving (S.backward t) volume volume) →
        ∀ e : ℝ, 0 ≤ e → ∀ Ypast : ℝ → FiniteCircularIndex (k + 1) → LittleContourSpace γ,
        ∀ ℓcap : ℕ, ∀ δ Hcap Cbcap Cgraph Ctarget : ℝ,
        ampScale A₀ b (k + 1) * e ≤ Lentry * ξ + Dentry →
        P.HasActualParentNextHandoffCaptureExtension gseq (s := s) (A₀ := A₀) (b := (b : ℝ))
          hR hρ hkchild S e Ypast ℓcap δ ηcur Hcap Cbcap D₀ Cgraph ξ sCanon Ctarget Lback Cback Cmoment →
        P.HasActualUniformParentWarmupState gseq (s := s) (A₀ := A₀) (b := (b : ℝ))
          hR hρ hkN S ((b : ℝ) * Dobs) Cpre Ccur Cobs κ Lentry Dentry ξ := by
  obtain ⟨Kself, hKself, hwindowAll⟩ := P.exists_actualCoupledCanonical_parent_window_setup
  refine ⟨Kself, hKself, ?_⟩
  intro b hb hbquarter hslow Dobs ηcur hDobs hη hηa hηgap
  obtain ⟨Cbwin, hCbwin, Ccur, hCcur, Cobs, hCobs, hwindow⟩ :=
    hwindowAll b hb hbquarter hslow hDobs hη hηa hηgap
  refine ⟨Ccur, hCcur, Cobs, hCobs, ?_⟩
  intro gseq ℓwarm qcwarm Ccomp Cpre nwarm hwitness
    sCanon Lback d Ccommon Cmoment Cback κ tstar Lentry Dentry D₀
    hObsEq hsCanon hLback hd hκ hCcommon hCmoment hmargin hLrec hDrec hWarm hConeBudget hresponse htarget hlead htail
  subst Dobs
  have hbR : 0 < (b : ℝ) := hb
  have hbqR : (b : ℝ) < 1 / 4 := hbquarter
  have hb1 : (b : ℝ) < 1 := hbqR.trans (by norm_num : (1 / 4 : ℝ) < 1)
  let Dpre := (b : ℝ) * (Lback + d)
  have hDpre : 0 < Dpre := mul_pos hbR (add_pos hLback hd)
  have hRate : (b : ℝ) * sigma < sigma / 2 := by
    have hh := mul_lt_mul_of_pos_right (show (b : ℝ) < 1 / 4 from hbquarter) sigma_pos
    nlinarith only [hh, sigma_pos]
  have hleadTwo : ((‖Kstar‖ * Ccommon * ηcur) / (sigma / 2 - (b : ℝ) * sigma) *
      Real.exp ((b : ℝ) * sigma * d)) *
        Real.exp (-(sigma / 2 - (b : ℝ) * sigma) * Lback) ≤ (2 * κ) / 8 := by
    convert hlead using 1 <;> ring
  have htailTwo : ∀ ρ : ℝ, 0 ≤ ρ →
      ‖retardedSol (((b : ℝ) : ℂ) * lamStar) (((b : ℝ) : ℂ) * (sigma + 5 / 4 * I))
        ((ρ : ℂ) ^ 6 * Kstar) P.moment (sCanon - Lback)‖ *
          Real.exp ((b : ℝ) * sigma * (Lback + d)) ≤ ((2 * κ) / 8) * ρ ^ 6 := by
    intro ρ hρ
    convert htail ρ hρ using 1 <;> ring
  intro s cA q T _ hs hcA hq hqE hT hancient
  have htransfer := P.eventually_actualCanonical_coupled_nonzero_transfer
    (b := (b : ℝ)) (Cb := Cbwin) (Ccur := Ccur) (Cobs := Cobs)
    (sCanon := sCanon) (ηctrl := ηcur) (Lback := Lback) (d := d)
    (Chistory := Ccommon) (Cback := Cback) (κ := 2 * κ) (tstar := tstar)
    (rate := sigma / 2) (Lclock := Lentry + 6 / sigma) (Dclock := Dentry + D₀)
    hq hqE ⟨hbR, hbqR⟩ hs hcA hT.le hsCanon hLback hd (by positivity) hCcommon hη.le
    hCbwin.le hCcur.le hCobs.le hRate hmargin hresponse htarget hleadTwo htailTwo
  have hηquarter : ηcur ≤ cellA / 4 := hηa.trans (by linarith only [cellA_pos])
  have hready := hwitness nwarm (Kw := Cobs) (Kcur := Ccur) (κ := κ)
    hCobs.le hCcur.le hκ hConeBudget hs hcA hq hqE hT.le hη.le hηquarter hancient
  have hduration : ∀ᶠ ξ : ℝ in atTop, Dpre / (cA * (1 + ξ)) < T / 2 := by
    let B := 2 * Dpre / (T * cA)
    filter_upwards [eventually_ge_atTop B, eventually_ge_atTop (0 : ℝ)] with ξ hB hξ
    have hAξ : 0 < cA * (1 + ξ) := mul_pos hcA (by linarith only [hξ])
    have hTcA : 0 < T * cA := mul_pos hT hcA
    have hBeq : (T * cA) * B = 2 * Dpre := by
      dsimp only [B]
      field_simp [hTcA.ne']
    have hmul := mul_le_mul_of_nonneg_left hB hTcA.le
    apply (div_lt_iff₀ hAξ).mpr
    nlinarith only [hBeq, hmul, hTcA]
  filter_upwards [hwindow hs hcA hq hqE hT hancient, htransfer, hready, hduration,
    eventually_ge_atTop (0 : ℝ)] with ξ hwindowξ htransferξ hreadyξ hdurationξ hξ
  let ρ := Real.exp (-ξ)
  let R := ρ ^ 10
  let A₀ := cA * (1 + ξ)
  let h := 2 * ρ ^ 6
  have hρ : 0 < ρ := Real.exp_pos (-ξ)
  have hR : 0 < R := pow_pos hρ 10
  have hA : 0 < A₀ := mul_pos hcA (by linarith only [hξ])
  dsimp only
  intro N k hkN hkchild S hS harea e he Ypast ℓcap δ Hcap Cbcap Cgraph Ctarget hEntryClock hcap
  obtain ⟨Ncap, hNcap, hDlog, hterminal, hphysical, X, hX, heq,
    hgrid, henv, hcur, hback, hweighted, hparticles, hgraph, hfirst,
    u, hu, hLong, htime, angle, hmatched, hEarlier, hFull, hMoment, hcontrols, hparticlesFull, hvalue, hbefore⟩ := hcap
  let Dcap := (Ncap : ℝ) * circularCaptureBlockTime ℓcap
  let Hchild := e + Dcap / ampScale A₀ b (k + 1)
  let exit := ampScale A₀ b (k + 1) * e + u
  let entrance := (exit - Lback) / ampScale A₀ b (k + 1)
  let Hparent := entrance + Dpre / ampScale A₀ b k
  have hAmp : 0 < ampScale A₀ b (k + 1) := div_pos hA (pow_pos hbR (k + 1))
  have hAmpParent : 0 < ampScale A₀ b k := div_pos hA (pow_pos hbR k)
  have hrad : 0 < radScale R ρ (k + 1) := radScale_pos hR hρ (k + 1)
  have hDcap : 0 ≤ Dcap := hu.1.le.trans hu.2
  have hHchild : 0 ≤ Hchild := add_nonneg he (div_nonneg hDcap hAmp.le)
  have hLexit : Lback < exit := by
    have hh := mul_nonneg hAmp.le he
    dsimp only [exit]
    linarith only [hh, hLong]
  have hExitClock : exit ≤ (Lentry + 6 / sigma) * ξ + (Dentry + D₀) := by
    dsimp only [exit]
    calc
      _ ≤ (Lentry * ξ + Dentry) + Dcap := add_le_add hEntryClock hu.2
      _ ≤ (Lentry * ξ + Dentry) + ((6 / sigma) * ξ + D₀) := add_le_add le_rfl hDlog
      _ = _ := by ring
  have hclockEntrance : physicalTimeFromNormalized (ampScale A₀ b (k + 1)) e (u - Lback) = entrance := by
    dsimp only [physicalTimeFromNormalized, entrance, exit]
    field_simp [hAmp.ne'] <;> ring
  have hentrance : 0 ≤ entrance := div_nonneg (sub_nonneg.mpr hLexit.le) hAmp.le
  have hentranceChild : entrance ≤ Hchild := by
    rw [← hclockEntrance]
    change e + (u - Lback) / ampScale A₀ b (k + 1) ≤ e + Dcap / ampScale A₀ b (k + 1)
    exact add_le_add le_rfl (div_le_div_of_nonneg_right ((sub_le_self u hLback.le).trans hu.2) hAmp.le)
  have hAmpLower : A₀ ≤ ampScale A₀ b k := by
    change A₀ ≤ A₀ / (b : ℝ) ^ k
    apply (le_div_iff₀ (pow_pos hbR k)).mpr
    exact mul_le_of_le_one_right hA.le (pow_le_one₀ hbR.le hb1.le)
  have hEnd : Hparent < T := by
    have hhand := hentranceChild.trans_lt hphysical
    have hinc := div_le_div_of_nonneg_left hDpre.le hA hAmpLower
    dsimp only [Hparent]
    linarith only [hhand, hinc, hdurationξ]
  have hMomentCommon : ∀ τ ∈ Icc (0 : ℝ) (exit - Lback),
      let t := physicalTimeFromNormalized (ampScale A₀ b (k + 1)) 0 τ
      ‖momentN (boxedComplexDensity
        (S.transportedScalar (P.finitePeriodicLabel s A₀ b R ρ N (k + 1)) t)) 4‖ ≤
        ampScale A₀ b (k + 1) * radScale R ρ (k + 1) ^ 6 * Ccommon * ηcur *
          Real.exp (-(sigma / 2) * (exit - τ)) := by
    intro τ hτ
    dsimp only
    refine (hMoment τ ⟨hτ.1, hτ.2.trans (sub_le_self _ hLback.le)⟩).trans ?_
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hCmoment (mul_nonneg hAmp.le (pow_nonneg hrad.le 6))) hη.le)
      (Real.exp_pos _).le
  have hclockNorm : ampScale A₀ b (k + 1) * entrance = exit - Lback := by
    dsimp only [entrance]
    field_simp [hAmp.ne']
  obtain ⟨Y, hY, hweightedY, hcurY, hparticlesWindow, hparticlesPast, hpast⟩ :=
    hwindowξ N (k + 1) (Nat.succ_pos k) hkchild S hS entrance
      (div_pos (sub_pos.mpr hLexit) hAmp) hEnd X (hX.mono hentranceChild)
      (by rw [hclockNorm]; intro τ hτ; exact (hcontrols τ hτ).1)
      (by rw [hclockNorm]; intro τ hτ; exact (hcontrols τ hτ).2) hparticlesFull
  have hHparent : 0 ≤ Hparent := add_nonneg hentrance (div_nonneg hDpre.le hAmpParent.le)
  have hwindowArg (v : ℝ) (hv : v ∈ Icc (0 : ℝ) (Lback + d)) :
      (b : ℝ) * v ∈ Icc (0 : ℝ) Dpre :=
    ⟨mul_nonneg hbR.le hv.1, mul_le_mul_of_nonneg_left hv.2 hbR.le⟩
  have hweightedObs (v : ℝ) (hv : v ∈ Icc (0 : ℝ) (Lback + d)) := hweightedY ((b : ℝ) * v) (hwindowArg v hv)
  have hcurObs (v : ℝ) (hv : v ∈ Icc (0 : ℝ) (Lback + d)) := hcurY ((b : ℝ) * v) (hwindowArg v hv)
  have hparticlesObs (v : ℝ) (hv : v ∈ Icc (0 : ℝ) (Lback + d)) := hparticlesWindow ((b : ℝ) * v) (hwindowArg v hv)
  have hlowerRaw := htransferξ N k hkN hkchild S hS harea Hchild Hparent hHchild hHparent X hX Y hY
    exit e (u - Lback) angle hLexit.le hExitClock hclockEntrance ⟨hentrance, hentranceChild⟩
    le_rfl hEarlier (by intro t ht; exact ⟨(hpast t ht).1, (hpast t ht).2.1⟩)
    hparticlesPast hMomentCommon hweightedObs hcurObs hparticlesObs
  have hlower : κ * ρ ^ 6 ≤ ‖canonicalPrefixMaterialGrowingCoordinate hγ hγ1 A₀ b R ρ k Y
      (ampScale A₀ b k * entrance + Dpre)‖ := by
    convert hlowerRaw using 1 <;> ring
  have hown0 : canonicalPrefixStageDeviation hγ hγ1 A₀ b R ρ k 0 Y
      (ampScale A₀ b k * entrance + 0) k =
        canonicalPrefixStageDeviation hγ hγ1 A₀ b R ρ k entrance Y 0 k := by
    apply canonicalPrefixStageDeviation_crossPrefix_eq hγ hγ1 hA.ne' hbR.ne' R ρ le_rfl Y Y
      (physicalTimeFromNormalized (ampScale A₀ b k) entrance 0)
      entrance 0 0 (ampScale A₀ b k * entrance + 0) rfl ?_ (fun _ => rfl) k le_rfl
    simp only [physicalTimeFromNormalized, zero_div, zero_add, add_zero]
    change (ampScale A₀ b k * entrance) / ampScale A₀ b k = entrance
    field_simp [hAmpParent.ne']
  have hinit : ‖canonicalPrefixStageDeviation hγ hγ1 A₀ b R ρ k entrance Y 0 k‖ ≤ h := by
    rw [← hown0]
    simpa only [add_zero] using (hpast entrance ⟨hentrance, le_rfl⟩).2.1
  have hweightedGrid (v : ℝ) (hv : v ∈ Icc (0 : ℝ) ((nwarm : ℝ) * circularCaptureBlockTime ℓwarm)) :=
    hweightedY v ⟨hv.1, hv.2.trans_eq hWarm.symm⟩
  have hcurGrid (v : ℝ) (hv : v ∈ Icc (0 : ℝ) ((nwarm : ℝ) * circularCaptureBlockTime ℓwarm)) :=
    hcurY v ⟨hv.1, hv.2.trans_eq hWarm.symm⟩
  have htimeGrid : entrance + ((nwarm : ℝ) * circularCaptureBlockTime ℓwarm) / ampScale A₀ b k ≤ Hparent := by
    rw [← hWarm]
  have hlowerGrid : κ * ρ ^ 6 ≤ ‖canonicalPrefixMaterialGrowingCoordinate hγ hγ1 A₀ b R ρ k Y
      (ampScale A₀ b k * entrance + (nwarm : ℝ) * circularCaptureBlockTime ℓwarm)‖ := by
    rw [← hWarm]
    exact hlower
  have hreadyData := hreadyξ N k hkN S hS hHparent Y hY entrance hentrance htimeGrid
    hweightedGrid hcurGrid hinit (hparticlesPast entrance ⟨hentrance, le_rfl⟩) hlowerGrid
  rw [← hWarm] at hreadyData
  obtain ⟨hαpos, hcone, hchart, hpure⟩ := hreadyData
  have hclockIdentity : ampScale A₀ b k * Hparent = (b : ℝ) * (exit - Lback) + Dpre := by
    dsimp only [Hparent, entrance]
    rw [ampScale_succ_eq_div]
    field_simp [hAmpParent.ne', hbR.ne'] <;> ring
  have hNextClock : ampScale A₀ b k * Hparent ≤ Lentry * ξ + Dentry := by
    rw [hclockIdentity]
    calc
      _ ≤ (b : ℝ) * exit + Dpre := add_le_add (mul_le_mul_of_nonneg_left (sub_le_self _ hLback.le) hbR.le) le_rfl
      _ ≤ (b : ℝ) * ((Lentry + 6 / sigma) * ξ + (Dentry + D₀)) + Dpre :=
        add_le_add (mul_le_mul_of_nonneg_left hExitClock hbR.le) le_rfl
      _ = ((b : ℝ) * (Lentry + 6 / sigma)) * ξ + ((b : ℝ) * (Dentry + D₀) + Dpre) := by ring
      _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_right hLrec hξ) hDrec
  exact ⟨entrance, hentrance, hEnd, hNextClock, Y, hY, hlower, ⟨hαpos, hcone, hchart⟩,
    hweightedY, hcurY, hpure, hparticlesPast, hpast⟩

end CircularMaterialTransferProfile
end Euler2D

end
