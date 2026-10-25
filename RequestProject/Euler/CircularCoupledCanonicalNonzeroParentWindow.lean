module

public import RequestProject.Euler.CircularCoupledCanonicalParentWindow
public import RequestProject.Euler.CircularCoupledCanonicalNonzeroTransfer

/-! Construct the next actual parent AND prove its nonzero response.
The input is the existing child's genuine past, lookback match and
transported moment history. The output parent is on the SAME original
finite Euler system, with all past/future controls retained. -/

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 64000000
set_option maxRecDepth 10000

noncomputable section

open Complex Set Filter Topology MeasureTheory Metric
open scoped NNReal ENNReal

namespace Euler2D

attribute [local instance 2000] rigidGaugeLittle_group rigidGaugeLittle_space rigidGaugeFamily_tower
attribute [local instance] LittleContourSpace.complexScalarNormedSpace LittleContourSpace.complexScalarTower
attribute [local irreducible] contourC1GraphSubmodule holderGraphSubmodule

namespace CircularMaterialTransferProfile

variable {γ : ℝ≥0} {hγ : 0 < γ} {hγ1 : (γ : ℝ) < 1}
    (P : CircularMaterialTransferProfile hγ hγ1)

theorem exists_actualCoupledCanonical_nonzero_parent_window_setup :
    ∃ Kself : ℝ≥0, 0 < Kself ∧
      ∀ b : ℝ≥0, 0 < b → b < 1 / 4 →
      (b : ℝ) * Kself + (b : ℝ) *
        (finiteInnerLabelLittleRowCoefficient (γ : ℝ) (cellA / 2)
          (circularCanonicalCellNormBudget hγ hγ1) / (2 - 1)) < sigma / 4 →
      ∀ {sCanon ηctrl Lback d Chistory Cback κ tstar rate Lclock Dclock : ℝ},
      0 < ηctrl → ηctrl ≤ cellA / 16 → ηctrl ≤ (1 - cellA) / 16 →
      sCanon < 0 → 0 < Lback → 0 < d → 0 < κ → 0 ≤ Chistory →
      (b : ℝ) * sigma < rate → sigma * Lclock < 8 →
      ‖retardedSol (((b : ℝ) : ℂ) * lamStar)
        (((b : ℝ) : ℂ) * (sigma + 5 / 4 * I)) Kstar P.moment tstar‖ = κ →
      sCanon + d = tstar →
      ((‖Kstar‖ * Chistory * ηctrl) / (rate - (b : ℝ) * sigma) *
        Real.exp ((b : ℝ) * sigma * d)) *
          Real.exp (-(rate - (b : ℝ) * sigma) * Lback) ≤ κ / 8 →
      (∀ ρ : ℝ, 0 ≤ ρ →
        ‖retardedSol (((b : ℝ) : ℂ) * lamStar) (((b : ℝ) : ℂ) * (sigma + 5 / 4 * I))
          ((ρ : ℂ) ^ 6 * Kstar) P.moment (sCanon - Lback)‖ *
            Real.exp ((b : ℝ) * sigma * (Lback + d)) ≤ (κ / 8) * ρ ^ 6) →
      ∃ Cb > 0, ∃ Ccur > 0, ∃ Cobs > 0,
      ∀ {s cA q T : ℝ}, ∀ [Fact (1 ≤ ENNReal.ofReal q)],
      ∀ (hs : s ≤ 0) (hcA : 0 < cA) (hq : 0 < q) (hqE : 2 ≤ ENNReal.ofReal q),
      0 < T → (∀ i, ‖(P.ancient s i).val - circularReferenceC1 hγ hγ1 i‖ ≤ ηctrl) →
      ∀ᶠ ξ : ℝ in atTop,
        let ρ := Real.exp (-ξ)
        let hρ := Real.exp_pos (-ξ)
        let R := ρ ^ 10
        let hR := pow_pos hρ 10
        let A₀ := cA * (1 + ξ)
        let h := 2 * ρ ^ 6
        ∀ N k : ℕ, ∀ hkN : k ≤ N, ∀ hkchild : k + 1 ≤ N,
        ∀ S : BoundedEulerParticleSystem
          (finiteBaseCurlL2 (A₀ := A₀) (b := (b : ℝ)) (ρ := ρ) hR hρ hq hqE
            (P.finiteBaseLp (A₀ := A₀) (b := (b : ℝ)) (ρ := ρ) (q := q) hs hR hρ) N) T,
        IsFourfoldBoundedEulerParticleSystem S →
        (∀ t ∈ Icc (0 : ℝ) T, MeasurePreserving (S.forward t) volume volume ∧
          MeasurePreserving (S.backward t) volume volume) →
        ∀ Hchild : ℝ, 0 ≤ Hchild →
        ∀ X : ℝ → FiniteCircularIndex (k + 1) → LittleContourSpace γ,
        P.ActualCanonicalPrefixTrajectory s A₀ b R ρ (1 / 16) T hR hρ hkchild S Hchild X →
        ∀ exit captureEntrance lookbackExit angle : ℝ,
        let entrance := (exit - Lback) / ampScale A₀ b (k + 1)
        let Dpre := (b : ℝ) * (Lback + d)
        let Hparent := entrance + Dpre / ampScale A₀ b k
        Lback < exit → exit ≤ Lclock * ξ + Dclock →
        physicalTimeFromNormalized (ampScale A₀ b (k + 1)) captureEntrance lookbackExit = entrance →
        entrance ≤ Hchild → Hparent < T →
        ‖circularCoRotationCLM γ lookbackExit
            (canonicalPrefixAlignedCurrentCell A₀ b R ρ (k + 1) captureEntrance X lookbackExit) -
          contourRotationFamilyLittleCLM γ angle
            (circularCoRotationCLM γ (sCanon - Lback) (P.ancient (sCanon - Lback)))‖ ≤ Cback * ρ ^ 3 →
        (∀ u ∈ Icc (0 : ℝ) (exit - Lback),
          let x := canonicalPrefixStageDeviation hγ hγ1 A₀ b R ρ (k + 1) 0 X u
          weightedFamilyNorm h (k + 1) x ≤ 1 ∧ ‖x (k + 1)‖ ≤ ηctrl) →
        (∀ t ∈ Icc (0 : ℝ) entrance, ∀ z ∈ P.finiteInnerActiveInitialLabels s A₀ b R ρ N (k + 1),
          ‖S.forward t z - torusCenter‖ ≤ 2 * radScale R ρ (k + 1)) →
        (∀ u ∈ Icc (0 : ℝ) (exit - Lback),
          let t := physicalTimeFromNormalized (ampScale A₀ b (k + 1)) 0 u
          ‖momentN (boxedComplexDensity
            (S.transportedScalar (P.finitePeriodicLabel s A₀ b R ρ N (k + 1)) t)) 4‖ ≤
            ampScale A₀ b (k + 1) * radScale R ρ (k + 1) ^ 6 * Chistory * ηctrl *
              Real.exp (-rate * (exit - u))) →
        ∃ Y : ℝ → FiniteCircularIndex k → LittleContourSpace γ,
          P.ActualCanonicalPrefixTrajectory s A₀ b R ρ (1 / 16) T hR hρ hkN S Hparent Y ∧
          (κ / 2) * ρ ^ 6 ≤ ‖canonicalPrefixMaterialGrowingCoordinate hγ hγ1 A₀ b R ρ k Y
            (ampScale A₀ b k * entrance + Dpre)‖ ∧
          (∀ u ∈ Icc (0 : ℝ) Dpre,
            weightedFamilyNorm h k (canonicalPrefixStageDeviation hγ hγ1 A₀ b R ρ k entrance Y u) ≤ Cobs * h) ∧
          (∀ u ∈ Icc (0 : ℝ) Dpre,
            ‖canonicalPrefixStageDeviation hγ hγ1 A₀ b R ρ k entrance Y u k‖ ≤ Ccur * h) ∧
          (∀ u ∈ Icc (0 : ℝ) Dpre, ∀ z ∈ P.finiteInnerActiveInitialLabels s A₀ b R ρ N k,
            ‖S.forward (physicalTimeFromNormalized (ampScale A₀ b k) entrance u) z - torusCenter‖ ≤
              Cb * ρ * radScale R ρ k * (1 + u)) ∧
          (∀ t ∈ Icc (0 : ℝ) entrance, ∀ z ∈ P.finiteInnerActiveInitialLabels s A₀ b R ρ N k,
            ‖S.forward t z - torusCenter‖ ≤ 2 * ρ * radScale R ρ k) ∧
          ∀ t ∈ Icc (0 : ℝ) entrance,
            let x := canonicalPrefixStageDeviation hγ hγ1 A₀ b R ρ k 0 Y (ampScale A₀ b k * t)
            weightedFamilyNorm h k x ≤ h ∧ ‖x k‖ ≤ h ∧
              (2 ≤ k + 1 → ‖x (k + 1 - 2)‖ ≤ h ^ 2) := by
  obtain ⟨Kself, hKself, hwindowAll⟩ := P.exists_actualCoupledCanonical_parent_window_setup
  refine ⟨Kself, hKself, ?_⟩
  intro b hb hbquarter hslow sCanon ηctrl Lback d Chistory Cback κ tstar rate Lclock Dclock
    hηctrl hηa hηgap hsCanon hLback hd hκ hChistory hRate hclockMargin hresponse htarget hlead htail
  let Dobs := Lback + d
  have hDobs : 0 < Dobs := add_pos hLback hd
  obtain ⟨Cb, hCb, Ccur, hCcur, Cobs, hCobs, hwindow⟩ :=
    hwindowAll b hb hbquarter hslow hDobs hηctrl hηa hηgap
  refine ⟨Cb, hCb, Ccur, hCcur, Cobs, hCobs, ?_⟩
  intro s cA q T _ hs hcA hq hqE hT hancient
  have htransfer := P.eventually_actualCanonical_coupled_nonzero_transfer
    (Chistory := Chistory) (Cback := Cback) (Cb := Cb) (Ccur := Ccur) (Cobs := Cobs)
    (Lclock := Lclock) (Dclock := Dclock)
    hq hqE ⟨hb, hbquarter⟩ hs hcA hT.le hsCanon hLback hd hκ hChistory hηctrl.le
    hCb.le hCcur.le hCobs.le hRate hclockMargin hresponse htarget hlead htail
  filter_upwards [hwindow hs hcA hq hqE hT hancient, htransfer, eventually_ge_atTop (0 : ℝ)]
    with ξ hwindowξ htransferξ hξ
  let ρ := Real.exp (-ξ)
  let R := ρ ^ 10
  let A₀ := cA * (1 + ξ)
  let h := 2 * ρ ^ 6
  have hA : 0 < A₀ := mul_pos hcA (by linarith only [hξ])
  have hbR : 0 < (b : ℝ) := hb
  dsimp only
  intro N k hkN hkchild S hS harea Hchild hHchild X hX exit captureEntrance lookbackExit angle
  let entrance := (exit - Lback) / ampScale A₀ b (k + 1)
  let Dpre := (b : ℝ) * Dobs
  let Hparent := entrance + Dpre / ampScale A₀ b k
  intro hLexit hclockLimit hclockEntrance hentranceChild hEnd hback hcontrols hdeeper hmomentHistory
  have hAmp : 0 < ampScale A₀ b (k + 1) := div_pos hA (pow_pos hbR (k + 1))
  have hAmpParent : 0 < ampScale A₀ b k := div_pos hA (pow_pos hbR k)
  have hentrance : 0 < entrance := div_pos (sub_pos.mpr hLexit) hAmp
  have hHparent : 0 ≤ Hparent := add_nonneg hentrance.le (div_nonneg (mul_nonneg hbR.le hDobs.le) hAmpParent.le)
  have hclockNorm : ampScale A₀ b (k + 1) * entrance = exit - Lback := by
    dsimp only [entrance]
    field_simp [hAmp.ne']
  obtain ⟨Y, hY, hweightedY, hcurY, hparticlesY, hparticlesPast, hpast⟩ :=
    hwindowξ N (k + 1) (Nat.succ_pos k) hkchild S hS entrance hentrance hEnd X (hX.mono hentranceChild)
      (by rw [hclockNorm]; intro u hu; exact (hcontrols u hu).1)
      (by rw [hclockNorm]; intro u hu; exact (hcontrols u hu).2) hdeeper
  have hwindowArg (u : ℝ) (hu : u ∈ Icc (0 : ℝ) Dobs) :
      (b : ℝ) * u ∈ Icc (0 : ℝ) Dpre :=
    ⟨mul_nonneg hbR.le hu.1, mul_le_mul_of_nonneg_left hu.2 hbR.le⟩
  have hweightedObs (u : ℝ) (hu : u ∈ Icc (0 : ℝ) Dobs) := hweightedY ((b : ℝ) * u) (hwindowArg u hu)
  have hcurObs (u : ℝ) (hu : u ∈ Icc (0 : ℝ) Dobs) := hcurY ((b : ℝ) * u) (hwindowArg u hu)
  have hparticlesObs (u : ℝ) (hu : u ∈ Icc (0 : ℝ) Dobs) := hparticlesY ((b : ℝ) * u) (hwindowArg u hu)
  have hlower := htransferξ N k hkN hkchild S hS harea Hchild Hparent hHchild hHparent X hX Y hY
    exit captureEntrance lookbackExit angle hLexit.le hclockLimit hclockEntrance
    ⟨hentrance.le, hentranceChild⟩ le_rfl hback
    (by intro t ht; exact ⟨(hpast t ht).1, (hpast t ht).2.1⟩)
    hparticlesPast hmomentHistory hweightedObs hcurObs hparticlesObs
  exact ⟨Y, hY, hlower, hweightedY, hcurY, hparticlesY, hparticlesPast, hpast⟩

end CircularMaterialTransferProfile
end Euler2D

end
