module

public import RequestProject.Euler.CircularActualFirstNonzeroTransfer
public import RequestProject.Euler.CircularCoupledCanonicalHistory
public import RequestProject.Euler.CircularCoupledCanonicalRetardedComparison
public import RequestProject.Euler.CircularCoupledCanonicalObservedMoment
public import RequestProject.Euler.CircularCoupledPastRemainderBudget

/-! A genuine nonzero transfer on the SAME actual finite Euler system,
at arbitrary cutoff N and parent k<N. The child may already be forced:
its history has any rate>b*sigma, its capture entrance need not be zero,
and its absolute exit may grow along the true logarithmic cascade clock.
No trajectory, initial amplitude, target or physical time is reset. -/

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

theorem eventually_actualCanonical_coupled_nonzero_transfer
    {q T : ℝ} [Fact (1 ≤ ENNReal.ofReal q)]
    (hq : 0 < q) (hqE : 2 ≤ ENNReal.ofReal q)
    {b s cA sCanon ηctrl Lback d Chistory Cback Cb Ccur Cobs κ tstar rate Lclock Dclock : ℝ}
    (hb : b ∈ Ioo (0 : ℝ) (1 / 4)) (hs : s ≤ 0) (hcA : 0 < cA) (hT : 0 ≤ T)
    (hsCanon : sCanon < 0) (hLback : 0 < Lback) (hd : 0 < d) (hκ : 0 < κ)
    (hChistory : 0 ≤ Chistory) (hηctrl : 0 ≤ ηctrl)
    (hCb : 0 ≤ Cb) (hCcur : 0 ≤ Ccur) (hCobs : 0 ≤ Cobs)
    (hRate : b * sigma < rate) (hclockMargin : sigma * Lclock < 8)
    (hresponse : ‖retardedSol ((b : ℂ) * lamStar)
      ((b : ℂ) * (sigma + 5 / 4 * I)) Kstar P.moment tstar‖ = κ)
    (htarget : sCanon + d = tstar)
    (hlead : ((‖Kstar‖ * Chistory * ηctrl) / (rate - b * sigma) *
        Real.exp (b * sigma * d)) * Real.exp (-(rate - b * sigma) * Lback) ≤ κ / 8)
    (htail : ∀ ρ : ℝ, 0 ≤ ρ →
      ‖retardedSol ((b : ℂ) * lamStar) ((b : ℂ) * (sigma + 5 / 4 * I))
        ((ρ : ℂ) ^ 6 * Kstar) P.moment (sCanon - Lback)‖ *
          Real.exp (b * sigma * (Lback + d)) ≤ (κ / 8) * ρ ^ 6) :
    ∀ᶠ ξ : ℝ in atTop,
      let ρ := Real.exp (-ξ)
      let hρ := Real.exp_pos (-ξ)
      let R := ρ ^ 10
      let hR := pow_pos hρ 10
      let A₀ := cA * (1 + ξ)
      let h := 2 * ρ ^ 6
      ∀ N k : ℕ, ∀ hkN : k ≤ N, ∀ hkchild : k + 1 ≤ N,
      ∀ S : BoundedEulerParticleSystem
        (finiteBaseCurlL2 (A₀ := A₀) (b := b) (ρ := ρ) hR hρ hq hqE
          (P.finiteBaseLp (A₀ := A₀) (b := b) (ρ := ρ) (q := q) hs hR hρ) N) T,
      IsFourfoldBoundedEulerParticleSystem S →
      (∀ t ∈ Icc (0 : ℝ) T, MeasurePreserving (S.forward t) volume volume ∧
        MeasurePreserving (S.backward t) volume volume) →
      ∀ Hchild Hparent : ℝ, 0 ≤ Hchild → 0 ≤ Hparent →
      ∀ X : ℝ → FiniteCircularIndex (k + 1) → LittleContourSpace γ,
      P.ActualCanonicalPrefixTrajectory s A₀ b R ρ (1 / 16) T hR hρ hkchild S Hchild X →
      ∀ Y : ℝ → FiniteCircularIndex k → LittleContourSpace γ,
      P.ActualCanonicalPrefixTrajectory s A₀ b R ρ (1 / 16) T hR hρ hkN S Hparent Y →
      ∀ exit captureEntrance lookbackExit angle : ℝ,
      let entrance := (exit - Lback) / ampScale A₀ b (k + 1)
      Lback ≤ exit → exit ≤ Lclock * ξ + Dclock →
      physicalTimeFromNormalized (ampScale A₀ b (k + 1)) captureEntrance lookbackExit = entrance →
      entrance ∈ Icc (0 : ℝ) Hchild →
      entrance + b * (Lback + d) / ampScale A₀ b k ≤ Hparent →
      ‖circularCoRotationCLM γ lookbackExit
          (canonicalPrefixAlignedCurrentCell A₀ b R ρ (k + 1) captureEntrance X lookbackExit) -
        contourRotationFamilyLittleCLM γ angle
          (circularCoRotationCLM γ (sCanon - Lback) (P.ancient (sCanon - Lback)))‖ ≤ Cback * ρ ^ 3 →
      (∀ t ∈ Icc (0 : ℝ) entrance,
        let x := canonicalPrefixStageDeviation hγ hγ1 A₀ b R ρ k 0 Y (ampScale A₀ b k * t)
        weightedFamilyNorm h k x ≤ h ∧ ‖x k‖ ≤ h) →
      (∀ t ∈ Icc (0 : ℝ) entrance, ∀ z ∈ P.finiteInnerActiveInitialLabels s A₀ b R ρ N k,
        ‖S.forward t z - torusCenter‖ ≤ 2 * ρ * radScale R ρ k) →
      (∀ u ∈ Icc (0 : ℝ) (exit - Lback),
        let t := physicalTimeFromNormalized (ampScale A₀ b (k + 1)) 0 u
        ‖momentN (boxedComplexDensity
          (S.transportedScalar (P.finitePeriodicLabel s A₀ b R ρ N (k + 1)) t)) 4‖ ≤
          ampScale A₀ b (k + 1) * radScale R ρ (k + 1) ^ 6 * Chistory * ηctrl *
            Real.exp (-rate * (exit - u))) →
      (∀ u ∈ Icc (0 : ℝ) (Lback + d),
        weightedFamilyNorm h k (canonicalPrefixStageDeviation hγ hγ1 A₀ b R ρ k entrance Y (b * u)) ≤ Cobs * h) →
      (∀ u ∈ Icc (0 : ℝ) (Lback + d),
        ‖canonicalPrefixStageDeviation hγ hγ1 A₀ b R ρ k entrance Y (b * u) k‖ ≤ Ccur * h) →
      (∀ u ∈ Icc (0 : ℝ) (Lback + d), ∀ z ∈ P.finiteInnerActiveInitialLabels s A₀ b R ρ N k,
        ‖S.forward (physicalTimeFromNormalized (ampScale A₀ b k) entrance (b * u)) z - torusCenter‖ ≤
          Cb * ρ * radScale R ρ k * (1 + b * u)) →
      (κ / 2) * ρ ^ 6 ≤ ‖canonicalPrefixMaterialGrowingCoordinate hγ hγ1 A₀ b R ρ k Y
        (ampScale A₀ b k * entrance + b * (Lback + d))‖ := by
  let Dobs := Lback + d
  have hb1 : b < 1 := hb.2.trans (by norm_num)
  have hDobs : 0 < Dobs := add_pos hLback hd
  have hbsigma : 0 ≤ b * sigma := mul_nonneg hb.1.le sigma_pos.le
  have hmargin : (b * sigma) * Lclock < 2 :=
    circularCapture_cascade_parent_amplification_margin hb.1 hb.2 hclockMargin
  obtain ⟨Cpast, hCpast, hpastEstimate⟩ := P.exists_eventually_actualCanonical_coupled_physical_lookback_history
    hb.1 hb1 hChistory hηctrl hRate
  obtain ⟨Cfuture, hCfuture, hcomparison⟩ := P.exists_eventually_actualCanonical_coupled_retarded_comparison
    (Cb := Cb) (Kw := Cobs) (Kcur := Ccur) hb hCb hCobs hCcur
  let Eamp := Real.exp (b * sigma * Dobs)
  let Bobs := Cfuture * Dobs * Eamp
  let ηobs := (κ / 16) / (Bobs + 1)
  have hBobs : 0 ≤ Bobs := by dsimp only [Bobs, Eamp]; positivity
  have hηobs : 0 < ηobs := div_pos (div_pos hκ (by norm_num)) (by linarith only [hBobs])
  have hηeq : ηobs * (Bobs + 1) = κ / 16 := by
    dsimp only [ηobs]
    exact div_mul_cancel₀ _ (by positivity : Bobs + 1 ≠ 0)
  have hηbudget : Bobs * ηobs ≤ κ / 16 := by nlinarith only [hηeq, hηobs.le]
  have hsObs : sCanon - Lback ≤ 0 := by linarith only [hsCanon, hLback]
  have hobserve := P.eventually_actualCanonical_coupled_observed_child_moment
    (sObs := sCanon - Lback) (Dobs := Dobs) (Cw := Cobs) (Ccur := Ccur) (Cback := Cback) (η := ηobs)
    hsObs hs hcA hb.1 hb1.le hq hqE hT hDobs.le hCobs hCcur hηobs
  have hpastSmall := eventually_circularCapture_actual_past_error_relative_small
    (C := Cpast) (θ := b * sigma) (L := Lclock) (D := Dclock) (d := d)
    hCpast.le hbsigma (div_pos hκ (by norm_num : (0 : ℝ) < 8)) hmargin
  let Kfuture := Cfuture * (1 + b * Dobs) ^ 8 * Dobs * Eamp
  have hfutureSmall : ∀ᶠ ξ : ℝ in atTop, Kfuture * Real.exp (-ξ) ^ 2 ≤ κ / 16 := by
    have ht : Tendsto (fun ξ : ℝ => Kfuture * Real.exp (-ξ) ^ 2) atTop (𝓝 0) := by
      simpa only [zero_pow (by decide : 2 ≠ 0), mul_zero] using
        (Real.tendsto_exp_neg_atTop_nhds_zero.pow 2).const_mul Kfuture
    exact (ht.eventually (gt_mem_nhds (div_pos hκ (by norm_num)))).mono (fun _ h => h.le)
  filter_upwards [hpastEstimate hs hcA hq hqE hT,
    hcomparison (Dobs := Dobs) hs hcA hq hqE hT hDobs.le, hobserve, hpastSmall, hfutureSmall,
    eventually_ge_atTop (0 : ℝ)] with ξ hpastξ hcomparisonξ hobserveξ hpastSmallξ hfutureSmallξ hξ
  let ρ := Real.exp (-ξ)
  let R := ρ ^ 10
  let A₀ := cA * (1 + ξ)
  let h := 2 * ρ ^ 6
  have hρ : 0 < ρ := Real.exp_pos (-ξ)
  have hR : 0 < R := pow_pos hρ 10
  have hA : 0 < A₀ := mul_pos hcA (by linarith only [hξ])
  dsimp only
  intro N k hkN hkchild S hS harea Hchild Hparent hHchild hHparent X hX Y hY exit captureEntrance lookbackExit angle
  let entrance := (exit - Lback) / ampScale A₀ b (k + 1)
  intro hLexit hclockLimit hclockEntrance hentranceChild hEnd hback hpast hparticlesPast hmomentHistory hweightedObs hcurObs hparticlesObs
  have hAmp : 0 < ampScale A₀ b (k + 1) := div_pos hA (pow_pos hb.1 (k + 1))
  have hAmpParent : 0 < ampScale A₀ b k := div_pos hA (pow_pos hb.1 k)
  have hentrance : 0 ≤ entrance := div_nonneg (sub_nonneg.mpr hLexit) hAmp.le
  have hentranceH : entrance ≤ Hparent :=
    (le_add_of_nonneg_right (div_nonneg (mul_nonneg hb.1.le hDobs.le) hAmpParent.le)).trans hEnd
  let σ₀ := ampScale A₀ b k * entrance
  let W := fun u : ℝ => canonicalPrefixMaterialGrowingCoordinate hγ hγ1 A₀ b R ρ k Y (σ₀ + b * u)
  let θp := entrance * finiteAncestorAngularVelocity A₀ b k
  let θc := entrance * finiteAncestorAngularVelocity A₀ b (k + 1) + angle
  let response := P.shiftedRetardedTransfer b ρ θp θc (sCanon - Lback)
  let ε := Cfuture * (ρ ^ 8 * (1 + b * Dobs) ^ 8 + ρ ^ 6 * ηobs)
  have hsigma0 : σ₀ = b * (exit - Lback) := by
    dsimp only [σ₀, entrance]
    rw [ampScale_succ_eq_div]
    field_simp [hAmpParent.ne', hb.1.ne'] <;> ring
  have hW0 : W 0 = canonicalPrefixMaterialGrowingCoordinate hγ hγ1 A₀ b R ρ k Y (b * (exit - Lback)) := by
    dsimp only [W]
    rw [mul_zero, add_zero, hsigma0]
  have hmomentObs := hobserveξ N k hkN hkchild S hS harea Hchild Hparent hHchild hHparent
    X hX Y hY captureEntrance lookbackExit entrance angle hclockEntrance hentranceChild hback
    hEnd hweightedObs hcurObs
  have hcompareAll := hcomparisonξ N k hkN hkchild S hS hHparent Y hY entrance angle (sCanon - Lback) ηobs
    hentrance hηobs.le hEnd hweightedObs hcurObs hparticlesObs hmomentObs
  have hcompare : ‖W Dobs - response Dobs‖ ≤ (‖W 0 - response 0‖ + ε * Dobs) * Eamp :=
    hcompareAll Dobs ⟨hDobs.le, le_rfl⟩
  have hpastBound := hpastξ N k hkN hkchild S hS hHparent Y hY exit Lback d hLback.le hLexit
    hentranceH hpast hparticlesPast hmomentHistory
  have hleadTerm : (ρ ^ 6 * ‖Kstar‖ * Chistory * ηctrl) / (rate - b * sigma) *
      Real.exp (-(rate - b * sigma) * Lback) * Real.exp (b * sigma * d) ≤ (κ / 8) * ρ ^ 6 := by
    calc
      _ = ρ ^ 6 * (((‖Kstar‖ * Chistory * ηctrl) / (rate - b * sigma) *
          Real.exp (b * sigma * d)) * Real.exp (-(rate - b * sigma) * Lback)) := by ring
      _ ≤ ρ ^ 6 * (κ / 8) := mul_le_mul_of_nonneg_left hlead (pow_nonneg hρ.le 6)
      _ = _ := by ring
  have hpastTerm := hpastSmallξ exit Lback (hLback.le.trans hLexit) hclockLimit hLback.le hLexit
  have hentryAmp : Eamp * ‖W 0‖ ≤ (κ / 4) * ρ ^ 6 := by
    rw [hW0]
    exact hpastBound.trans (by nlinarith only [hleadTerm, hpastTerm])
  have hresponse0 : ‖response 0‖ * Eamp ≤ (κ / 8) * ρ ^ 6 := by
    dsimp only [response]
    rw [P.shiftedRetardedTransfer_norm, add_zero]
    exact htail ρ hρ.le
  have hresponseEnd : ‖response Dobs‖ = ρ ^ 6 * κ := by
    dsimp only [response]
    rw [P.shiftedRetardedTransfer_norm,
      show sCanon - Lback + Dobs = tstar by dsimp only [Dobs]; linarith only [htarget],
      P.norm_retarded_transfer_rho_factor hρ.le, hresponse]
  have hobsTerm : (Bobs * ηobs) * ρ ^ 6 ≤ (κ / 16) * ρ ^ 6 :=
    mul_le_mul_of_nonneg_right hηbudget (pow_nonneg hρ.le 6)
  have hresidualTerm : Kfuture * ρ ^ 8 ≤ (κ / 16) * ρ ^ 6 := by
    calc
      _ = (Kfuture * ρ ^ 2) * ρ ^ 6 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hfutureSmallξ (pow_nonneg hρ.le 6)
  have herror : ‖W Dobs - response Dobs‖ ≤ (κ / 2) * ρ ^ 6 := by
    calc
      _ ≤ (‖W 0 - response 0‖ + ε * Dobs) * Eamp := hcompare
      _ ≤ (‖W 0‖ + ‖response 0‖ + ε * Dobs) * Eamp :=
        mul_le_mul_of_nonneg_right (add_le_add (norm_sub_le _ _) le_rfl) (Real.exp_pos _).le
      _ = Eamp * ‖W 0‖ + ‖response 0‖ * Eamp + Kfuture * ρ ^ 8 + (Bobs * ηobs) * ρ ^ 6 := by
        dsimp only [ε, Kfuture, Bobs]
        ring
      _ ≤ (κ / 4) * ρ ^ 6 + (κ / 8) * ρ ^ 6 + (κ / 16) * ρ ^ 6 + (κ / 16) * ρ ^ 6 :=
        add_le_add (add_le_add (add_le_add hentryAmp hresponse0) hresidualTerm) hobsTerm
      _ = _ := by ring
  have htri := norm_sub_norm_le (response Dobs) (W Dobs)
  rw [norm_sub_rev, hresponseEnd] at htri
  change (κ / 2) * ρ ^ 6 ≤ ‖W Dobs‖
  nlinarith only [htri, herror]

end CircularMaterialTransferProfile
end Euler2D

end
