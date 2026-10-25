module

public import RequestProject.Euler.CircularActualCapturedChildHandoff

/-! Upgrade a real capture after its actual warmup to the SAME next-
handoff-ready captured child. The fourth-moment coefficient is chosen
BEFORE b, while lookback/graph constants precede cA and the finite cutoff.
The original genuine capture is supplied by the proved warmup capture API. -/

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
attribute [local instance 2000] valueScalarC1_group valueScalarC1_space
attribute [local instance] ContourC1Space.complexScalarNormedSpace ContourC1Space.complexScalarTower
attribute [local irreducible] contourC1GraphSubmodule holderGraphSubmodule circularCoRotationCLM
  circularConstrainedTangentSubmodule circularConstrainedUnstableProjectionCLM
  circularConstrainedReturnMap circularConstrainedChart circularConstraintProjectionToTangentCLM
  circularBanachField circularBanachDomain

namespace CircularMaterialTransferProfile

variable {γ : ℝ≥0} {hγ : 0 < γ} {hγ1 : (γ : ℝ) < 1}
    (P : CircularMaterialTransferProfile hγ hγ1)

theorem exists_uniform_actualWarmup_capture_handoff_upgrade
    (gseq : CircularConstrainedTangentSpace γ → ℕ → CircularConstrainedTangentSpace γ)
    {ηcur : ℝ} (hη : 0 < ηcur) (hηa : ηcur ≤ cellA / 4) :
    ∃ Cmoment > 0,
      ∀ b : ℝ≥0, 0 < b → b ≤ 1 →
      ∀ {Dpre Cpre Ccur Cobs δ sCanon εtarget Ctarget Hcap Cbcap D₀ Cgraph Lback Lentry Dentry : ℝ} {ℓcap : ℕ},
      0 ≤ Dpre → 0 ≤ Cpre → 0 ≤ Ccur → 0 ≤ Cobs →
      0 < δ → sCanon ≤ 0 → 0 ≤ Ctarget → 0 < Hcap → 0 ≤ Cbcap → 0 ≤ Cgraph →
      0 < Lback → 0 < ℓcap →
      P.IsSelectedCanonicalCaptureTarget gseq δ sCanon εtarget Ctarget →
      (Hcap * (4 * circularCaptureBlockMultiplier ℓcap / 3)) * δ < εtarget →
      sigma * (Lentry + 6 / sigma) < 8 →
      ∃ Cback > 0,
      ∀ {s cA q T : ℝ}, ∀ [Fact (1 ≤ ENNReal.ofReal q)],
      ∀ (hs : s ≤ 0) (hcA : 0 < cA) (hq : 0 < q) (hqE : 2 ≤ ENNReal.ofReal q),
      0 < T → (∀ i, ‖(P.ancient s i).val - circularReferenceC1 hγ hγ1 i‖ ≤ ηcur) →
      ∀ᶠ ξ : ℝ in atTop,
        let ρ := Real.exp (-ξ)
        let hρ := Real.exp_pos (-ξ)
        let R := ρ ^ 10
        let hR := pow_pos hρ 10
        let A₀ := cA * (1 + ξ)
        let h := 2 * ρ ^ 6
        ∀ N k : ℕ, ∀ hkN : k ≤ N,
        ∀ S : BoundedEulerParticleSystem
          (finiteBaseCurlL2 (A₀ := A₀) (b := (b : ℝ)) (ρ := ρ) hR hρ hq hqE
            (P.finiteBaseLp (A₀ := A₀) (b := (b : ℝ)) (ρ := ρ) (q := q) hs hR hρ) N) T,
        IsFourfoldBoundedEulerParticleSystem S →
        ∀ a : ℝ, 0 ≤ a →
        let H := a + Dpre / ampScale A₀ b k
        ∀ Y : ℝ → FiniteCircularIndex k → LittleContourSpace γ,
        P.ActualCanonicalPrefixTrajectory s A₀ b R ρ (1 / 16) T hR hρ hkN S H Y →
        (∀ t ∈ Icc (0 : ℝ) a,
          let x := canonicalPrefixStageDeviation hγ hγ1 A₀ b R ρ k 0 Y (ampScale A₀ b k * t)
          weightedFamilyNorm h k x ≤ h ∧ ‖x k‖ ≤ h) →
        (∀ u ∈ Icc (0 : ℝ) Dpre,
          weightedFamilyNorm h k (canonicalPrefixStageDeviation hγ hγ1 A₀ b R ρ k a Y u) ≤ Cobs * h) →
        (∀ u ∈ Icc (0 : ℝ) Dpre,
          ‖canonicalPrefixStageDeviation hγ hγ1 A₀ b R ρ k a Y u k‖ ≤ Ccur * h) →
        (∀ t ∈ Icc (0 : ℝ) a, ∀ z ∈ P.finiteInnerActiveInitialLabels s A₀ b R ρ N k,
          ‖S.forward t z - torusCenter‖ ≤ 2 * ρ * radScale R ρ k) →
        (∀ u ∈ Icc (0 : ℝ) Dpre, ∀ z ∈ P.finiteInnerActiveInitialLabels s A₀ b R ρ N k,
          ‖S.forward (physicalTimeFromNormalized (ampScale A₀ b k) a u) z - torusCenter‖ ≤
            Cpre * ρ * radScale R ρ k * (1 + u)) →
        ampScale A₀ b k * H ≤ Lentry * ξ + Dentry →
        P.HasActualParentCaptureExtension gseq (s := s) (A₀ := A₀) (b := (b : ℝ))
          hR hρ hkN S H Y ℓcap δ ηcur Hcap Cbcap D₀ Cgraph ξ →
        P.HasActualParentNextHandoffCaptureExtension gseq (s := s) (A₀ := A₀) (b := (b : ℝ))
          hR hρ hkN S H Y ℓcap δ ηcur Hcap Cbcap D₀ Cgraph ξ sCanon Ctarget Lback Cback Cmoment := by
  obtain ⟨Cmoment, hCmoment, hmomentAll⟩ := P.exists_eventually_actualParent_whole_past_boxed_moment gseq hη.le
  refine ⟨Cmoment, hCmoment, ?_⟩
  intro b hb hb1 Dpre Cpre Ccur Cobs δ sCanon εtarget Ctarget Hcap Cbcap D₀ Cgraph Lback Lentry Dentry ℓcap
    hDpre hCpre hCcur hCobs hδ hsCanon hCtarget hHcap hCbcap hCgraph hLback hℓcap htarget hTargetRadius hmargin
  let J := circularConstraintProjectionToTangentCLM hγ hγ1.le
  let Q := circularConstrainedUnstableProjectionCLM hγ hγ1.le
  let Cseed := 2 * ‖Q‖ * ‖J‖ * Ccur
  let Kpast := 2 * max (1 : ℝ) Ccur
  have hCseed : 0 ≤ Cseed := by dsimp only [Cseed]; positivity
  have hKpast : 0 ≤ Kpast := by dsimp only [Kpast]; positivity
  obtain ⟨Cback, hCback, hlookAll⟩ := P.exists_eventually_actualCoupled_parentMatchedCapture_with_lookback
    hsCanon hδ hη hηa hHcap.le hCtarget hCgraph hLback hℓcap gseq
  refine ⟨Cback, hCback, ?_⟩
  intro s cA q T _ hs hcA hq hqE hT hancient
  have hbR : 0 < (b : ℝ) := hb
  have hmatch := P.eventually_actualCoupled_parentCapture_matches_selected_target
    hs hb hcA hT hq hqE hℓcap hδ hη hηa hHcap htarget hTargetRadius hancient
  have hlook := hlookAll b hb hb1 Cbcap D₀ Cseed hCbcap hCseed hs hcA hq hqE hT.le hancient
  have hhistory := P.eventually_actualParentCapture_whole_past_history
    (δ := δ) (ηcur := ηcur) (Hcap := Hcap) (Cb := Cbcap) (D₀ := D₀) (Cgraph := Cgraph)
    (sCanon := sCanon) (Ctarget := Ctarget) (Lback := Lback) (Cback := Cback)
    (Kpast := Kpast) (Lentry := Lentry) (Dentry := Dentry)
    hη hKpast hℓcap hmargin gseq
  have hmoment := hmomentAll hs hcA hbR hq hqE hT.le
  have hnext := P.eventually_actualParentCapture_next_handoff_controls gseq
    (T := T) (ηcur := ηcur) (Cb := Cbcap) (D₀ := D₀) hs hcA hbR hq hqE hη.le hCbcap
  have hsmall (K : ℝ) (n : ℕ) (hn : n ≠ 0) (ε : ℝ) (hε : 0 < ε) :
      ∀ᶠ ξ : ℝ in atTop, K * Real.exp (-ξ) ^ n ≤ ε := by
    have ht : Tendsto (fun ξ : ℝ => K * Real.exp (-ξ) ^ n) atTop (𝓝 0) := by
      simpa only [zero_pow hn, mul_zero] using (Real.tendsto_exp_neg_atTop_nhds_zero.pow n).const_mul K
    exact (ht.eventually (gt_mem_nhds hε)).mono (fun _ h => h.le)
  filter_upwards [hmatch, hlook, hhistory, hmoment, hnext,
    hsmall 2 6 (by decide) 1 (by norm_num), hsmall (2 * Cobs) 6 (by decide) 1 (by norm_num),
    hsmall (Cpre * (1 + Dpre)) 1 (by decide) 2 (by norm_num), eventually_ge_atTop (0 : ℝ)]
    with ξ hmatchξ hlookξ hhistoryξ hmomentξ hnextξ hhOne hobsOne hparticleSmall hξ
  let ρ := Real.exp (-ξ)
  let R := ρ ^ 10
  let A₀ := cA * (1 + ξ)
  let h := 2 * ρ ^ 6
  have hρ : 0 < ρ := Real.exp_pos (-ξ)
  have hR : 0 < R := pow_pos hρ 10
  have hA : 0 < A₀ := mul_pos hcA (by linarith only [hξ])
  have hρOne : ρ ≤ 1 := Real.exp_le_one_iff.mpr (by linarith only [hξ])
  have hobsOne' : Cobs * h ≤ 1 := by
    simpa only [h, mul_assoc, mul_comm, mul_left_comm] using hobsOne
  have hparticleSmall' : Cpre * ρ * (1 + Dpre) ≤ 2 := by
    simpa only [pow_one, mul_assoc, mul_comm, mul_left_comm] using hparticleSmall
  dsimp only
  intro N k hkN S hS a ha Y hY hpast hweightedWarm hcurWarm hparticlesPast hparticlesWarm hEntryClock hcap
  let H := a + Dpre / ampScale A₀ b k
  have hAmp : 0 < ampScale A₀ b k := div_pos hA (pow_pos hbR k)
  have hH : 0 ≤ H := add_nonneg ha (div_nonneg hDpre hAmp.le)
  have hHclock : ampScale A₀ b k * H = ampScale A₀ b k * a + Dpre := by
    dsimp only [H]
    field_simp [hAmp.ne'] <;> ring
  have hmaterialPast := canonicalPrefixMaterialCurrentCell_past_warmup_bound hγ hγ1
    (R := R) hA hbR hρ.le ha hDpre hCcur k Y (fun t ht => (hpast t ht).2) hcurWarm
  have hown : canonicalPrefixStageDeviation hγ hγ1 A₀ b R ρ k H Y 0 k =
      canonicalPrefixStageDeviation hγ hγ1 A₀ b R ρ k a Y Dpre k := by
    apply canonicalPrefixStageDeviation_crossPrefix_eq hγ hγ1 hA.ne' hbR.ne' R ρ le_rfl Y Y
      H a Dpre H 0 rfl ?_ (fun _ => rfl) k le_rfl
    simp only [physicalTimeFromNormalized, zero_div, add_zero]
  have hnormZero : ‖canonicalPrefixAlignedCurrentCell A₀ b R ρ k H Y 0 - littleCircularReference hγ hγ1‖ =
      ‖canonicalPrefixStageDeviation hγ hγ1 A₀ b R ρ k H Y 0 k‖ := by
    rw [← littleCircularMaterialContours_zero, norm_canonicalPrefixAlignedCurrentCell_sub_reference]
  have hseed : ‖Q (J (canonicalPrefixAlignedCurrentCell A₀ b R ρ k H Y 0 -
      littleCircularReference hγ hγ1))‖ ≤ Cseed * ρ ^ 6 := by
    calc
      _ ≤ ‖Q‖ * ‖J (canonicalPrefixAlignedCurrentCell A₀ b R ρ k H Y 0 - littleCircularReference hγ hγ1)‖ := Q.le_opNorm _
      _ ≤ ‖Q‖ * (‖J‖ * ‖canonicalPrefixAlignedCurrentCell A₀ b R ρ k H Y 0 - littleCircularReference hγ hγ1‖) :=
        mul_le_mul_of_nonneg_left (J.le_opNorm _) (norm_nonneg _)
      _ = ‖Q‖ * (‖J‖ * ‖canonicalPrefixStageDeviation hγ hγ1 A₀ b R ρ k a Y Dpre k‖) := by rw [hnormZero, hown]
      _ ≤ ‖Q‖ * (‖J‖ * (Ccur * h)) := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (hcurWarm Dpre ⟨hDpre, le_rfl⟩) (norm_nonneg _)) (norm_nonneg _)
      _ = _ := by dsimp only [Cseed, h]; ring
  have hweightedAll := canonicalPrefix_whole_past_weighted_splice hγ hγ1
    (A₀ := A₀) (b := (b : ℝ)) (R := R) (ρ := ρ) (h := h) (D := Dpre) (shift := Dpre)
    hA hbR ha hDpre le_rfl k Y Y (fun _ _ => rfl)
    (fun t ht => (hpast t ht).1.trans hhOne)
    (fun v hv => (hweightedWarm v hv).trans hobsOne')
  have hweightedBeforeH : ∀ t ∈ Icc (0 : ℝ) H,
      weightedFamilyNorm h k (canonicalPrefixStageDeviation hγ hγ1 A₀ b R ρ k 0 Y (ampScale A₀ b k * t)) ≤ 1 := by
    intro t ht
    apply hweightedAll (ampScale A₀ b k * t) ⟨mul_nonneg hAmp.le ht.1, ?_⟩
    rw [← hHclock]
    exact mul_le_mul_of_nonneg_left ht.2 hAmp.le
  have hpastParticlesSmall : ∀ t ∈ Icc (0 : ℝ) a,
      ∀ z ∈ P.finiteInnerActiveInitialLabels s A₀ b R ρ N k,
      ‖S.forward t z - torusCenter‖ ≤ 2 * radScale R ρ k := by
    intro t ht z hz
    exact (hparticlesPast t ht z hz).trans (by
      have hh := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hρOne (by norm_num : (0 : ℝ) ≤ 2))
        (radScale_pos hR hρ k).le
      simpa only [mul_one] using hh)
  have hparticlesBeforeH := P.actual_inner_particle_handoff_radius_splice hA hbR hR hρ hCpre
    hDpre le_rfl hparticleSmall' N k S hpastParticlesSmall hparticlesWarm
  have hmatched := hmatchξ N k hkN S hS H hH Y Cbcap D₀ Cgraph hcap
  have hearlier := hlookξ N k hkN S hS H hH Y hseed hmatched
  have hfull := hhistoryξ hA hbR hR N k hkN S H hH Y hEntryClock hmaterialPast hearlier
  have hboxed := hmomentξ N k hkN S H hH Y ℓcap δ Hcap Cbcap D₀ Cgraph sCanon Ctarget Lback Cback hfull
  exact hnextξ N k hkN S H hH Y hweightedBeforeH hparticlesBeforeH
    ℓcap δ Hcap Cgraph sCanon Ctarget Lback Cback Cmoment hLback hboxed

end CircularMaterialTransferProfile
end Euler2D

end
