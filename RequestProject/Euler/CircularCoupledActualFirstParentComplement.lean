module

public import RequestProject.Euler.CircularCoupledActualFirstParentPreCapture
public import RequestProject.Euler.CircularExistingProportionalCaptureStep
public import RequestProject.Euler.FiniteWeightedCaptureRecurrence
public import RequestProject.Euler.CapturePolynomialBlockBudget
public import RequestProject.Euler.CircularCaptureBlockClock

/-! The literal fixed-graph complement of the SAME first-parent Euler
trajectory has a slower return-block bound. Its coefficient precedes
the warmup length; only the higher-order error threshold uses the
preliminary bounds on that fixed window. No capture cone is assumed. -/

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 64000000
set_option maxRecDepth 11000

noncomputable section

open Complex Set Filter Topology MeasureTheory Metric
open scoped NNReal ENNReal ContDiff BigOperators

namespace Euler2D

attribute [local instance 2000] rigidGaugeLittle_group rigidGaugeLittle_space rigidGaugeFamily_tower
attribute [local instance 2000] captureBlockFamily_tower captureBlockTangent_group captureBlockTangent_space
  captureBlockTangent_continuousAdd captureBlockEndo_monoid captureBlockTangent_complete
attribute [local instance] LittleContourSpace.complexScalarNormedSpace LittleContourSpace.complexScalarTower
attribute [local irreducible] circularConstrainedTangentSubmodule circularConstrainedUnstableProjectionCLM
  circularConstrainedReturnMap circularConstrainedChart circularConstraintProjectionToTangentCLM
  circularBanachField circularBanachDomain finiteBaseCurlL2
  CircularMaterialTransferProfile.finiteBaseLp

namespace CircularMaterialTransferProfile

variable {γ : ℝ≥0} {hγ : 0 < γ} {hγ1 : (γ : ℝ) < 1}
    (P : CircularMaterialTransferProfile hγ hγ1)

theorem exists_eventually_actualFinite_coupled_preCapture_complement {Rflow r₀ : ℝ}
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
      qc ^ 2 < circularCaptureBlockMultiplier ℓ ∧ ∃ Ccomp > 0,
      ∀ nWarm : ℕ, ∀ {Kw Kcur s cA q T η : ℝ}, ∀ [Fact (1 ≤ ENNReal.ofReal q)],
      ∀ (hs : s ≤ 0) (hcA : 0 < cA) (hq : 0 < q) (hqE : 2 ≤ ENNReal.ofReal q),
      0 ≤ Kw → 0 ≤ Kcur → 0 ≤ T → 0 ≤ η → η ≤ cellA / 4 →
      (∀ i, ‖(P.ancient s i).val - circularReferenceC1 hγ hγ1 i‖ ≤ η) →
      ∀ᶠ ξ : ℝ in atTop,
      let ρ := Real.exp (-ξ)
      let hρ := Real.exp_pos (-ξ)
      let R := ρ ^ 10
      let hR := pow_pos hρ 10
      let A₀ := cA * (1 + ξ)
      let h := 2 * ρ ^ 6
      let D := (nWarm : ℝ) * circularCaptureBlockTime ℓ
      ∀ N k : ℕ, ∀ hkN : k ≤ N, ∀ S : BoundedEulerParticleSystem
        (finiteBaseCurlL2 (A₀ := A₀) (b := b) (ρ := ρ) hR hρ hq hqE
          (P.finiteBaseLp (A₀ := A₀) (b := b) (ρ := ρ) (q := q) hs hR hρ) N) T,
      IsFourfoldBoundedEulerParticleSystem S →
      ∀ {H : ℝ}, 0 ≤ H → ∀ Y : ℝ → FiniteCircularIndex k → LittleContourSpace γ,
      P.ActualCanonicalPrefixTrajectory s A₀ b R ρ (1 / 16) T hR hρ
        hkN S H Y →
      ∀ entrance : ℝ, 0 ≤ entrance → entrance + D / ampScale A₀ b k ≤ H →
      (∀ u ∈ Icc (0 : ℝ) D,
        weightedFamilyNorm h k (canonicalPrefixStageDeviation hγ hγ1 A₀ b R ρ k entrance Y u) ≤ Kw * h) →
      (∀ u ∈ Icc (0 : ℝ) D,
        ‖canonicalPrefixStageDeviation hγ hγ1 A₀ b R ρ k entrance Y u k‖ ≤ Kcur * h) →
      ‖canonicalPrefixStageDeviation hγ hγ1 A₀ b R ρ k entrance Y 0 k‖ ≤ h →
      (∀ z ∈ P.finiteInnerActiveInitialLabels s A₀ b R ρ N k,
        ‖S.forward entrance z - torusCenter‖ ≤ 2 * ρ * radScale R ρ k) →
      let y := canonicalPrefixAlignedCurrentCell A₀ b R ρ k entrance Y
      let J := circularConstraintProjectionToTangentCLM hγ hγ1.le
      let Q := circularConstrainedUnstableProjectionCLM hγ hγ1.le
      let v := fun n : ℕ => J (y ((n : ℝ) * circularCaptureBlockTime ℓ) - littleCircularReference hγ hγ1)
      ∀ n ≤ nWarm, ‖v n - gseq (Q (v n)) 0‖ ≤ Ccomp * qc ^ n * ρ ^ 6 := by
  obtain ⟨ℓ, hℓ, qc, hqc, hgap, C, hC, d, hdpos, hdr, E, hE, r, hr,
    κ₀, hκ₀, ε₀, hε₀, Henv, hHenv, hstep⟩ :=
    exists_circular_existing_proportional_capture_step hγ hγ1 hRflow hr₀ hflow hd hfix harea hg
  obtain ⟨Cb, hCb, Bpoly, hBpoly, Ktorus, hKtorus, εchart, hεchart, hforcing⟩ :=
    P.exists_eventually_actualFinite_coupled_preCapture_forcing hb hb1
  let Tblock := circularCaptureBlockTime ℓ
  let J := circularConstraintProjectionToTangentCLM hγ hγ1.le
  let Q := circularConstrainedUnstableProjectionCLM hγ hγ1.le
  let g := fun v => gseq v 0 - v
  have hTblock : 0 < Tblock := circularCaptureBlockTime_pos hℓ
  obtain ⟨Fq, hFq, hsum⟩ := exists_capture_polynomial_block_budget hqc hTblock.le
  let Cinit := 2 * (1 + 2 * ‖Q‖) * ‖J‖
  let Btotal := E * Bpoly + 1
  let Ccomp := Cinit + Fq * Btotal + 1
  have hCinit : 0 ≤ Cinit := by dsimp only [Cinit]; positivity
  have hBtotal : 0 < Btotal := by dsimp only [Btotal]; positivity
  have hCcomp : 0 < Ccomp := by dsimp only [Ccomp]; positivity
  refine ⟨ℓ, hℓ, qc, hqc, hgap, Ccomp, hCcomp, ?_⟩
  intro nWarm Kw Kcur s cA q T η _ hs hcA hq hqE hKw hKcur hT hη hηa hancient
  let D := (nWarm : ℝ) * Tblock
  have hD : 0 ≤ D := mul_nonneg (Nat.cast_nonneg _) hTblock.le
  let Av := 2 * ‖J‖ * Kcur
  let Au := 2 * ‖Q‖ * ‖J‖ * Kcur
  let Aw := Av + 2 * Au
  let Asum := Au + Aw
  have hAv : 0 ≤ Av := by dsimp only [Av]; positivity
  have hAu : 0 ≤ Au := by dsimp only [Au]; positivity
  have hAw : 0 ≤ Aw := add_nonneg hAv (mul_nonneg (by norm_num) hAu)
  have hAsum : 0 ≤ Asum := add_nonneg hAu hAw
  have hsmall (A : ℝ) (n : ℕ) (hn : n ≠ 0) (e : ℝ) (he : 0 < e) :
      ∀ᶠ ξ : ℝ in atTop, A * Real.exp (-ξ) ^ n ≤ e := by
    have ht : Tendsto (fun ξ : ℝ => A * Real.exp (-ξ) ^ n) atTop (𝓝 0) := by
      simpa only [zero_pow hn, mul_zero] using
        (Real.tendsto_exp_neg_atTop_nhds_zero.pow n).const_mul A
    exact (ht.eventually (gt_mem_nhds he)).mono (fun _ h => h.le)
  have hforce := hforcing (D := D) (Kw := Kw) (Kcur := Kcur)
    hs hcA hq hqE hD hKw hKcur hT hη hηa hancient
  filter_upwards [hforce,
    hsmall (2 * Kcur) 6 (by decide) (εchart / 2) (half_pos hεchart),
    hsmall (2 * Kcur) 6 (by decide) r hr,
    hsmall Au 6 (by decide) (r₀ / 2) (half_pos hr₀),
    hsmall Asum 6 (by decide) d hdpos,
    hsmall Ktorus 8 (by decide) κ₀ hκ₀,
    hsmall (Bpoly * (1 + D) ^ 4) 6 (by decide) (ε₀ / 2) (half_pos hε₀),
    hsmall (Ktorus * Asum) 14 (by decide) (ε₀ / 2) (half_pos hε₀),
    hsmall (C * Asum * Aw) 6 (by decide) (1 / 2) (by norm_num),
    hsmall (E * Ktorus * Asum) 8 (by decide) (1 / 2) (by norm_num)]
      with ξ hforceξ hchartSmall hnearSmall hgraphSmall hsizeSmall hκcap hBcap hκsize hCerror hTerror
  let ρ := Real.exp (-ξ)
  let R := ρ ^ 10
  let A₀ := cA * (1 + ξ)
  let h := 2 * ρ ^ 6
  let κ := Ktorus * ρ ^ 8
  have hρ : 0 < ρ := Real.exp_pos (-ξ)
  have hκ : 0 ≤ κ := mul_nonneg hKtorus.le (pow_nonneg hρ.le 8)
  have hnearSmall' : Kcur * h ≤ r := by
    simpa only [h, mul_assoc, mul_left_comm, mul_comm] using hnearSmall
  have hchartSmall' : Kcur * h < εchart :=
    (by simpa only [h, mul_assoc, mul_left_comm, mul_comm] using hchartSmall : Kcur * h ≤ εchart / 2).trans_lt
      (half_lt_self hεchart)
  dsimp only
  intro N k hkN S hS H hH Y hY entrance hentrance htimeEnd hweighted hcur hinit hstart
  obtain ⟨p, hp, hparticle⟩ := hforceξ N k hkN S hS hH Y hY entrance hentrance htimeEnd hweighted hcur hstart
  let y := canonicalPrefixAlignedCurrentCell A₀ b R ρ k entrance Y
  let v := fun n : ℕ => J (y ((n : ℝ) * Tblock) - littleCircularReference hγ hγ1)
  let α := fun n : ℕ => Q (v n)
  let w := fun n : ℕ => (v n - α n) - g (α n)
  let B := fun n : ℕ => Bpoly * ρ ^ 6 * (1 + ((n + 1 : ℕ) : ℝ) * Tblock) ^ 4
  let f := fun n : ℕ => Btotal * ρ ^ 6 * (1 + ((n + 1 : ℕ) : ℝ) * Tblock) ^ 4
  have hnorm (u : ℝ) : ‖y u - littleCircularMaterialContours hγ hγ1 u‖ =
      ‖canonicalPrefixStageDeviation hγ hγ1 A₀ b R ρ k entrance Y u k‖ :=
    norm_canonicalPrefixAlignedCurrentCell_sub_reference hγ hγ1 A₀ b R ρ k entrance u Y
  have hnear (u : ℝ) (hu : u ∈ Icc (0 : ℝ) D) :
      ‖y u - littleCircularMaterialContours hγ hγ1 u‖ ≤ Kcur * h := by
    rw [hnorm]
    exact hcur u hu
  have hperiod : Function.Periodic (littleCircularMaterialContours hγ hγ1) Tblock :=
    (periodic_littleCircularMaterialContours hγ hγ1).nat_mul (2 * ℓ)
  have hcshift (n : ℕ) (u : ℝ) :
      littleCircularMaterialContours hγ hγ1 ((n : ℝ) * Tblock + u) =
        littleCircularMaterialContours hγ hγ1 u := by
    simpa only [add_comm] using (hperiod.nat_mul n) u
  have hcgrid (n : ℕ) : littleCircularMaterialContours hγ hγ1 ((n : ℝ) * Tblock) =
      littleCircularReference hγ hγ1 :=
    (hperiod.nat_mul_eq n).trans (littleCircularMaterialContours_zero hγ hγ1)
  have hgridTime (n : ℕ) (hn : n ≤ nWarm) : (n : ℝ) * Tblock ∈ Icc (0 : ℝ) D :=
    ⟨mul_nonneg (Nat.cast_nonneg _) hTblock.le,
      mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hn) hTblock.le⟩
  have hgridNear (n : ℕ) (hn : n ≤ nWarm) :
      ‖y ((n : ℝ) * Tblock) - littleCircularReference hγ hγ1‖ ≤ Kcur * h := by
    simpa only [hcgrid] using hnear _ (hgridTime n hn)
  have hchart (n : ℕ) (hn : n ≤ nWarm) :
      circularConstrainedChart hγ hγ1 (v n) = y ((n : ℝ) * Tblock) :=
    (hp _ (hgridTime n hn)).2.2.2
      (mem_ball_iff_norm.mpr ((hgridNear n hn).trans_lt hchartSmall'))
  have hv (n : ℕ) (hn : n ≤ nWarm) : ‖v n‖ ≤ Av * ρ ^ 6 := by
    calc
      _ ≤ ‖J‖ * ‖y ((n : ℝ) * Tblock) - littleCircularReference hγ hγ1‖ := J.le_opNorm _
      _ ≤ ‖J‖ * (Kcur * h) := mul_le_mul_of_nonneg_left (hgridNear n hn) (norm_nonneg J)
      _ = _ := by dsimp only [h, Av]; ring
  have hα (n : ℕ) (hn : n ≤ nWarm) : ‖α n‖ ≤ Au * ρ ^ 6 := by
    calc
      _ ≤ ‖Q‖ * ‖v n‖ := Q.le_opNorm _
      _ ≤ ‖Q‖ * (Av * ρ ^ 6) := mul_le_mul_of_nonneg_left (hv n hn) (norm_nonneg Q)
      _ = _ := by dsimp only [Av, Au]; ring
  have hαrange (n : ℕ) : Q (α n) = α n :=
    circularConstrainedUnstableProjectionCLM_idempotent hγ hγ1.le (v n)
  have hαgraph (n : ℕ) (hn : n ≤ nWarm) : ‖α n‖ ≤ r₀ / 2 :=
    (hα n hn).trans hgraphSmall
  have hwEq (n : ℕ) : w n = v n - gseq (α n) 0 := by dsimp only [w, g]; module
  have hwRange (n : ℕ) (hn : n ≤ nWarm) : Q (w n) = 0 := by
    rw [hwEq, Q.map_sub, hg.coordinate (α n) (hαrange n) (hαgraph n hn)]
    exact sub_self (α n)
  have hw (n : ℕ) (hn : n ≤ nWarm) : ‖w n‖ ≤ Aw * ρ ^ 6 := by
    have hgn : ‖gseq (α n) 0‖ ≤ 2 * ‖α n‖ := by
      simpa only [pow_zero, mul_one] using hg.norm_le (α n) (hαrange n) (hαgraph n hn) 0
    calc
      _ = ‖v n - gseq (α n) 0‖ := congrArg norm (hwEq n)
      _ ≤ ‖v n‖ + ‖gseq (α n) 0‖ := norm_sub_le _ _
      _ ≤ Av * ρ ^ 6 + 2 * (Au * ρ ^ 6) :=
        add_le_add (hv n hn) (hgn.trans (mul_le_mul_of_nonneg_left (hα n hn) (by norm_num)))
      _ = _ := by dsimp only [Aw]; ring
  have hsumSize (n : ℕ) (hn : n ≤ nWarm) : ‖α n‖ + ‖w n‖ ≤ Asum * ρ ^ 6 := by
    exact (add_le_add (hα n hn) (hw n hn)).trans_eq (by dsimp only [Asum]; ring)
  have hw0 : ‖w 0‖ ≤ Cinit * ρ ^ 6 := by
    have hy0 : ‖y 0 - littleCircularReference hγ hγ1‖ ≤ h := by
      rw [← littleCircularMaterialContours_zero hγ hγ1, hnorm]
      exact hinit
    have hv0 : ‖v 0‖ ≤ 2 * ‖J‖ * ρ ^ 6 := by
      have hop := J.le_opNorm (y 0 - littleCircularReference hγ hγ1)
      change ‖J (y (((0 : ℕ) : ℝ) * Tblock) - littleCircularReference hγ hγ1)‖ ≤ _
      simp only [Nat.cast_zero, zero_mul] at hop ⊢
      exact (hop.trans (mul_le_mul_of_nonneg_left hy0 (norm_nonneg J))).trans_eq
        (by dsimp only [h]; ring)
    have hα0 : ‖α 0‖ ≤ 2 * ‖Q‖ * ‖J‖ * ρ ^ 6 :=
      (Q.le_opNorm (v 0)).trans ((mul_le_mul_of_nonneg_left hv0 (norm_nonneg Q)).trans_eq (by ring))
    have hg0 : ‖gseq (α 0) 0‖ ≤ 2 * ‖α 0‖ := by
      simpa only [pow_zero, mul_one] using hg.norm_le (α 0) (hαrange 0) (hαgraph 0 (Nat.zero_le _)) 0
    rw [hwEq]
    exact ((norm_sub_le _ _).trans (add_le_add hv0
      (hg0.trans (mul_le_mul_of_nonneg_left hα0 (by norm_num))))).trans_eq
        (by dsimp only [Cinit]; ring)
  have hrec (n : ℕ) (hn : n < nWarm) : ‖w (n + 1)‖ ≤ qc * ‖w n‖ + f n := by
    have hlocalTime (u : ℝ) (hu : u ∈ Icc (0 : ℝ) Tblock) :
        (n : ℝ) * Tblock + u ∈ Icc (0 : ℝ) D := by
      refine ⟨add_nonneg (mul_nonneg (Nat.cast_nonneg _) hTblock.le) hu.1, ?_⟩
      have hh := mul_le_mul_of_nonneg_right
        (Nat.cast_le.mpr (Nat.succ_le_of_lt hn) : ((n + 1 : ℕ) : ℝ) ≤ (nWarm : ℝ)) hTblock.le
      push_cast at hh
      nlinarith only [hh, hu.2]
    have hBn : B n ≤ (Bpoly * (1 + D) ^ 4) * ρ ^ 6 := by
      have hnt : ((n + 1 : ℕ) : ℝ) * Tblock ≤ D :=
        (hgridTime (n + 1) (Nat.succ_le_of_lt hn)).2
      have hp4 := pow_le_pow_left₀ (show 0 ≤ 1 + ((n + 1 : ℕ) : ℝ) * Tblock by positivity)
        (by linarith only [hnt] : 1 + ((n + 1 : ℕ) : ℝ) * Tblock ≤ 1 + D) 4
      exact (mul_le_mul_of_nonneg_left hp4 (mul_nonneg hBpoly.le (pow_nonneg hρ.le 6))).trans_eq (by ring)
    have hκsize' : κ * (‖α n‖ + ‖w n‖) ≤ (Ktorus * Asum) * ρ ^ 14 :=
      (mul_le_mul_of_nonneg_left (hsumSize n hn.le) hκ).trans_eq (by dsimp only [κ]; ring)
    have hforcingSmall : B n + κ * (‖α n‖ + ‖w n‖) ≤ ε₀ := by
      have h₁ := hBn.trans hBcap
      have h₂ := hκsize'.trans hκsize
      linarith only [h₁, h₂]
    have hinitLocal : y ((n : ℝ) * Tblock + 0) =
        circularConstrainedChart hγ hγ1 (α n + g (α n) + w n) := by
      have he : α n + g (α n) + w n = v n := by dsimp only [w]; module
      rw [add_zero, he]
      exact (hchart n hn.le).symm
    have hderivLocal (u : ℝ) (hu : u ∈ Icc (0 : ℝ) Tblock) :
        HasDerivAt (fun z => y ((n : ℝ) * Tblock + z))
          (circularBanachField hγ hγ1 (y ((n : ℝ) * Tblock + u)) + p ((n : ℝ) * Tblock + u)) u := by
      have hh := (hp _ (hlocalTime u hu)).1.scomp u ((hasDerivAt_id u).const_add ((n : ℝ) * Tblock))
      simpa only [Function.comp_def, y, A₀, R, ρ, one_smul] using hh
    have hnearLocal (u : ℝ) (hu : u ∈ Icc (0 : ℝ) Tblock) :
        ‖y ((n : ℝ) * Tblock + u) - littleCircularMaterialContours hγ hγ1 u‖ ≤ r := by
      have hh := (hnear _ (hlocalTime u hu)).trans hnearSmall'
      simpa only [hcshift] using hh
    have hforcingLocal (u : ℝ) (hu : u ∈ Icc (0 : ℝ) Tblock) :
        ‖p ((n : ℝ) * Tblock + u)‖ ≤ B n + κ *
          ‖y ((n : ℝ) * Tblock + u) - littleCircularMaterialContours hγ hγ1 u‖ := by
      have hclock : (n : ℝ) * Tblock + u ≤ ((n + 1 : ℕ) : ℝ) * Tblock := by
        push_cast
        nlinarith only [hu.2]
      have hp4 := pow_le_pow_left₀
        (show 0 ≤ 1 + ((n : ℝ) * Tblock + u) by linarith only [(hlocalTime u hu).1])
        (by linarith only [hclock] : 1 + ((n : ℝ) * Tblock + u) ≤ 1 + ((n + 1 : ℕ) : ℝ) * Tblock) 4
      have hpoly := mul_le_mul_of_nonneg_left hp4 (mul_nonneg hBpoly.le (pow_nonneg hρ.le 6))
      have hh := (hp _ (hlocalTime u hu)).2.1
      rw [hcshift] at hh
      exact hh.trans ((add_le_add le_rfl hpoly).trans_eq (by dsimp only [κ, B]; ring))
    have hstepNow := hstep (α n) (w n) (hαrange n) (hwRange n hn.le)
      ((hsumSize n hn.le).trans hsizeSmall) (by dsimp only [B]; positivity)
      hκ hκcap hforcingSmall
      (fun u => y ((n : ℝ) * Tblock + u)) (fun u => p ((n : ℝ) * Tblock + u))
      hinitLocal hderivLocal hnearLocal hforcingLocal
    have hgrid : (n : ℝ) * Tblock + ((2 * ℓ : ℕ) : ℝ) * period =
        ((n + 1 : ℕ) : ℝ) * Tblock := by
      dsimp only [Tblock, circularCaptureBlockTime]
      push_cast
      ring
    simp only at hstepNow
    rw [hgrid] at hstepNow
    have hstable : ‖w (n + 1)‖ ≤ qc * ‖w n‖ +
        C * (‖α n‖ + ‖w n‖) * ‖w n‖ + E * B n + E * κ * (‖α n‖ + ‖w n‖) := by
      simpa only [w, α, v, mul_assoc] using hstepNow.2.1
    have hnonlinear : C * (‖α n‖ + ‖w n‖) * ‖w n‖ ≤ (C * Asum * Aw) * ρ ^ 12 := by
      calc
        _ ≤ (C * (Asum * ρ ^ 6)) * (Aw * ρ ^ 6) :=
          mul_le_mul (mul_le_mul_of_nonneg_left (hsumSize n hn.le) hC.le) (hw n hn.le)
            (norm_nonneg _) (by positivity)
        _ = _ := by ring
    have htorus : E * κ * (‖α n‖ + ‖w n‖) ≤ (E * Ktorus * Asum) * ρ ^ 14 := by
      exact (mul_le_mul_of_nonneg_left (hsumSize n hn.le) (mul_nonneg hE.le hκ)).trans_eq
        (by dsimp only [κ]; ring)
    have herrors : (C * Asum * Aw) * ρ ^ 12 + (E * Ktorus * Asum) * ρ ^ 14 ≤ ρ ^ 6 := by
      calc
        _ = ((C * Asum * Aw) * ρ ^ 6 + (E * Ktorus * Asum) * ρ ^ 8) * ρ ^ 6 := by ring
        _ ≤ ((1 / 2 : ℝ) + 1 / 2) * ρ ^ 6 :=
          mul_le_mul_of_nonneg_right (add_le_add hCerror hTerror) (pow_nonneg hρ.le 6)
        _ = _ := by ring
    have hpolyOne : (1 : ℝ) ≤ (1 + ((n + 1 : ℕ) : ℝ) * Tblock) ^ 4 :=
      one_le_pow₀ (le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg _) hTblock.le))
    calc
      _ ≤ qc * ‖w n‖ + C * (‖α n‖ + ‖w n‖) * ‖w n‖ + E * B n +
          E * κ * (‖α n‖ + ‖w n‖) := hstable
      _ ≤ qc * ‖w n‖ + (C * Asum * Aw) * ρ ^ 12 + E * B n +
          (E * Ktorus * Asum) * ρ ^ 14 :=
        add_le_add (add_le_add (add_le_add le_rfl hnonlinear) le_rfl) htorus
      _ = qc * ‖w n‖ + E * B n +
          ((C * Asum * Aw) * ρ ^ 12 + (E * Ktorus * Asum) * ρ ^ 14) := by ring
      _ ≤ qc * ‖w n‖ + E * B n + ρ ^ 6 := add_le_add le_rfl herrors
      _ ≤ qc * ‖w n‖ + E * B n + ρ ^ 6 * (1 + ((n + 1 : ℕ) : ℝ) * Tblock) ^ 4 :=
        add_le_add le_rfl (le_mul_of_one_le_right (pow_nonneg hρ.le 6) hpolyOne)
      _ = _ := by dsimp only [B, f, Btotal]; ring
  have hbound := finite_norm_recurrence_bound (w := w) (e := f) (zero_lt_one.trans hqc) hrec
  intro n hn
  have hsumN : (∑ j ∈ Finset.range n, f j / qc ^ (j + 1)) ≤ Fq * Btotal * ρ ^ 6 := by
    simpa only [f, zero_add, add_zero, one_pow, mul_one] using
      hsum (S := 0) (B := Btotal) (ρ := ρ) (le_refl (0 : ℝ)) hBtotal.le n
  have hcoeff : Cinit + Fq * Btotal ≤ Ccomp := by dsimp only [Ccomp]; linarith
  rw [← hwEq]
  calc
    _ ≤ qc ^ n * (‖w 0‖ + ∑ j ∈ Finset.range n, f j / qc ^ (j + 1)) := hbound n hn
    _ ≤ qc ^ n * (Cinit * ρ ^ 6 + Fq * Btotal * ρ ^ 6) :=
      mul_le_mul_of_nonneg_left (add_le_add hw0 hsumN) (pow_nonneg (zero_lt_one.trans hqc).le n)
    _ = (Cinit + Fq * Btotal) * qc ^ n * ρ ^ 6 := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hcoeff (pow_nonneg (zero_lt_one.trans hqc).le n)) (pow_nonneg hρ.le 6)

theorem exists_eventually_actualFirstParent_coupled_preCapture_complement {Rflow r₀ : ℝ}
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
      qc ^ 2 < circularCaptureBlockMultiplier ℓ ∧ ∃ Ccomp > 0,
      ∀ nWarm : ℕ, ∀ {Kw Kcur s cA q T η : ℝ}, ∀ [Fact (1 ≤ ENNReal.ofReal q)],
      ∀ (hs : s ≤ 0) (hcA : 0 < cA) (hq : 0 < q) (hqE : 2 ≤ ENNReal.ofReal q),
      0 ≤ Kw → 0 ≤ Kcur → 0 ≤ T → 0 ≤ η → η ≤ cellA / 4 →
      (∀ i, ‖(P.ancient s i).val - circularReferenceC1 hγ hγ1 i‖ ≤ η) →
      ∀ᶠ ξ : ℝ in atTop,
      let ρ := Real.exp (-ξ)
      let hρ := Real.exp_pos (-ξ)
      let R := ρ ^ 10
      let hR := pow_pos hρ 10
      let A₀ := cA * (1 + ξ)
      let h := 2 * ρ ^ 6
      let D := (nWarm : ℝ) * circularCaptureBlockTime ℓ
      ∀ k : ℕ, ∀ S : BoundedEulerParticleSystem
        (finiteBaseCurlL2 (A₀ := A₀) (b := b) (ρ := ρ) hR hρ hq hqE
          (P.finiteBaseLp (A₀ := A₀) (b := b) (ρ := ρ) (q := q) hs hR hρ) (k + 1)) T,
      IsFourfoldBoundedEulerParticleSystem S →
      ∀ {H : ℝ}, 0 ≤ H → ∀ Y : ℝ → FiniteCircularIndex k → LittleContourSpace γ,
      P.ActualCanonicalPrefixTrajectory s A₀ b R ρ (1 / 16) T hR hρ
        (Nat.le_succ k) S H Y →
      ∀ entrance : ℝ, 0 ≤ entrance → entrance + D / ampScale A₀ b k ≤ H →
      (∀ u ∈ Icc (0 : ℝ) D,
        weightedFamilyNorm h k (canonicalPrefixStageDeviation hγ hγ1 A₀ b R ρ k entrance Y u) ≤ Kw * h) →
      (∀ u ∈ Icc (0 : ℝ) D,
        ‖canonicalPrefixStageDeviation hγ hγ1 A₀ b R ρ k entrance Y u k‖ ≤ Kcur * h) →
      ‖canonicalPrefixStageDeviation hγ hγ1 A₀ b R ρ k entrance Y 0 k‖ ≤ h →
      (∀ z ∈ P.finiteInnerActiveInitialLabels s A₀ b R ρ (k + 1) k,
        ‖S.forward entrance z - torusCenter‖ ≤ 2 * ρ * radScale R ρ k) →
      let y := canonicalPrefixAlignedCurrentCell A₀ b R ρ k entrance Y
      let J := circularConstraintProjectionToTangentCLM hγ hγ1.le
      let Q := circularConstrainedUnstableProjectionCLM hγ hγ1.le
      let v := fun n : ℕ => J (y ((n : ℝ) * circularCaptureBlockTime ℓ) - littleCircularReference hγ hγ1)
      ∀ n ≤ nWarm, ‖v n - gseq (Q (v n)) 0‖ ≤ Ccomp * qc ^ n * ρ ^ 6 := by
  obtain ⟨ℓ, hℓ, qc, hqc, hgap, Ccomp, hCcomp, hcomp⟩ :=
    P.exists_eventually_actualFinite_coupled_preCapture_complement hRflow hr₀ hflow hd hfix harea hg hb hb1
  refine ⟨ℓ, hℓ, qc, hqc, hgap, Ccomp, hCcomp, ?_⟩
  intro nWarm Kw Kcur s cA q T η _ hs hcA hq hqE hKw hKcur hT hη hηa hancient
  filter_upwards [hcomp nWarm hs hcA hq hqE hKw hKcur hT hη hηa hancient] with ξ hcompξ
  dsimp only
  intro k
  exact hcompξ (k + 1) k (Nat.le_succ k)

end CircularMaterialTransferProfile
end Euler2D

end
