module

public import RequestProject.Euler.CircularActualContourInnerMomentSection
public import RequestProject.Euler.CircularActualUniformCapturedCascade
public import RequestProject.Euler.CircularActualParentMatchedCapture

public import RequestProject.Euler.CircularActualCoupledParentCapture
public import RequestProject.Euler.CircularSelectedCanonicalCaptureTarget

public import RequestProject.Euler.CircularParentCaptureScaleTrajectory
public import RequestProject.Euler.CircularCoupledParentCaptureEntrance
public import RequestProject.Euler.CircularParentCaptureLogarithmicCount
public import RequestProject.Euler.CircularCoupledParentCaptureScaleChoice
public import RequestProject.Euler.CircularCapturePhysicalScaleBaseTimeBudget
public import RequestProject.Euler.CircularActualDeepestScaleCapturedFamily

/-! Actual capture on the SAME Euler system after its genuine warmup.
The capture count comes from the real entrance seed, all physical budgets
are discharged at R=rho^10 and A0=cA*(1+xi), and the entire actual past is
retained. Capture constants are selected before the transfer ratio and
the future particle entry coefficient. -/

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
  circularBanachField circularBanachDomain finiteBaseCurlL2 CircularMaterialTransferProfile.finiteBaseLp

namespace CircularMaterialTransferProfile

variable {γ : ℝ≥0} {hγ : 0 < γ} {hγ1 : (γ : ℝ) < 1}
    (P : CircularMaterialTransferProfile hγ hγ1)


def HasActualCapturedInnerMomentSection
    {s A₀ b R ρ T : ℝ} (hR : 0 < R) (hρ : 0 < ρ)
    {N k : ℕ} (hkN : k ≤ N) {f : Lp ℝ 2 μT}
    (S : BoundedEulerParticleSystem f T)
    (ℓ : ℕ) (δ η Cb D₀ ξ m : ℝ) : Prop :=
  ∃ entrance : ℝ, 0 ≤ entrance ∧ ∃ Ncap : ℕ, 0 < Ncap ∧
    let Dcap := (Ncap : ℝ) * circularCaptureBlockTime ℓ
    Dcap ≤ (6 / sigma) * ξ + D₀ ∧
    entrance + Dcap / ampScale A₀ b k < T / 2 ∧
    ∃ X : ℝ → FiniteCircularIndex k → LittleContourSpace γ,
      P.ActualCanonicalPrefixTrajectory s A₀ b R ρ (1 / 16) T hR hρ hkN S
        (entrance + Dcap / ampScale A₀ b k) X ∧
      ∃ u ∈ Ioc (0 : ℝ) Dcap,
        let Z := circularCoRotationCLM γ u (canonicalPrefixAlignedCurrentCell A₀ b R ρ k entrance X u)
        let t := physicalTimeFromNormalized (ampScale A₀ b k) entrance u
        t ∈ Ioo 0 (T / 2) ∧
        (∀ i, Z i ∈ fourfoldLittleContourSubmodule γ) ∧
        (∀ i, littleContourArea γ (Z i) = Real.pi * circularContourRadii i ^ 2) ∧
        circularConstrainedChart hγ hγ1
          (circularConstraintProjectionToTangentCLM hγ hγ1.le (Z - littleCircularReference hγ hγ1)) = Z ∧
        (m / 2) * δ ≤ ‖littlePatchFourthMoment hγ hγ1.le cellA cellA_pos (Z 0)‖ ∧
        ‖canonicalPrefixStageDeviation hγ hγ1 A₀ b R ρ k entrance X u k‖ ≤ η ∧
        weightedFamilyNorm (2 * ρ ^ 6) k
          (canonicalPrefixStageDeviation hγ hγ1 A₀ b R ρ k entrance X u) ≤ 1 ∧
        ∀ z ∈ P.finiteInnerActiveInitialLabels s A₀ b R ρ N k,
          ‖S.forward t z - torusCenter‖ ≤ Cb * ρ * radScale R ρ k * (1 + u)

theorem exists_uniform_actualCaptured_innerMoment {Rflow r₀ : ℝ}
    (hRflow : 0 < Rflow) (hr₀ : 0 < r₀)
    {Xflow : (Fin 2 → LittleContourSpace γ) → ℝ → Fin 2 → LittleContourSpace γ}
    (hflow : IsBanachFlowOn (circularBanachField hγ hγ1) (circularBanachDomain hγ hγ1)
      (ball (littleCircularReference hγ hγ1) Rflow) period Xflow)
    (hd : ContDiffAt ℝ 2 (fun W => Xflow W period) (littleCircularReference hγ hγ1))
    (hfix : Xflow (littleCircularReference hγ hγ1) period = littleCircularReference hγ hγ1)
    (hareaFlow : ∀ W ∈ ball (littleCircularReference hγ hγ1) Rflow, ∀ i,
      littleContourArea γ (Xflow W period i) = littleContourArea γ (W i))
    {gseq : CircularConstrainedTangentSpace γ → ℕ → CircularConstrainedTangentSpace γ}
    (hg : IsLocalWeightedBackwardGraph
      (banachDoubleReturn (circularConstrainedReturnMap hγ hγ1 (fun W => Xflow W period)))
      (circularConstrainedUnstableProjectionCLM hγ hγ1.le) circularAncientBackwardWeight r₀ gseq) :
    ∃ δmax > 0, ∃ m > 0,
      ∀ b : ℝ≥0, 0 < b →
      ∀ δ sCanon εtarget Ctarget η Hcap Cgraph : ℝ, ∀ ℓ : ℕ,
      0 < ℓ → 0 < δ → δ < δmax → 0 < η → η ≤ cellA / 4 → 0 < Hcap → 0 ≤ Cgraph →
      P.IsSelectedCanonicalCaptureTarget gseq δ sCanon εtarget Ctarget →
      (Hcap * (4 * circularCaptureBlockMultiplier ℓ / 3)) * δ < εtarget →
      ∀ {s cA q T : ℝ}, ∀ [Fact (1 ≤ ENNReal.ofReal q)],
      ∀ (hs : s ≤ 0) (hcA : 0 < cA) (hT : 0 < T) (hq : 0 < q) (hqE : 2 ≤ ENNReal.ofReal q),
      (∀ i, ‖(P.ancient s i).val - circularReferenceC1 hγ hγ1 i‖ ≤ η) →
      ∀ Cb D₀ Lback Cback Cmoment : ℝ,
      ∀ᶠ ξ : ℝ in atTop,
        let ρ := Real.exp (-ξ)
        let hρ := Real.exp_pos (-ξ)
        let R := ρ ^ 10
        let hR := pow_pos hρ 10
        let A₀ := cA * (1 + ξ)
        ∀ N k : ℕ, ∀ hkN : k ≤ N,
        ∀ S : BoundedEulerParticleSystem
          (finiteBaseCurlL2 (A₀ := A₀) (b := (b : ℝ)) (ρ := ρ) hR hρ hq hqE
            (P.finiteBaseLp (A₀ := A₀) (b := (b : ℝ)) (ρ := ρ) (q := q) hs hR hρ) N) T,
        IsFourfoldBoundedEulerParticleSystem S →
        ∀ entrance : ℝ, 0 ≤ entrance →
        ∀ Ypast : ℝ → FiniteCircularIndex k → LittleContourSpace γ,
        P.HasActualParentNextHandoffCaptureExtension gseq (s := s) (A₀ := A₀) (b := (b : ℝ))
          hR hρ hkN S entrance Ypast ℓ δ η Hcap Cb D₀ Cgraph ξ sCanon Ctarget Lback Cback Cmoment →
        P.HasActualCapturedInnerMomentSection (s := s) (A₀ := A₀) (b := (b : ℝ)) hR hρ hkN S
          ℓ δ η Cb D₀ ξ m := by
  obtain ⟨δmax, hδmax, m, hm, hContourAll⟩ :=
    P.exists_uniform_actualContour_innerMoment_section hRflow hr₀ hflow hd hfix hareaFlow hg
  refine ⟨δmax, hδmax, m, hm, ?_⟩
  intro b hb δ sCanon εtarget Ctarget η Hcap Cgraph ℓ hℓ hδ hδbound hη hηa hHcap hCgraph
    htarget hTargetRadius s cA q T _ hs hcA hT hq hqE hancient Cb D₀ Lback Cback Cmoment
  have hContourEv := hContourAll δ hδ hδbound sCanon εtarget Ctarget htarget Cgraph hCgraph
  obtain ⟨Cgeo, hCgeo, hconstraints⟩ := P.exists_uniform_actualCanonical_prefix_constraints
  let targetFactor := Hcap * (4 * circularCaptureBlockMultiplier ℓ / 3)
  have hFactor : 0 < targetFactor := by
    dsimp only [targetFactor]
    rw [circularCaptureBlockMultiplier_eq_exp]
    positivity
  let δgeom := min η (targetFactor * δ)
  have hδgeom : 0 < δgeom := lt_min hη (mul_pos hFactor hδ)
  have hδgeomA : δgeom ≤ cellA / 4 := (min_le_left _ _).trans hηa
  have hδgeomE : δgeom < εtarget := (min_le_right _ _).trans_lt hTargetRadius
  have hbR : 0 < (b : ℝ) := hb
  let dcoef := 4 * Cgeo * cA * T
  let dsupport := fun ξ : ℝ => 2 + dcoef * (1 + ξ)
  have hρlim : Tendsto (fun ξ : ℝ => Real.exp (-ξ)) atTop (𝓝 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero
  have hhalf : ∀ᶠ ξ : ℝ in atTop, Real.exp (-ξ) ≤ (b : ℝ) / 2 :=
    (hρlim.eventually (gt_mem_nhds (half_pos hbR))).mono (fun _ h => h.le)
  have hmax : ∀ᶠ ξ : ℝ in atTop, Real.exp (-ξ) ≤ 1 / 2 :=
    (hρlim.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))).mono (fun _ h => h.le)
  have hdlim : Tendsto (fun ξ : ℝ => dsupport ξ * Real.exp (-ξ) ^ 10) atTop (𝓝 0) := by
    convert tendsto_circularCapture_log_monomial 1 dcoef (1 + dcoef) 10 1 (by decide) using 1
    ext ξ
    dsimp only [dsupport]
    ring
  have hdriftScale : ∀ᶠ ξ : ℝ in atTop, dsupport ξ * Real.exp (-ξ) ^ 10 ≤ 1 / 4 :=
    (hdlim.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 4))).mono (fun _ h => h.le)
  have hhlim : Tendsto (fun ξ : ℝ => 2 * Real.exp (-ξ) ^ 6) atTop (𝓝 0) := by
    simpa only [zero_pow (by decide : 6 ≠ 0), mul_zero] using (hρlim.pow 6).const_mul 2
  have hweight : ∀ᶠ ξ : ℝ in atTop, 2 * Real.exp (-ξ) ^ 6 ≤ δgeom :=
    (hhlim.eventually (gt_mem_nhds hδgeom)).mono (fun _ h => h.le)
  filter_upwards [hhalf, hmax, hdriftScale, hweight, hContourEv, eventually_ge_atTop (0 : ℝ)]
    with ξ hρhalf hρmax hdR hhK hContourξ hξ
  let ρ := Real.exp (-ξ)
  have hρ : 0 < ρ := Real.exp_pos (-ξ)
  let R := ρ ^ 10
  have hR : 0 < R := pow_pos hρ 10
  let A₀ := cA * (1 + ξ)
  have hA : 0 < A₀ := mul_pos hcA (by linarith only [hξ])
  have hρone : ρ ≤ 1 := hρmax.trans (by norm_num)
  have hRρ : R ≤ ρ := by
    simpa only [R, pow_one] using pow_le_pow_of_le_one hρ.le hρone (by decide : (1 : ℕ) ≤ 10)
  have hRmax : R ≤ 1 / 2 := hRρ.trans hρmax
  have hρb : ρ < (b : ℝ) := hρhalf.trans_lt (half_lt_self hbR)
  have hdenHalf : (1 / 2 : ℝ) ≤ 1 - ρ / b := by
    have hfrac : ρ / b ≤ 1 / 2 := (div_le_iff₀ hbR).mpr (by linarith only [hρhalf])
    linarith only [hfrac]
  let d := 2 + 4 * Cgeo * A₀ * T
  have hdeq : dsupport ξ = d := by dsimp only [dsupport, dcoef, d, A₀]; ring
  rw [hdeq] at hdR
  have hcat : 0 < Cgeo * A₀ * T := mul_pos (mul_pos hCgeo hA) hT
  have hdiv : Cgeo * A₀ / (1 - ρ / b) ≤ 2 * Cgeo * A₀ := by
    calc
      _ ≤ Cgeo * A₀ / (1 / 2) :=
        div_le_div_of_nonneg_left (mul_nonneg hCgeo.le hA.le) (by norm_num) hdenHalf
      _ = _ := by ring
  have hdrift : 5 / 4 + (Cgeo * A₀ / (1 - ρ / b)) * T < d := by
    have hh := mul_le_mul_of_nonneg_right hdiv hT.le
    dsimp only [d]
    nlinarith only [hh, hcat]
  have hh1 : 2 * ρ ^ 6 ≤ 1 := hhK.trans (hδgeomA.trans (by linarith only [cellA_lt_one]))
  have hcorei (i : Fin 2) : cellA / 2 ≤ 3 * circularContourRadii i / 4 := by
    have hi := (circularContourRadii_bounds i).2.1
    linarith only [hi, cellA_pos]
  dsimp only
  intro N k hkN S hS entrance he Ypast hcap
  try dsimp only [HasActualParentNextHandoffCaptureExtension] at hcap
  obtain ⟨Ncap, hNcap, hDlog, hterminal, hphysical, X, hX, heq,
    hgrid, henv, hcur, hback, hweighted, hparticles, hgraph, hfirst,
    u, hu, hLong, htime, angle, hMatched, hEarlier, hFull, hMoment, hControls, hParticlesFull, hvalue, hbefore⟩ := hcap
  let Dcap := (Ncap : ℝ) * circularCaptureBlockTime ℓ
  have hDcap : 0 ≤ Dcap := mul_nonneg (Nat.cast_nonneg Ncap) (circularCaptureBlockTime_pos hℓ).le
  have hAk : 0 < ampScale A₀ b k := by unfold ampScale; positivity
  have hEnd : 0 ≤ entrance + Dcap / ampScale A₀ b k := add_nonneg he (div_nonneg hDcap hAk.le)
  have hEndT : entrance + Dcap / ampScale A₀ b k ≤ T :=
    hphysical.le.trans (half_le_self hT.le)
  let α₀ := circularConstrainedUnstableProjectionCLM hγ hγ1.le
    (circularConstraintProjectionToTangentCLM hγ hγ1.le
      (canonicalPrefixAlignedCurrentCell A₀ b R ρ k entrance Ypast 0 - littleCircularReference hγ hγ1))
  have hcurRelative (u : ℝ) (hu : u ∈ Icc (0 : ℝ) Dcap) :
      ‖canonicalPrefixStageDeviation hγ hγ1 A₀ b R ρ k entrance X u k‖ ≤ targetFactor * δ :=
    (henv u hu).trans (parentCapture_envelope_bound_relative_section
      (norm_nonneg α₀) hHcap.le hterminal hu.2)
  have hcurGeom (u : ℝ) (hu : u ∈ Icc (0 : ℝ) Dcap) :
      ‖canonicalPrefixStageDeviation hγ hγ1 A₀ b R ρ k entrance X u k‖ ≤ δgeom :=
    le_min (hcur u hu) (hcurRelative u hu)

  let t := physicalTimeFromNormalized (ampScale A₀ b k) entrance u
  have hucc : u ∈ Icc (0 : ℝ) Dcap := ⟨hu.1.le, hu.2⟩
  have htpos : 0 < t := he.trans_lt htime.1
  have htT : t < T / 2 := htime.2.trans_lt hphysical
  have htend : t ∈ Icc (0 : ℝ) (entrance + Dcap / ampScale A₀ b k) := ⟨htpos.le, htime.2⟩
  obtain ⟨hfour, harea⟩ := hconstraints
    (s := s) (A₀ := A₀) (b := (b : ℝ)) (R := R) (ρ := ρ) (q := q) (T := T)
    (Hglob := T) (a := 1 / 16) (d := d)
    (Dphys := entrance + Dcap / ampScale A₀ b k)
    (core := cellA / 2) (δ := δgeom) (η := η) (C₀ := 2) (K := 1)
    hs hA.le hbR hR hRmax hρ hρone hρb hq hqE le_rfl hdrift hdR hEnd hδgeomA
    hcorei (by norm_num) hh1 (by norm_num) (by simpa only [mul_one] using hhK)
    hη.le hηa hancient hkN S hS X hX t htend entrance u rfl (hweighted u hucc) (hcurGeom u hucc)
  let y := canonicalPrefixAlignedCurrentCell A₀ b R ρ k entrance X
  let Z := circularCoRotationCLM γ u (y u)
  have hfourZ := circularCoRotationCLM_fourfold u (y u) hfour
  have hareaZ (i : Fin 2) : littleContourArea γ (Z i) = Real.pi * circularContourRadii i ^ 2 :=
    (circularCoRotationCLM_area u (y u) i).trans (harea i)
  have hZtarget : Z ∈ ball (littleCircularReference hγ hγ1) εtarget := by
    apply mem_ball_iff_norm.mpr
    change ‖circularCoRotationCLM γ u (y u) - littleCircularReference hγ hγ1‖ < εtarget
    rw [norm_circularCoRotationCLM_sub_reference hγ hγ1,
      norm_canonicalPrefixAlignedCurrentCell_sub_reference hγ hγ1]
    exact (hcurGeom u hucc).trans_lt hδgeomE
  have hResult := hContourξ Z hZtarget hfourZ hareaZ hvalue (hgraph u hucc)
  exact ⟨entrance, he, Ncap, hNcap, hDlog, hphysical, X, hX, u, hu, ⟨htpos, htT⟩,
    hfourZ, hareaZ, hResult.1, hResult.2, hcur u hucc, hweighted u hucc, hparticles u hucc⟩

end CircularMaterialTransferProfile
end Euler2D

end
