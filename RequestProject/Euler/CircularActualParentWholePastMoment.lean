module

public import RequestProject.Euler.CircularActualParentWholePastHistory
public import RequestProject.Euler.CircularBoundaryFourthMomentFixedBall
public import RequestProject.Euler.CircularCanonicalInstantaneousMoment

public import RequestProject.Euler.CircularCoupledWholePastSlowHistory
public import RequestProject.Euler.CircularActualParentMatchedLookbackCapture

public import RequestProject.Euler.CircularActualParentMatchedCapture
public import RequestProject.Euler.CircularCoupledForcedEarlierEntry

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

def HasActualParentWholePastMomentCaptureExtension
    (gseq : CircularConstrainedTangentSpace γ → ℕ → CircularConstrainedTangentSpace γ)
    {s A₀ b R ρ T : ℝ} (hR : 0 < R) (hρ : 0 < ρ)
    {N k : ℕ} (hkN : k ≤ N) {f : Lp ℝ 2 μT}
    (S : BoundedEulerParticleSystem f T) (entrance : ℝ)
    (Ypast : ℝ → FiniteCircularIndex k → LittleContourSpace γ)
    (ℓ : ℕ) (δ ηcur Hcap Cb D₀ Cgraph ξ sCanon Ctarget Lback Cback Cmoment : ℝ) : Prop :=
  let yPast := canonicalPrefixAlignedCurrentCell A₀ b R ρ k entrance Ypast
  let α₀ := circularConstrainedUnstableProjectionCLM hγ hγ1.le
    (circularConstraintProjectionToTangentCLM hγ hγ1.le (yPast 0 - littleCircularReference hγ hγ1))
  ∃ Ncap : ℕ, 0 < Ncap ∧
    let Dcap := (Ncap : ℝ) * circularCaptureBlockTime ℓ
    Dcap ≤ (6 / sigma) * ξ + D₀ ∧
    ‖α₀‖ * circularCaptureBlockMultiplier ℓ ^ Ncap < (4 * circularCaptureBlockMultiplier ℓ / 3) * δ ∧
    entrance + Dcap / ampScale A₀ b k < T / 2 ∧
    ∃ X : ℝ → FiniteCircularIndex k → LittleContourSpace γ,
      P.ActualCanonicalPrefixTrajectory s A₀ b R ρ (1 / 16) T hR hρ hkN S
        (entrance + Dcap / ampScale A₀ b k) X ∧
      EqOn X Ypast (Icc (0 : ℝ) entrance) ∧
      let x := canonicalPrefixStageDeviation hγ hγ1 A₀ b R ρ k entrance X
      let y := canonicalPrefixAlignedCurrentCell A₀ b R ρ k entrance X
      let v := fun n : ℕ => circularConstraintProjectionToTangentCLM hγ hγ1.le
        (y ((n : ℝ) * circularCaptureBlockTime ℓ) - littleCircularReference hγ hγ1)
      let α := fun n => circularConstrainedUnstableProjectionCLM hγ hγ1.le (v n)
      let w := fun n => v n - gseq (α n) 0
      (∀ n ≤ Ncap,
        (3 / 4 : ℝ) * ‖α₀‖ * circularCaptureBlockMultiplier ℓ ^ n ≤ ‖α n‖ ∧
        ‖α n‖ ≤ (5 / 4 : ℝ) * ‖α₀‖ * circularCaptureBlockMultiplier ℓ ^ n ∧
        ‖w n‖ ≤ (1 / 8 : ℝ) * ‖α₀‖ * circularCaptureBlockMultiplier ℓ ^ n) ∧
      (∀ u ∈ Icc (0 : ℝ) Dcap, ‖x u k‖ ≤ Hcap * ‖α₀‖ * Real.exp (sigma * u)) ∧
      (∀ u ∈ Icc (0 : ℝ) Dcap, ‖x u k‖ ≤ ηcur) ∧
      (∀ u ∈ Icc (0 : ℝ) Dcap, ‖x u k‖ ≤ ηcur * Real.exp (-sigma * (Dcap - u))) ∧
      (∀ u ∈ Icc (0 : ℝ) Dcap, weightedFamilyNorm (2 * ρ ^ 6) k (x u) ≤ 1) ∧
      (∀ u ∈ Icc (0 : ℝ) Dcap, ∀ z ∈ P.finiteInnerActiveInitialLabels s A₀ b R ρ N k,
        ‖S.forward (physicalTimeFromNormalized (ampScale A₀ b k) entrance u) z - torusCenter‖ ≤
          Cb * ρ * radScale R ρ k * (1 + u)) ∧
      (∀ u ∈ Icc (0 : ℝ) Dcap,
        let vc := circularConstraintProjectionToTangentCLM hγ hγ1.le
          (circularCoRotationCLM γ u (y u) - littleCircularReference hγ hγ1)
        ‖vc - gseq (circularConstrainedUnstableProjectionCLM hγ hγ1.le vc) 0‖ ≤ Cgraph * ρ ^ 3) ∧
      HasFirstCircularCoRotatedCaptureSection hγ hγ1 y Dcap δ ∧
      ∃ u ∈ Ioc (0 : ℝ) Dcap,
        Lback < u ∧
        physicalTimeFromNormalized (ampScale A₀ b k) entrance u ∈
          Ioc entrance (entrance + Dcap / ampScale A₀ b k) ∧
        ∃ angle : ℝ,
        ‖circularCoRotationCLM γ u (y u) - contourRotationFamilyLittleCLM γ angle
          (circularCoRotationCLM γ sCanon (P.ancient sCanon))‖ ≤ Ctarget * Cgraph * ρ ^ 3 ∧
        ‖circularCoRotationCLM γ (u - Lback) (y (u - Lback)) - contourRotationFamilyLittleCLM γ angle
          (circularCoRotationCLM γ (sCanon - Lback) (P.ancient (sCanon - Lback)))‖ ≤ Cback * ρ ^ 3 ∧
        (∀ τ ∈ Icc (0 : ℝ) (ampScale A₀ b k * entrance + u),
          ‖canonicalPrefixMaterialCurrentCell A₀ b R ρ k X τ - littleCircularReference hγ hγ1‖ ≤
            ηcur * Real.exp (-(sigma / 2) * ((ampScale A₀ b k * entrance + u) - τ))) ∧
        (∀ τ ∈ Icc (0 : ℝ) (ampScale A₀ b k * entrance + u),
          let t := physicalTimeFromNormalized (ampScale A₀ b k) 0 τ
          ‖momentN (boxedComplexDensity
            (S.transportedScalar (P.finitePeriodicLabel s A₀ b R ρ N k) t)) 4‖ ≤
            ampScale A₀ b k * radScale R ρ k ^ 6 * Cmoment * ηcur *
              Real.exp (-(sigma / 2) * ((ampScale A₀ b k * entrance + u) - τ))) ∧
        ‖circularConstrainedUnstableProjectionCLM hγ hγ1.le
          (circularConstraintProjectionToTangentCLM hγ hγ1.le
            (circularCoRotationCLM γ u (y u) - littleCircularReference hγ hγ1))‖ = δ ∧
        ∀ t ∈ Ico (0 : ℝ) u,
          ‖circularConstrainedUnstableProjectionCLM hγ hγ1.le
            (circularConstraintProjectionToTangentCLM hγ hγ1.le
              (circularCoRotationCLM γ t (y t) - littleCircularReference hγ hγ1))‖ < δ

theorem exists_eventually_actualParent_whole_past_boxed_moment
    (gseq : CircularConstrainedTangentSpace γ → ℕ → CircularConstrainedTangentSpace γ)
    {ηcur : ℝ} (hη : 0 ≤ ηcur) :
    ∃ Cmoment > 0,
      ∀ {s cA b q T : ℝ} [Fact (1 ≤ ENNReal.ofReal q)],
      ∀ (hs : s ≤ 0) (hcA : 0 < cA) (hb : 0 < b) (hq : 0 < q) (hqE : 2 ≤ ENNReal.ofReal q),
      0 ≤ T → ∀ᶠ ξ : ℝ in atTop,
      let ρ := Real.exp (-ξ)
      let hρ := Real.exp_pos (-ξ)
      let R := ρ ^ 10
      let hR := pow_pos hρ 10
      let A₀ := cA * (1 + ξ)
      ∀ N k : ℕ, ∀ hkN : k ≤ N,
      ∀ S : BoundedEulerParticleSystem
        (finiteBaseCurlL2 (A₀ := A₀) (b := b) (ρ := ρ) hR hρ hq hqE
          (P.finiteBaseLp (A₀ := A₀) (b := b) (ρ := ρ) (q := q) hs hR hρ) N) T,
      ∀ entrance : ℝ, 0 ≤ entrance →
      ∀ Ypast : ℝ → FiniteCircularIndex k → LittleContourSpace γ,
      ∀ ℓ : ℕ, ∀ δ Hcap Cb D₀ Cgraph sCanon Ctarget Lback Cback : ℝ,
      P.HasActualParentWholePastCaptureExtension gseq (s := s) (A₀ := A₀) (b := b)
        hR hρ hkN S entrance Ypast ℓ δ ηcur Hcap Cb D₀ Cgraph ξ sCanon Ctarget Lback Cback →
      P.HasActualParentWholePastMomentCaptureExtension gseq (s := s) (A₀ := A₀) (b := b)
        hR hρ hkN S entrance Ypast ℓ δ ηcur Hcap Cb D₀ Cgraph ξ sCanon Ctarget Lback Cback Cmoment := by
  obtain ⟨Cmoment, hCmoment, hboundary⟩ :=
    exists_circularBoundaryFourthMoment_prescribed_reference_bound hγ hγ1 hη
  obtain ⟨Cgeo, hCgeo, hidentity⟩ := P.exists_uniform_actualCanonical_instantaneous_boxed_moment
  refine ⟨Cmoment, hCmoment, ?_⟩
  intro s cA b q T _ hs hcA hb hq hqE hT
  let dcoef := 4 * Cgeo * cA * T
  let dsupport := fun ξ : ℝ => 2 + dcoef * (1 + ξ)
  have hρlim : Tendsto (fun ξ : ℝ => Real.exp (-ξ)) atTop (𝓝 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero
  have hhalf : ∀ᶠ ξ : ℝ in atTop, Real.exp (-ξ) ≤ b / 2 :=
    (hρlim.eventually (gt_mem_nhds (half_pos hb))).mono (fun _ h => h.le)
  have hmax : ∀ᶠ ξ : ℝ in atTop, Real.exp (-ξ) ≤ 1 / 2 :=
    (hρlim.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))).mono (fun _ h => h.le)
  have hdlim : Tendsto (fun ξ : ℝ => dsupport ξ * Real.exp (-ξ) ^ 10) atTop (𝓝 0) := by
    convert tendsto_circularCapture_log_monomial 1 dcoef (1 + dcoef) 10 1 (by decide) using 1
    ext ξ
    dsimp only [dsupport]
    ring
  have hdsmall := (hdlim.eventually (gt_mem_nhds
    (by norm_num : (0 : ℝ) < 1 / 4))).mono (fun _ h => h.le)
  filter_upwards [hhalf, hmax, hdsmall, eventually_ge_atTop (0 : ℝ)]
    with ξ hρhalf hρmax hdR hξ
  let ρ := Real.exp (-ξ)
  have hρ : 0 < ρ := Real.exp_pos (-ξ)
  let R := ρ ^ 10
  have hR : 0 < R := pow_pos hρ 10
  let A₀ := cA * (1 + ξ)
  have hA : 0 < A₀ := mul_pos hcA (by linarith only [hξ])
  have hρone : ρ ≤ 1 := hρmax.trans (by norm_num)
  have hRρ : R ≤ ρ := by
    simpa only [R, pow_one] using pow_le_pow_of_le_one hρ.le hρone (by decide : (1 : ℕ) ≤ 10)
  have hRhalf : R ≤ 1 / 2 := hRρ.trans hρmax
  have hρb : ρ < b := hρhalf.trans_lt (half_lt_self hb)
  have hdenHalf : (1 / 2 : ℝ) ≤ 1 - ρ / b := by
    have hh : ρ / b ≤ 1 / 2 := (div_le_iff₀ hb).mpr (by nlinarith only [hρhalf])
    linarith only [hh]
  let d := 2 + 4 * Cgeo * A₀ * T
  have hdeq : dsupport ξ = d := by dsimp only [dsupport, dcoef, d, A₀]; ring
  rw [hdeq] at hdR
  have hcat : 0 ≤ Cgeo * A₀ * T := mul_nonneg (mul_nonneg hCgeo.le hA.le) hT
  have hdiv : Cgeo * A₀ / (1 - ρ / b) ≤ 2 * Cgeo * A₀ := by
    calc
      _ ≤ Cgeo * A₀ / (1 / 2) :=
        div_le_div_of_nonneg_left (mul_nonneg hCgeo.le hA.le) (by norm_num) hdenHalf
      _ = _ := by ring
  have hdrift : 5 / 4 + (Cgeo * A₀ / (1 - ρ / b)) * T < d := by
    have hh := mul_le_mul_of_nonneg_right hdiv hT
    dsimp only [d]
    nlinarith only [hh, hcat]
  dsimp only
  intro N k hkN S entrance he Ypast ℓ δ Hcap Cb D₀ Cgraph sCanon Ctarget Lback Cback hcap
  obtain ⟨Ncap, hNcap, hDlog, hterminal, hphysical, X, hX, heq,
    hgrid, henv, hcur, hback, hweighted, hparticles, hgraph, hfirst,
    u, hu, hLong, htime, angle, hmatched, hEarlier, hFull, hvalue, hbefore⟩ := hcap
  let Dcap := (Ncap : ℝ) * circularCaptureBlockTime ℓ
  have hDcap : 0 ≤ Dcap := hu.1.le.trans hu.2
  have hAk : 0 < ampScale A₀ b k := div_pos hA (pow_pos hb k)
  have hrad : 0 < radScale R ρ k := radScale_pos hR hρ k
  have hDphys : 0 ≤ entrance + Dcap / ampScale A₀ b k := add_nonneg he (div_nonneg hDcap hAk.le)
  have hMoment : ∀ τ ∈ Icc (0 : ℝ) (ampScale A₀ b k * entrance + u),
      let t := physicalTimeFromNormalized (ampScale A₀ b k) 0 τ
      ‖momentN (boxedComplexDensity
        (S.transportedScalar (P.finitePeriodicLabel s A₀ b R ρ N k) t)) 4‖ ≤
        ampScale A₀ b k * radScale R ρ k ^ 6 * Cmoment * ηcur *
          Real.exp (-(sigma / 2) * ((ampScale A₀ b k * entrance + u) - τ)) := by
    intro τ hτ
    let t := physicalTimeFromNormalized (ampScale A₀ b k) 0 τ
    have hτcap : τ ≤ ampScale A₀ b k * entrance + Dcap :=
      hτ.2.trans (add_le_add le_rfl hu.2)
    have ht : t ∈ Icc (0 : ℝ) (entrance + Dcap / ampScale A₀ b k) := by
      change 0 ≤ 0 + τ / ampScale A₀ b k ∧
        0 + τ / ampScale A₀ b k ≤ entrance + Dcap / ampScale A₀ b k
      simp only [zero_add]
      refine ⟨div_nonneg hτ.1 hAk.le, (div_le_iff₀ hAk).mpr ?_⟩
      rw [add_mul, div_mul_cancel₀ Dcap hAk.ne']
      nlinarith only [hτcap]
    have hid := hidentity (s := s) (A₀ := A₀) (b := b) (R := R) (ρ := ρ) (q := q)
      (T := T) (Hglob := T) (c := d)
      hs hA hb hR hRhalf hρ hρone hρb hq hqE le_rfl hdrift hdR N S hkN hDphys X hX t ht 0 τ rfl
    let y := canonicalPrefixAlignedCurrentCell A₀ b R ρ k 0 X
    have hnormEq : ‖y τ - littleCircularMaterialContours hγ hγ1 τ‖ =
        ‖canonicalPrefixMaterialCurrentCell A₀ b R ρ k X τ - littleCircularReference hγ hγ1‖ := by
      dsimp only [y]
      rw [canonicalPrefixAlignedCurrentCell_zero_entrance, norm_canonicalPrefixMaterialCurrent_sub_reference]
    have hexp : Real.exp (-(sigma / 2) * ((ampScale A₀ b k * entrance + u) - τ)) ≤ 1 := by
      apply Real.exp_le_one_iff.mpr
      exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (half_pos sigma_pos).le) (sub_nonneg.mpr hτ.2)
    have hnear : ‖y τ - littleCircularMaterialContours hγ hγ1 τ‖ ≤ ηcur := by
      rw [hnormEq]
      exact (hFull τ hτ).trans (mul_le_of_le_one_right hη hexp)
    have hbnd := hboundary τ (y τ) hnear
    have hMbound : ‖circularBoundaryFourthMoment (y τ)‖ ≤
        Cmoment * ηcur * Real.exp (-(sigma / 2) * ((ampScale A₀ b k * entrance + u) - τ)) := by
      calc
        _ ≤ Cmoment * ‖y τ - littleCircularMaterialContours hγ hγ1 τ‖ := hbnd
        _ ≤ Cmoment * (ηcur * Real.exp (-(sigma / 2) * ((ampScale A₀ b k * entrance + u) - τ))) :=
          mul_le_mul_of_nonneg_left (by rw [hnormEq]; exact hFull τ hτ) hCmoment.le
        _ = _ := by ring
    have hphase : ‖Complex.exp (-(4 * (((t * finiteAncestorAngularVelocity A₀ b k : ℝ) : ℂ)) * I))‖ = 1 := by
      rw [show -(4 * (((t * finiteAncestorAngularVelocity A₀ b k : ℝ) : ℂ)) * I) =
        ((-(4 * (t * finiteAncestorAngularVelocity A₀ b k)) : ℝ) : ℂ) * I by push_cast; ring,
        Complex.norm_exp_ofReal_mul_I]
    have hnorm : ‖momentN (boxedComplexDensity
        (S.transportedScalar (P.finitePeriodicLabel s A₀ b R ρ N k) t)) 4‖ =
        ampScale A₀ b k * radScale R ρ k ^ 6 * ‖circularBoundaryFourthMoment (y τ)‖ := by
      rw [hid, norm_mul, norm_mul, norm_mul, norm_pow, hphase]
      simp only [y, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hAk, abs_of_pos hrad, mul_one]
    change ‖momentN (boxedComplexDensity
      (S.transportedScalar (P.finitePeriodicLabel s A₀ b R ρ N k) t)) 4‖ ≤ _
    rw [hnorm]
    calc
      _ ≤ ampScale A₀ b k * radScale R ρ k ^ 6 *
          (Cmoment * ηcur * Real.exp (-(sigma / 2) * ((ampScale A₀ b k * entrance + u) - τ))) :=
        mul_le_mul_of_nonneg_left hMbound (by positivity)
      _ = _ := by ring
  exact ⟨Ncap, hNcap, hDlog, hterminal, hphysical, X, hX, heq,
    hgrid, henv, hcur, hback, hweighted, hparticles, hgraph, hfirst,
    u, hu, hLong, htime, angle, hmatched, hEarlier, hFull, hMoment, hvalue, hbefore⟩

end CircularMaterialTransferProfile
end Euler2D

end
