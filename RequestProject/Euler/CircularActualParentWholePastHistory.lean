module

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

theorem canonicalPrefixMaterialCurrentCell_congr_at_normalized_time {γ : ℝ≥0}
    (A₀ b R ρ : ℝ) (k : ℕ) (τ : ℝ)
    {X Y : ℝ → FiniteCircularIndex k → LittleContourSpace γ}
    (hXY : X (physicalTimeFromNormalized (ampScale A₀ b k) 0 τ) =
      Y (physicalTimeFromNormalized (ampScale A₀ b k) 0 τ)) :
    canonicalPrefixMaterialCurrentCell A₀ b R ρ k X τ =
      canonicalPrefixMaterialCurrentCell A₀ b R ρ k Y τ := by
  unfold canonicalPrefixMaterialCurrentCell canonicalPrefixAbsoluteCell normalizedPhysicalCurve
  simp only [hXY]

theorem canonicalPrefixMaterialCurrentCell_past_warmup_bound {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1)
    {A₀ b R ρ entrance Dpre Kcur : ℝ}
    (hA : 0 < A₀) (hb : 0 < b) (hρ : 0 ≤ ρ)
    (he : 0 ≤ entrance) (hD : 0 ≤ Dpre) (hKcur : 0 ≤ Kcur)
    (k : ℕ) (Y : ℝ → FiniteCircularIndex k → LittleContourSpace γ)
    (hpast : ∀ t ∈ Icc (0 : ℝ) entrance,
      ‖canonicalPrefixStageDeviation hγ hγ1 A₀ b R ρ k 0 Y
        (ampScale A₀ b k * t) k‖ ≤ 2 * ρ ^ 6)
    (hwarm : ∀ u ∈ Icc (0 : ℝ) Dpre,
      ‖canonicalPrefixStageDeviation hγ hγ1 A₀ b R ρ k entrance Y u k‖ ≤ Kcur * (2 * ρ ^ 6)) :
    ∀ τ ∈ Icc (0 : ℝ) (ampScale A₀ b k * (entrance + Dpre / ampScale A₀ b k)),
      ‖canonicalPrefixMaterialCurrentCell A₀ b R ρ k Y τ - littleCircularReference hγ hγ1‖ ≤
        (2 * max (1 : ℝ) Kcur) * ρ ^ 6 := by
  have hAk : 0 < ampScale A₀ b k := div_pos hA (pow_pos hb k)
  have hh : 0 ≤ 2 * ρ ^ 6 := mul_nonneg (by norm_num) (pow_nonneg hρ 6)
  have hcoefOne : 2 * ρ ^ 6 ≤ (2 * max (1 : ℝ) Kcur) * ρ ^ 6 := by
    have hx := mul_le_mul_of_nonneg_right (le_max_left (1 : ℝ) Kcur) hh
    nlinarith only [hx]
  have hcoefCur : Kcur * (2 * ρ ^ 6) ≤ (2 * max (1 : ℝ) Kcur) * ρ ^ 6 := by
    have hx := mul_le_mul_of_nonneg_right (le_max_right (1 : ℝ) Kcur) hh
    nlinarith only [hx]
  intro τ hτ
  by_cases hbefore : τ ≤ ampScale A₀ b k * entrance
  · have ht : τ / ampScale A₀ b k ∈ Icc (0 : ℝ) entrance :=
      ⟨div_nonneg hτ.1 hAk.le, (div_le_iff₀ hAk).mpr (by simpa only [mul_comm] using hbefore)⟩
    have hx := hpast (τ / ampScale A₀ b k) ht
    rw [mul_div_cancel₀ τ hAk.ne'] at hx
    rw [norm_canonicalPrefixMaterialCurrent_sub_reference,
      ← canonicalPrefixAlignedCurrentCell_zero_entrance,
      norm_canonicalPrefixAlignedCurrentCell_sub_reference]
    exact hx.trans hcoefOne
  · let u := τ - ampScale A₀ b k * entrance
    have hu0 : 0 ≤ u := by dsimp only [u]; linarith only [hbefore]
    have hτend := hτ.2
    rw [mul_add, mul_div_cancel₀ Dpre hAk.ne'] at hτend
    have huD : u ≤ Dpre := by dsimp only [u]; linarith only [hτend]
    have hclock : ampScale A₀ b k * entrance + u = τ := by dsimp only [u]; ring
    rw [← hclock,
      canonicalPrefixMaterialCurrentCell_eq_coRotatedAligned hA.ne' hb.ne' R ρ k entrance u Y,
      norm_circularCoRotationCLM_sub_reference hγ hγ1,
      norm_canonicalPrefixAlignedCurrentCell_sub_reference hγ hγ1]
    exact (hwarm u ⟨hu0, huD⟩).trans hcoefCur

theorem eventually_canonicalPrefixMaterialCurrent_whole_past_slow_history {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1)
    {rate Lclock Dclock K η : ℝ}
    (hrate : 0 ≤ rate) (hfast : rate ≤ sigma)
    (hK : 0 ≤ K) (hη : 0 < η) (hgap : rate * Lclock < 6) :
    ∀ᶠ ξ : ℝ in atTop,
      let ρ := Real.exp (-ξ)
      ∀ {A₀ b R : ℝ}, 0 < A₀ → 0 < b →
      ∀ k : ℕ, ∀ X Ypast : ℝ → FiniteCircularIndex k → LittleContourSpace γ,
      ∀ entrance Dcap hit : ℝ,
      0 ≤ entrance → hit ∈ Icc (0 : ℝ) Dcap →
      ampScale A₀ b k * entrance + hit ≤ Lclock * ξ + Dclock →
      EqOn X Ypast (Icc (0 : ℝ) entrance) →
      (∀ τ ∈ Icc (0 : ℝ) (ampScale A₀ b k * entrance),
        ‖canonicalPrefixMaterialCurrentCell A₀ b R ρ k Ypast τ - littleCircularReference hγ hγ1‖ ≤
          K * ρ ^ 6) →
      (∀ u ∈ Icc (0 : ℝ) Dcap,
        ‖canonicalPrefixStageDeviation hγ hγ1 A₀ b R ρ k entrance X u k‖ ≤
          η * Real.exp (-sigma * (Dcap - u))) →
      ∀ τ ∈ Icc (0 : ℝ) (ampScale A₀ b k * entrance + hit),
        ‖canonicalPrefixMaterialCurrentCell A₀ b R ρ k X τ - littleCircularReference hγ hγ1‖ ≤
          η * Real.exp (-rate * ((ampScale A₀ b k * entrance + hit) - τ)) := by
  filter_upwards [eventually_circularCapture_whole_past_slow_decay hrate hfast hK hη hgap]
    with ξ hslow
  dsimp only
  intro A₀ b R hA hb k X Ypast entrance Dcap hit he hhit hclock heq hpast hcapture
  let ρ := Real.exp (-ξ)
  have hAk : 0 < ampScale A₀ b k := div_pos hA (pow_pos hb k)
  let v := fun τ : ℝ => ‖canonicalPrefixMaterialCurrentCell A₀ b R ρ k X τ - littleCircularReference hγ hγ1‖
  apply hslow (ampScale A₀ b k * entrance) Dcap hit v (mul_nonneg hAk.le he) hhit hclock
  · intro τ hτ
    have ht : physicalTimeFromNormalized (ampScale A₀ b k) 0 τ ∈ Icc (0 : ℝ) entrance := by
      change 0 ≤ 0 + τ / ampScale A₀ b k ∧ 0 + τ / ampScale A₀ b k ≤ entrance
      simp only [zero_add]
      exact ⟨div_nonneg hτ.1 hAk.le, (div_le_iff₀ hAk).mpr (by simpa only [mul_comm] using hτ.2)⟩
    dsimp only [v]
    rw [canonicalPrefixMaterialCurrentCell_congr_at_normalized_time A₀ b R ρ k τ (heq ht)]
    exact hpast τ hτ
  · intro u hu
    dsimp only [v]
    rw [canonicalPrefixMaterialCurrentCell_eq_coRotatedAligned hA.ne' hb.ne' R ρ k entrance u X,
      norm_circularCoRotationCLM_sub_reference hγ hγ1,
      norm_canonicalPrefixAlignedCurrentCell_sub_reference hγ hγ1]
    exact hcapture u hu


namespace CircularMaterialTransferProfile

variable {γ : ℝ≥0} {hγ : 0 < γ} {hγ1 : (γ : ℝ) < 1}
    (P : CircularMaterialTransferProfile hγ hγ1)

def HasActualParentWholePastCaptureExtension
    (gseq : CircularConstrainedTangentSpace γ → ℕ → CircularConstrainedTangentSpace γ)
    {s A₀ b R ρ T : ℝ} (hR : 0 < R) (hρ : 0 < ρ)
    {N k : ℕ} (hkN : k ≤ N) {f : Lp ℝ 2 μT}
    (S : BoundedEulerParticleSystem f T) (entrance : ℝ)
    (Ypast : ℝ → FiniteCircularIndex k → LittleContourSpace γ)
    (ℓ : ℕ) (δ ηcur Hcap Cb D₀ Cgraph ξ sCanon Ctarget Lback Cback : ℝ) : Prop :=
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
        ‖circularConstrainedUnstableProjectionCLM hγ hγ1.le
          (circularConstraintProjectionToTangentCLM hγ hγ1.le
            (circularCoRotationCLM γ u (y u) - littleCircularReference hγ hγ1))‖ = δ ∧
        ∀ t ∈ Ico (0 : ℝ) u,
          ‖circularConstrainedUnstableProjectionCLM hγ hγ1.le
            (circularConstraintProjectionToTangentCLM hγ hγ1.le
              (circularCoRotationCLM γ t (y t) - littleCircularReference hγ hγ1))‖ < δ

theorem eventually_actualParentCapture_whole_past_history
    {δ ηcur Hcap Cb D₀ Cgraph sCanon Ctarget Lback Cback Kpast Lentry Dentry : ℝ} {ℓ : ℕ}
    (hη : 0 < ηcur) (hKpast : 0 ≤ Kpast) (hℓ : 0 < ℓ)
    (hClockMargin : sigma * (Lentry + 6 / sigma) < 8)
    (gseq : CircularConstrainedTangentSpace γ → ℕ → CircularConstrainedTangentSpace γ) :
    ∀ᶠ ξ : ℝ in atTop,
      let ρ := Real.exp (-ξ)
      let hρ := Real.exp_pos (-ξ)
      ∀ {s A₀ b R T : ℝ}, ∀ (hA : 0 < A₀) (hb : 0 < b) (hR : 0 < R),
      ∀ N k : ℕ, ∀ hkN : k ≤ N, ∀ {f : Lp ℝ 2 μT},
      ∀ S : BoundedEulerParticleSystem f T,
      ∀ entrance : ℝ, 0 ≤ entrance →
      ∀ Ypast : ℝ → FiniteCircularIndex k → LittleContourSpace γ,
      ampScale A₀ b k * entrance ≤ Lentry * ξ + Dentry →
      (∀ τ ∈ Icc (0 : ℝ) (ampScale A₀ b k * entrance),
        ‖canonicalPrefixMaterialCurrentCell A₀ b R ρ k Ypast τ - littleCircularReference hγ hγ1‖ ≤
          Kpast * ρ ^ 6) →
      P.HasActualParentMatchedLookbackCaptureExtension gseq (s := s) (A₀ := A₀) (b := b)
        hR hρ hkN S entrance Ypast ℓ δ ηcur Hcap Cb D₀ Cgraph ξ sCanon Ctarget Lback Cback →
      P.HasActualParentWholePastCaptureExtension gseq (s := s) (A₀ := A₀) (b := b)
        hR hρ hkN S entrance Ypast ℓ δ ηcur Hcap Cb D₀ Cgraph ξ sCanon Ctarget Lback Cback := by
  have hrate : 0 ≤ sigma / 2 := (half_pos sigma_pos).le
  have hfast : sigma / 2 ≤ sigma := half_le_self sigma_pos.le
  have hgap : (sigma / 2) * (Lentry + 6 / sigma) < 6 := by nlinarith only [hClockMargin]
  have hslow := eventually_canonicalPrefixMaterialCurrent_whole_past_slow_history hγ hγ1
    (rate := sigma / 2) (Lclock := Lentry + 6 / sigma) (Dclock := Dentry + D₀)
    hrate hfast hKpast hη hgap
  filter_upwards [hslow] with ξ hslowξ
  dsimp only
  intro s A₀ b R T hA hb hR N k hkN f S entrance he Ypast hEntryClock hpast hcap
  obtain ⟨Ncap, hNcap, hDlog, hterminal, hphysical, X, hX, heq,
    hgrid, henv, hcur, hback, hweighted, hparticles, hgraph, hfirst,
    u, hu, hLong, htime, angle, hmatched, hEarlier, hvalue, hbefore⟩ := hcap
  let Dcap := (Ncap : ℝ) * circularCaptureBlockTime ℓ
  have hTotalClock : ampScale A₀ b k * entrance + u ≤
      (Lentry + 6 / sigma) * ξ + (Dentry + D₀) := by
    have hucap : u ≤ Dcap := hu.2
    change Dcap ≤ (6 / sigma) * ξ + D₀ at hDlog
    nlinarith only [hEntryClock, hDlog, hucap]
  have hFull := hslowξ hA hb k X Ypast entrance Dcap u he ⟨hu.1.le, hu.2⟩
    hTotalClock heq hpast hback
  exact ⟨Ncap, hNcap, hDlog, hterminal, hphysical, X, hX, heq,
    hgrid, henv, hcur, hback, hweighted, hparticles, hgraph, hfirst,
    u, hu, hLong, htime, angle, hmatched, hEarlier, hFull, hvalue, hbefore⟩

end CircularMaterialTransferProfile
end Euler2D

end
