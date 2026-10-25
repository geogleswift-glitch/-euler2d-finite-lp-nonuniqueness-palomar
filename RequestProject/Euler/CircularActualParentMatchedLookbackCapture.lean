module

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

def HasActualParentMatchedLookbackCaptureExtension
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
        ‖circularConstrainedUnstableProjectionCLM hγ hγ1.le
          (circularConstraintProjectionToTangentCLM hγ hγ1.le
            (circularCoRotationCLM γ u (y u) - littleCircularReference hγ hγ1))‖ = δ ∧
        ∀ t ∈ Ico (0 : ℝ) u,
          ‖circularConstrainedUnstableProjectionCLM hγ hγ1.le
            (circularConstraintProjectionToTangentCLM hγ hγ1.le
              (circularCoRotationCLM γ t (y t) - littleCircularReference hγ hγ1))‖ < δ

theorem exists_eventually_actualCoupled_parentMatchedCapture_with_lookback
    {sCanon δ η Hcap Ctarget Cgraph Lback : ℝ} {ℓ : ℕ}
    (hsCanon : sCanon ≤ 0) (hδ : 0 < δ) (hη : 0 < η) (hηa : η ≤ cellA / 4)
    (hHcap : 0 ≤ Hcap) (hCtarget : 0 ≤ Ctarget) (hCgraph : 0 ≤ Cgraph)
    (hLback : 0 < Lback) (hℓ : 0 < ℓ)
    (gseq : CircularConstrainedTangentSpace γ → ℕ → CircularConstrainedTangentSpace γ) :
    ∃ Cback > 0,
      ∀ b : ℝ≥0, 0 < b → b ≤ 1 →
      ∀ Cb D₀ Cseed : ℝ, 0 ≤ Cb → 0 ≤ Cseed →
      ∀ {s cA q T : ℝ} [Fact (1 ≤ ENNReal.ofReal q)],
      ∀ (hs : s ≤ 0) (hcA : 0 < cA) (hq : 0 < q) (hqE : 2 ≤ ENNReal.ofReal q),
      0 ≤ T → (∀ i, ‖(P.ancient s i).val - circularReferenceC1 hγ hγ1 i‖ ≤ η) →
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
      ‖circularConstrainedUnstableProjectionCLM hγ hγ1.le
        (circularConstraintProjectionToTangentCLM hγ hγ1.le
          (canonicalPrefixAlignedCurrentCell A₀ b R ρ k entrance Ypast 0 -
            littleCircularReference hγ hγ1))‖ ≤ Cseed * ρ ^ 6 →
      P.HasActualParentMatchedCaptureExtension gseq (s := s) (A₀ := A₀) (b := (b : ℝ))
        hR hρ hkN S entrance Ypast ℓ δ η Hcap Cb D₀ Cgraph ξ sCanon Ctarget →
      P.HasActualParentMatchedLookbackCaptureExtension gseq (s := s) (A₀ := A₀) (b := (b : ℝ))
        hR hρ hkN S entrance Ypast ℓ δ η Hcap Cb D₀ Cgraph ξ sCanon Ctarget Lback Cback := by
  obtain ⟨Cback, hCback, hlook⟩ := P.exists_eventually_actualCoupledForced_earlier_section_match
    hsCanon hη hηa (mul_nonneg hCtarget hCgraph) hLback
  refine ⟨Cback, hCback, ?_⟩
  intro b hb hb1 Cb D₀ Cseed hCb hCseed s cA q T _ hs hcA hq hqE hT hancient
  let J := circularConstraintProjectionToTangentCLM hγ hγ1.le
  let Q := circularConstrainedUnstableProjectionCLM hγ hγ1.le
  let M := ‖Q‖ * ‖J‖
  have hM : 0 ≤ M := mul_nonneg (norm_nonneg _) (norm_nonneg _)
  let Kseed := M * Hcap * Cseed * Real.exp (sigma * Lback)
  have hseedLimit : Tendsto (fun ξ : ℝ => Kseed * Real.exp (-ξ) ^ 6) atTop (𝓝 0) := by
    simpa only [zero_pow (by decide : (6 : ℕ) ≠ 0), mul_zero] using
      (Real.tendsto_exp_neg_atTop_nhds_zero.pow 6).const_mul Kseed
  have hseedSmall : ∀ᶠ ξ : ℝ in atTop, Kseed * Real.exp (-ξ) ^ 6 < δ :=
    hseedLimit.eventually (gt_mem_nhds hδ)
  have hlookEv := hlook (b : ℝ) Cb (6 / sigma) D₀ hb (show (b : ℝ) ≤ 1 from hb1)
    hCb hs hcA hq hqE hT hancient
  filter_upwards [hlookEv, hseedSmall] with ξ hlookξ hseedξ
  dsimp only
  intro N k hkN S hS entrance he Ypast hseed hcap
  let ρ := Real.exp (-ξ)
  let R := ρ ^ 10
  let A₀ := cA * (1 + ξ)
  obtain ⟨Ncap, hNcap, hDlog, hterminal, hphysical, X, hX, heq,
    hgrid, henv, hcur, hback, hweighted, hparticles, hgraph, hfirst,
    u, hu, htime, angle, hmatched, hvalue, hbefore⟩ := hcap
  let Dcap := (Ncap : ℝ) * circularCaptureBlockTime ℓ
  have hDcap : 0 ≤ Dcap := mul_nonneg (Nat.cast_nonneg Ncap) (circularCaptureBlockTime_pos hℓ).le
  have huu : u ∈ Icc (0 : ℝ) Dcap := ⟨hu.1.le, hu.2⟩
  let α₀ := Q (J (canonicalPrefixAlignedCurrentCell A₀ b R ρ k entrance Ypast 0 -
    littleCircularReference hγ hγ1))
  have hcoord : δ ≤ M * ‖canonicalPrefixStageDeviation hγ hγ1 A₀ b R ρ k entrance X u k‖ := by
    calc
      _ = ‖Q (J (circularCoRotationCLM γ u
          (canonicalPrefixAlignedCurrentCell A₀ b R ρ k entrance X u) - littleCircularReference hγ hγ1))‖ := hvalue.symm
      _ ≤ ‖Q‖ * ‖J (circularCoRotationCLM γ u
          (canonicalPrefixAlignedCurrentCell A₀ b R ρ k entrance X u) - littleCircularReference hγ hγ1)‖ := Q.le_opNorm _
      _ ≤ ‖Q‖ * (‖J‖ * ‖circularCoRotationCLM γ u
          (canonicalPrefixAlignedCurrentCell A₀ b R ρ k entrance X u) - littleCircularReference hγ hγ1‖) :=
        mul_le_mul_of_nonneg_left (J.le_opNorm _) (norm_nonneg _)
      _ = _ := by
        rw [norm_circularCoRotationCLM_sub_reference hγ hγ1,
          norm_canonicalPrefixAlignedCurrentCell_sub_reference hγ hγ1]
        dsimp only [M]
        ring
  have hLong : Lback < u := by
    by_contra hn
    have huL : u ≤ Lback := le_of_not_gt hn
    have he : Real.exp (sigma * u) ≤ Real.exp (sigma * Lback) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left huL sigma_pos.le)
    have hα : ‖α₀‖ ≤ Cseed * ρ ^ 6 := hseed
    have henvSeed : Hcap * ‖α₀‖ * Real.exp (sigma * u) ≤
        Hcap * (Cseed * ρ ^ 6) * Real.exp (sigma * Lback) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hα hHcap) he (Real.exp_pos _).le
        (mul_nonneg hHcap (mul_nonneg hCseed (pow_nonneg (Real.exp_pos _).le 6)))
    have hδseed : δ ≤ Kseed * ρ ^ 6 := by
      calc
        _ ≤ M * (Hcap * ‖α₀‖ * Real.exp (sigma * u)) :=
          hcoord.trans (mul_le_mul_of_nonneg_left (henv u huu) hM)
        _ ≤ M * (Hcap * (Cseed * ρ ^ 6) * Real.exp (sigma * Lback)) :=
          mul_le_mul_of_nonneg_left henvSeed hM
        _ = _ := by dsimp only [Kseed]; ring
    exact (not_lt_of_ge hδseed) hseedξ
  have hEarlier := hlookξ N k hkN S hS entrance Dcap he hDcap hDlog X hX
    hweighted hcur hparticles u angle ⟨hLong.le, hu.2⟩ hmatched
  exact ⟨Ncap, hNcap, hDlog, hterminal, hphysical, X, hX, heq,
    hgrid, henv, hcur, hback, hweighted, hparticles, hgraph, hfirst,
    u, hu, hLong, htime, angle, hmatched, hEarlier, hvalue, hbefore⟩

end CircularMaterialTransferProfile
end Euler2D

end
