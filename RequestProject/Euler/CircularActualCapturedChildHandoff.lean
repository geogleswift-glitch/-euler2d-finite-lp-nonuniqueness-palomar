module

public import RequestProject.Euler.CircularActualHandoffPastControls

/-! A literal strengthening of the SAME captured child's actual
whole-past moment extension, at its SAME first hit and SAME angle.
It supplies all past contour/particle controls for the next handoff. -/

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

def HasActualParentNextHandoffCaptureExtension
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
        (∀ τ ∈ Icc (0 : ℝ) (ampScale A₀ b k * entrance + u - Lback),
          weightedFamilyNorm (2 * ρ ^ 6) k
            (canonicalPrefixStageDeviation hγ hγ1 A₀ b R ρ k 0 X τ) ≤ 1 ∧
          ‖canonicalPrefixStageDeviation hγ hγ1 A₀ b R ρ k 0 X τ k‖ ≤ ηcur) ∧
        (∀ t ∈ Icc (0 : ℝ) ((ampScale A₀ b k * entrance + u - Lback) / ampScale A₀ b k),
          ∀ z ∈ P.finiteInnerActiveInitialLabels s A₀ b R ρ N k,
          ‖S.forward t z - torusCenter‖ ≤ 2 * radScale R ρ k) ∧
        ‖circularConstrainedUnstableProjectionCLM hγ hγ1.le
          (circularConstraintProjectionToTangentCLM hγ hγ1.le
            (circularCoRotationCLM γ u (y u) - littleCircularReference hγ hγ1))‖ = δ ∧
        ∀ t ∈ Ico (0 : ℝ) u,
          ‖circularConstrainedUnstableProjectionCLM hγ hγ1.le
            (circularConstraintProjectionToTangentCLM hγ hγ1.le
              (circularCoRotationCLM γ t (y t) - littleCircularReference hγ hγ1))‖ < δ

theorem eventually_actualParentCapture_next_handoff_controls
    (gseq : CircularConstrainedTangentSpace γ → ℕ → CircularConstrainedTangentSpace γ)
    {s cA b q T ηcur Cb D₀ : ℝ} [Fact (1 ≤ ENNReal.ofReal q)]
    (hs : s ≤ 0) (hcA : 0 < cA) (hb : 0 < b) (hq : 0 < q) (hqE : 2 ≤ ENNReal.ofReal q)
    (hη : 0 ≤ ηcur) (hCb : 0 ≤ Cb) :
    ∀ᶠ ξ : ℝ in atTop,
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
      (∀ t ∈ Icc (0 : ℝ) entrance,
        weightedFamilyNorm (2 * ρ ^ 6) k
          (canonicalPrefixStageDeviation hγ hγ1 A₀ b R ρ k 0 Ypast (ampScale A₀ b k * t)) ≤ 1) →
      (∀ t ∈ Icc (0 : ℝ) entrance, ∀ z ∈ P.finiteInnerActiveInitialLabels s A₀ b R ρ N k,
        ‖S.forward t z - torusCenter‖ ≤ 2 * radScale R ρ k) →
      ∀ ℓ : ℕ, ∀ δ Hcap Cgraph sCanon Ctarget Lback Cback Cmoment : ℝ,
      0 < Lback →
      P.HasActualParentWholePastMomentCaptureExtension gseq (s := s) (A₀ := A₀) (b := b)
        hR hρ hkN S entrance Ypast ℓ δ ηcur Hcap Cb D₀ Cgraph ξ sCanon Ctarget Lback Cback Cmoment →
      P.HasActualParentNextHandoffCaptureExtension gseq (s := s) (A₀ := A₀) (b := b)
        hR hρ hkN S entrance Ypast ℓ δ ηcur Hcap Cb D₀ Cgraph ξ sCanon Ctarget Lback Cback Cmoment := by
  have hsmall := eventually_circularCapture_log_monomial_small
    (K := Cb) (L := 6 / sigma) (D₀ := D₀) (ε := 2)
    hCb (by norm_num : (0 : ℝ) < 2) 1 1 (by decide)
  filter_upwards [hsmall, eventually_ge_atTop (0 : ℝ)] with ξ hsmallξ hξ
  let ρ := Real.exp (-ξ)
  let R := ρ ^ 10
  let A₀ := cA * (1 + ξ)
  have hρ : 0 < ρ := Real.exp_pos (-ξ)
  have hR : 0 < R := pow_pos hρ 10
  have hA : 0 < A₀ := mul_pos hcA (by linarith only [hξ])
  dsimp only
  intro N k hkN S entrance he Ypast hpastWeighted hpastParticles ℓ δ Hcap Cgraph sCanon Ctarget Lback Cback Cmoment hLback hcap
  dsimp only [HasActualParentWholePastMomentCaptureExtension, HasActualParentNextHandoffCaptureExtension] at hcap ⊢
  obtain ⟨Ncap, hNcap, hDlog, hterminal, hphysical, X, hX, heq,
    hgrid, henv, hcur, hback, hweighted, hparticles, hgraph, hfirst,
    u, hu, hLong, htime, angle, hmatched, hEarlier, hFull, hMoment, hvalue, hbefore⟩ := hcap
  let Dcap := (Ncap : ℝ) * circularCaptureBlockTime ℓ
  have hDcap : 0 ≤ Dcap := hu.1.le.trans hu.2
  have hAmp : 0 < ampScale A₀ b k := div_pos hA (pow_pos hb k)
  have hshift : 0 ≤ u - Lback := sub_nonneg.mpr hLong.le
  have hshiftD : u - Lback ≤ Dcap := (sub_le_self u hLback.le).trans hu.2
  have hcaptureSmall : Cb * ρ * (1 + Dcap) ≤ 2 := by
    simpa only [pow_one] using hsmallξ Dcap hDcap hDlog
  have hweightedFull := canonicalPrefix_whole_past_weighted_splice hγ hγ1
    (A₀ := A₀) (b := b) (R := R) (ρ := ρ) (h := 2 * ρ ^ 6)
    (D := Dcap) (shift := u - Lback) hA hb he hshift hshiftD k X Ypast heq hpastWeighted hweighted
  have hendpoint : ampScale A₀ b k * entrance + (u - Lback) =
      ampScale A₀ b k * entrance + u - Lback := by ring
  rw [hendpoint] at hweightedFull
  have hcontrols : ∀ τ ∈ Icc (0 : ℝ) (ampScale A₀ b k * entrance + u - Lback),
      weightedFamilyNorm (2 * ρ ^ 6) k
        (canonicalPrefixStageDeviation hγ hγ1 A₀ b R ρ k 0 X τ) ≤ 1 ∧
      ‖canonicalPrefixStageDeviation hγ hγ1 A₀ b R ρ k 0 X τ k‖ ≤ ηcur := by
    intro τ hτ
    refine ⟨hweightedFull τ hτ, ?_⟩
    exact canonicalPrefix_current_le_of_full_material_history hγ hγ1 A₀ b R ρ k X
      (half_pos sigma_pos).le hη
      ⟨hτ.1, hτ.2.trans (sub_le_self _ hLback.le)⟩ hFull
  have hparticlesFull :
      ∀ t ∈ Icc (0 : ℝ) ((ampScale A₀ b k * entrance + u - Lback) / ampScale A₀ b k),
      ∀ z ∈ P.finiteInnerActiveInitialLabels s A₀ b R ρ N k,
      ‖S.forward t z - torusCenter‖ ≤ 2 * radScale R ρ k := by
    have hclock : (ampScale A₀ b k * entrance + u - Lback) / ampScale A₀ b k =
        entrance + (u - Lback) / ampScale A₀ b k := by
      field_simp [hAmp.ne'] <;> ring
    rw [hclock]
    exact P.actual_inner_particle_handoff_radius_splice hA hb hR hρ hCb hshift hshiftD
      hcaptureSmall N k S hpastParticles hparticles
  exact ⟨Ncap, hNcap, hDlog, hterminal, hphysical, X, hX, heq,
    hgrid, henv, hcur, hback, hweighted, hparticles, hgraph, hfirst,
    u, hu, hLong, htime, angle, hmatched, hEarlier, hFull, hMoment, hcontrols, hparticlesFull, hvalue, hbefore⟩

end CircularMaterialTransferProfile
end Euler2D

end
