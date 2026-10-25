module

public import RequestProject.Euler.CircularCanonicalInstantaneousMoment

/-! The backward capture estimate now bounds the literal original
boxed physical child moment, not a replacement boundary profile.
All factors and the SAME canonical particle trajectory are retained. -/

@[expose] public section

set_option maxHeartbeats 22000000
set_option maxRecDepth 7500

noncomputable section

open Complex Set Filter Topology MeasureTheory Metric
open scoped NNReal ENNReal

namespace Euler2D

attribute [local instance 2000] rigidGaugeLittle_group rigidGaugeLittle_space rigidGaugeFamily_tower
attribute [local instance 2000] captureBlockTangent_group captureBlockTangent_space
  captureBlockTangent_continuousAdd captureBlockEndo_monoid captureBlockTangent_complete
attribute [local instance] LittleContourSpace.complexScalarNormedSpace LittleContourSpace.complexScalarTower
attribute [local irreducible] circularConstrainedTangentSubmodule
  circularConstrainedUnstableProjectionCLM circularConstraintProjectionToTangentCLM

namespace CircularMaterialTransferProfile

variable {γ : ℝ≥0} {hγ : 0 < γ} {hγ1 : (γ : ℝ) < 1}
    (P : CircularMaterialTransferProfile hγ hγ1)

theorem exists_uniform_actualCanonical_capture_moment_history :
    ∃ Cgeo > 0, ∃ Cm > 0, ∃ rm > 0,
      ∀ {s A₀ b R ρ q T Hglob c : ℝ},
      ∀ [Fact (1 ≤ ENNReal.ofReal q)] (hs : s ≤ 0) (hA : 0 < A₀) (hb : 0 < b)
        (hR : 0 < R) (hRmax : R ≤ 1 / 2) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
        (hρb : ρ < b) (hq : 0 < q) (hqE : 2 ≤ ENNReal.ofReal q),
      Hglob ≤ T → 5 / 4 + (Cgeo * A₀ / (1 - ρ / b)) * Hglob < c → c * R ≤ 1 / 4 →
      ∀ N : ℕ,
      ∀ S : BoundedEulerParticleSystem
        (finiteBaseCurlL2 (A₀ := A₀) (b := b) hR hρ hq hqE
          (P.finiteBaseLp (A₀ := A₀) (b := b) (q := q) hs hR hρ) N) T,
      ∀ {k : ℕ} (hkN : k ≤ N) {a Htraj : ℝ}, 0 ≤ Htraj →
      ∀ X : ℝ → FiniteCircularIndex k → LittleContourSpace γ,
      P.ActualCanonicalPrefixTrajectory s A₀ b R ρ a Hglob hR hρ hkN S Htraj X →
      ∀ entrance Dcap Henv seed r : ℝ, ∀ (kb Nb : ℕ), 0 < kb →
      let y := canonicalPrefixAlignedCurrentCell A₀ b R ρ k entrance X;
      0 ≤ Dcap → 0 ≤ Henv → 0 ≤ seed → r ≤ rm →
      Dcap ≤ (Nb : ℝ) * circularCaptureBlockTime kb →
      (∀ u ∈ Icc (0 : ℝ) Dcap,
        physicalTimeFromNormalized (ampScale A₀ b k) entrance u ∈ Icc (0 : ℝ) Htraj) →
      (∀ u ∈ Icc (0 : ℝ) Dcap,
        ‖y u - littleCircularMaterialContours hγ hγ1 u‖ ≤ Henv * seed * Real.exp (sigma * u)) →
      (∀ u ∈ Icc (0 : ℝ) Dcap, ‖y u - littleCircularMaterialContours hγ hγ1 u‖ ≤ r) →
      (∀ n ≤ Nb, (n : ℝ) * circularCaptureBlockTime kb ≤ Dcap →
        (3 / 4 : ℝ) * seed * circularCaptureBlockMultiplier kb ^ n ≤
          ‖circularConstrainedUnstableProjectionCLM hγ hγ1.le
            (circularConstraintProjectionToTangentCLM hγ hγ1.le
              (y ((n : ℝ) * circularCaptureBlockTime kb) - littleCircularReference hγ hγ1))‖) →
      ∀ u ∈ Icc (0 : ℝ) Dcap,
        let t := physicalTimeFromNormalized (ampScale A₀ b k) entrance u;
        ‖momentN (boxedComplexDensity (S.transportedScalar (P.finitePeriodicLabel s A₀ b R ρ N k) t)) 4‖ ≤
          ampScale A₀ b k * radScale R ρ k ^ 6 *
            (Cm * (Henv * (4 / 3) * circularCaptureBlockMultiplier kb *
              (‖circularConstrainedUnstableProjectionCLM hγ hγ1.le‖ *
                ‖circularConstraintProjectionToTangentCLM hγ hγ1.le‖))) * r *
                  Real.exp (-sigma * (Dcap - u)) := by
  obtain ⟨Cgeo, hCgeo, hidentity⟩ := P.exists_uniform_actualCanonical_instantaneous_boxed_moment
  obtain ⟨Cm, hCm, rm, hrm, hmoment⟩ :=
    exists_circularBoundaryFourthMoment_moving_reference_bound hγ hγ1
  refine ⟨Cgeo, hCgeo, Cm, hCm, rm, hrm, ?_⟩
  intro s A₀ b R ρ q T Hglob c _ hs hA hb hR hRmax hρ hρ1 hρb hq hqE hglobT hdrift hcR
    N S k hkN a Htraj hHtraj X hX entrance Dcap Henv seed r kb Nb hkb y
    hDcap hHenv hseed hr hNb hwindow hforward hnear hlower u hu
  let t := physicalTimeFromNormalized (ampScale A₀ b k) entrance u
  have hid := hidentity hs hA hb hR hRmax hρ hρ1 hρb hq hqE hglobT hdrift hcR
    N S hkN hHtraj X hX t (hwindow u hu) entrance u rfl
  have hback := circularCapture_backward_envelope_of_stopped_bounds hγ hγ1 hkb
    hDcap hHenv hseed hNb y hforward hnear hlower u hu
  have hm := hmoment u (y u) ((hnear u hu).trans hr)
  have hAmp : 0 < ampScale A₀ b k := div_pos hA (pow_pos hb k)
  have hrad : 0 < radScale R ρ k := radScale_pos hR hρ k
  have hphase : ‖Complex.exp (-(4 * (((t * finiteAncestorAngularVelocity A₀ b k : ℝ) : ℂ)) * I))‖ = 1 := by
    rw [show -(4 * (((t * finiteAncestorAngularVelocity A₀ b k : ℝ) : ℂ)) * I) =
      ((-(4 * (t * finiteAncestorAngularVelocity A₀ b k)) : ℝ) : ℂ) * I by push_cast; ring,
      Complex.norm_exp_ofReal_mul_I]
  have hnorm : ‖momentN (boxedComplexDensity
      (S.transportedScalar (P.finitePeriodicLabel s A₀ b R ρ N k) t)) 4‖ =
      ampScale A₀ b k * radScale R ρ k ^ 6 * ‖circularBoundaryFourthMoment (y u)‖ := by
    rw [hid, norm_mul, norm_mul, norm_mul, norm_pow, hphase]
    simp only [y, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hAmp, abs_of_pos hrad, mul_one]
  change ‖momentN (boxedComplexDensity
    (S.transportedScalar (P.finitePeriodicLabel s A₀ b R ρ N k) t)) 4‖ ≤ _
  rw [hnorm]
  calc
    _ ≤ ampScale A₀ b k * radScale R ρ k ^ 6 * (Cm * ‖y u - littleCircularMaterialContours hγ hγ1 u‖) :=
      mul_le_mul_of_nonneg_left hm (by positivity)
    _ ≤ ampScale A₀ b k * radScale R ρ k ^ 6 * (Cm *
        ((Henv * (4 / 3) * circularCaptureBlockMultiplier kb *
          (‖circularConstrainedUnstableProjectionCLM hγ hγ1.le‖ *
            ‖circularConstraintProjectionToTangentCLM hγ hγ1.le‖)) * r *
              Real.exp (-sigma * (Dcap - u)))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hback hCm.le) (by positivity)
    _ = _ := by ring

end CircularMaterialTransferProfile
end Euler2D

end
