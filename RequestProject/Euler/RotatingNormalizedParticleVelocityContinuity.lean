module

public import RequestProject.Euler.CircularActualObservationParticleBound
public import RequestProject.Euler.BoundedLagrangianEuler

/-! The actual rotating velocity along the same original particles is
continuous. The same fixed canonical positive flow has exactly its
original material self velocity, as required by singular stability. -/

@[expose] public section

set_option maxHeartbeats 3000000
set_option maxRecDepth 6000

noncomputable section

open Complex Set Filter Topology MeasureTheory
open scoped NNReal ENNReal

namespace Euler2D

theorem continuous_planarRigidRotation :
    Continuous (fun p : ℝ × R2 => planarRigidRotation p.1 p.2) := by
  simp only [planarRigidRotation_apply]
  have hI : Continuous (fun p : ℝ × R2 => (p.1 : ℂ) * I) :=
    (Complex.continuous_ofReal.comp continuous_fst).mul continuous_const
  exact complexPhysicalPlane.continuous.comp
    ((Complex.continuous_exp.comp hI).mul
      (complexPhysicalPlane.symm.continuous.comp continuous_snd))

namespace BoundedEulerParticleSystem

variable {f : Lp ℝ 2 μT} {T : ℝ} (S : BoundedEulerParticleSystem f T)

attribute [local irreducible] particleVelocityRepresentative rotatingNormalizedRelativeParticleCurve
  rotatingNormalizedRelativeHomeomorph planarRigidRotation planarMaterialLabelVelocity

theorem continuous_rotatingNormalizedVelocityAt
    (A r Ω : ℝ) {M : ℝ} (hM0 : 0 ≤ M) (hM : ∀ᵐ x ∂μT, ‖f x‖ ≤ M) :
    Continuous (fun p : ℝ × ℝ × R2 => S.rotatingNormalizedVelocityAt A r Ω p.1 p.2.1 p.2.2) := by
  have hv := continuous_particleVelocityRepresentative f hM0 hM S.backward_area S.backward_continuous
  have hangle : Continuous (fun p : ℝ × ℝ × R2 => p.2.1) := continuous_fst.comp continuous_snd
  have hz : Continuous (fun p : ℝ × ℝ × R2 => p.2.2) := continuous_snd.comp continuous_snd
  have hrot := continuous_planarRigidRotation.comp (hangle.prodMk hz)
  have hquery : Continuous (fun p : ℝ × ℝ × R2 =>
      (p.1, r • planarRigidRotation p.2.1 p.2.2 + torusCenter)) :=
    continuous_fst.prodMk ((hrot.const_smul r).add continuous_const)
  have hvel := hv.comp hquery
  have houter := continuous_planarRigidRotation.comp
    (hangle.neg.prodMk (hvel.const_smul ((A * r)⁻¹)))
  have hJc : Continuous (fun p : ℝ × ℝ × R2 => I * complexPhysicalPlane.symm p.2.2) :=
    continuous_const.mul (complexPhysicalPlane.symm.continuous.comp hz)
  have hJ : Continuous (fun p : ℝ × ℝ × R2 => perpJ p.2.2) := by
    simpa only [Function.comp_def, complexPhysicalPlane_mul_I, LinearIsometryEquiv.apply_symm_apply] using
      complexPhysicalPlane.continuous.comp hJc
  simpa only [rotatingNormalizedVelocityAt] using houter.sub (hJ.const_smul (Ω / A))

theorem continuous_rotatingNormalized_curve_velocity
    (A r entrance Ω θentry : ℝ) {M : ℝ} (hM0 : 0 ≤ M) (hM : ∀ᵐ x ∂μT, ‖f x‖ ≤ M) (a : R2) :
    Continuous (fun τ => S.rotatingNormalizedParticleVelocity A r entrance Ω θentry τ
      (S.rotatingNormalizedRelativeParticleCurve A r entrance Ω θentry a τ)) := by
  have htime : Continuous (physicalTimeFromNormalized A entrance) := by
    unfold physicalTimeFromNormalized
    exact continuous_const.add (continuous_id.div_const A)
  have hangle : Continuous (fun τ : ℝ => θentry + (Ω / A) * τ) :=
    continuous_const.add (continuous_const.mul continuous_id)
  have hcurve : Continuous (S.rotatingNormalizedRelativeParticleCurve A r entrance Ω θentry a) :=
    (S.continuous_rotatingNormalizedRelativeParticleCurve A r entrance Ω θentry).comp
      (continuous_id.prodMk continuous_const)
  have hh := (S.continuous_rotatingNormalizedVelocityAt A r Ω hM0 hM).comp
    (htime.prodMk (hangle.prodMk hcurve))
  simpa only [rotatingNormalizedParticleVelocity_eq_velocityAt] using hh

end BoundedEulerParticleSystem

namespace CircularMaterialTransferProfile

variable {γ : ℝ≥0} {hγ : 0 < γ} {hγ1 : (γ : ℝ) < 1}
    (P : CircularMaterialTransferProfile hγ hγ1)

theorem positive_velocity_eq_material {t : ℝ} (ht : 0 ≤ t) (x : R2) :
    P.positive.velocity t x = planarMaterialLabelVelocity kernelK
      (circularPhasePatchPlanarVorticity (P.ancient 0)) (P.positive.homeomorph t ht) x := by
  rw [planarMaterialBiotSavart_eq_spatial _ _ (P.positive.forward_area t ht)]
  exact P.positive.selfconsistent t x

end CircularMaterialTransferProfile
end Euler2D

end
