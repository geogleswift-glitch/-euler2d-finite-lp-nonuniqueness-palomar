module

public import RequestProject.Euler.NormalizedFiniteLabelTransport
public import RequestProject.Euler.ActualTorusCancellation

/-! Exact rotating coordinates for the same finite Euler particles and
the same integrable planar label. Both endpoint frames are retained;
the time-dependent frame has its actual angular-velocity derivative. -/

@[expose] public section

set_option maxHeartbeats 6000000
set_option maxRecDepth 5500

noncomputable section

open Complex Set Filter Topology MeasureTheory
open scoped NNReal ENNReal

namespace Euler2D

def planarRigidRotation (θ : ℝ) : R2 ≃ₗᵢ[ℝ] R2 :=
  complexPhysicalPlane.symm.trans ((rotation (Circle.exp θ)).trans complexPhysicalPlane)

theorem planarRigidRotation_apply (θ : ℝ) (a : R2) :
    planarRigidRotation θ a =
      complexPhysicalPlane (Complex.exp ((θ : ℂ) * I) * complexPhysicalPlane.symm a) := by
  simp only [planarRigidRotation, LinearIsometryEquiv.trans_apply, rotation_apply, Circle.coe_exp]

@[simp] theorem planarRigidRotation_neg_cancel (θ : ℝ) (a : R2) :
    planarRigidRotation θ (planarRigidRotation (-θ) a) = a := by
  rw [planarRigidRotation_apply, planarRigidRotation_apply,
    LinearIsometryEquiv.symm_apply_apply, ← mul_assoc, ← Complex.exp_add]
  have he : (θ : ℂ) * I + ((-θ : ℝ) : ℂ) * I = 0 := by push_cast; ring
  rw [he, Complex.exp_zero, one_mul, LinearIsometryEquiv.apply_symm_apply]

@[simp] theorem planarRigidRotation_symm_apply (θ : ℝ) (a : R2) :
    (planarRigidRotation θ).symm a = planarRigidRotation (-θ) a := by
  apply (planarRigidRotation θ).injective
  rw [LinearIsometryEquiv.apply_symm_apply, planarRigidRotation_neg_cancel]

theorem hasDerivAt_planarRigidRotatedCurve {z : ℝ → R2} {v : R2} {θ₀ ω t : ℝ}
    (hz : HasDerivAt z v t) :
    HasDerivAt (fun u => planarRigidRotation (-(θ₀ + ω * u)) (z u))
      (planarRigidRotation (-(θ₀ + ω * t)) v -
        ω • perpJ (planarRigidRotation (-(θ₀ + ω * t)) (z t))) t := by
  let g : ℝ → ℂ := fun u => Complex.exp (((-(θ₀ + ω * u) : ℝ) : ℂ) * I)
  have hg : HasDerivAt g (g t * ((-ω : ℂ) * I)) t := by
    have hh := (((((hasDerivAt_id t).const_mul ω).const_add θ₀).neg).ofReal_comp.mul_const I).cexp
    simpa only [g, id_eq, one_mul, mul_one, Pi.neg_apply, Complex.ofReal_neg] using hh
  have hzC := complexPhysicalPlane.symm.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt t hz
  have hh := complexPhysicalPlane.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt t (hg.mul hzC)
  change HasDerivAt (fun u => complexPhysicalPlane (g u * complexPhysicalPlane.symm (z u)))
    (complexPhysicalPlane ((g t * ((-ω : ℂ) * I)) * complexPhysicalPlane.symm (z t) +
      g t * complexPhysicalPlane.symm v)) t at hh
  have hfirst : complexPhysicalPlane
      ((g t * ((-ω : ℂ) * I)) * complexPhysicalPlane.symm (z t)) =
      (-ω) • perpJ (complexPhysicalPlane (g t * complexPhysicalPlane.symm (z t))) := by
    calc
      _ = complexPhysicalPlane ((-ω : ℝ) • (I * (g t * complexPhysicalPlane.symm (z t)))) := by
        congr 1
        rw [Complex.real_smul]
        push_cast
        ring
      _ = _ := by rw [map_smul, complexPhysicalPlane_mul_I]
  have hfun : (fun u => planarRigidRotation (-(θ₀ + ω * u)) (z u)) =
      fun u => complexPhysicalPlane (g u * complexPhysicalPlane.symm (z u)) := by
    funext u
    exact planarRigidRotation_apply _ _
  rw [hfun]
  have hderiv : complexPhysicalPlane
      ((g t * ((-ω : ℂ) * I)) * complexPhysicalPlane.symm (z t) + g t * complexPhysicalPlane.symm v) =
      planarRigidRotation (-(θ₀ + ω * t)) v -
        ω • perpJ (planarRigidRotation (-(θ₀ + ω * t)) (z t)) := by
    rw [map_add, hfirst, planarRigidRotation_apply, planarRigidRotation_apply]
    change (-ω) • perpJ (complexPhysicalPlane (g t * complexPhysicalPlane.symm (z t))) +
      complexPhysicalPlane (g t * complexPhysicalPlane.symm v) =
      complexPhysicalPlane (g t * complexPhysicalPlane.symm v) -
        ω • perpJ (complexPhysicalPlane (g t * complexPhysicalPlane.symm (z t)))
    rw [neg_smul]
    abel
  rw [hderiv] at hh
  exact hh

namespace BoundedEulerParticleSystem

variable {f : Lp ℝ 2 μT} {T : ℝ} (S : BoundedEulerParticleSystem f T)

def rotatingNormalizedRelativeHomeomorph (r : ℝ) (hr : r ≠ 0)
    (entrance : ℝ) (he : entrance ∈ Icc (0 : ℝ) T)
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) (θentry θtarget : ℝ) : R2 ≃ₜ R2 :=
  (planarRigidRotation θentry).toHomeomorph.trans
    ((S.normalizedRelativeHomeomorph r hr entrance he t ht).trans
      (planarRigidRotation θtarget).symm.toHomeomorph)

theorem rotatingNormalizedRelativeHomeomorph_apply (r : ℝ) (hr : r ≠ 0)
    (entrance : ℝ) (he : entrance ∈ Icc (0 : ℝ) T)
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) (θentry θtarget : ℝ) (a : R2) :
    S.rotatingNormalizedRelativeHomeomorph r hr entrance he t ht θentry θtarget a =
      planarRigidRotation (-θtarget)
        (S.normalizedRelativeHomeomorph r hr entrance he t ht (planarRigidRotation θentry a)) := by
  exact planarRigidRotation_symm_apply _ _

theorem rotatingNormalizedRelativeHomeomorph_symm_apply (r : ℝ) (hr : r ≠ 0)
    (entrance : ℝ) (he : entrance ∈ Icc (0 : ℝ) T)
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) (θentry θtarget : ℝ) (a : R2) :
    (S.rotatingNormalizedRelativeHomeomorph r hr entrance he t ht θentry θtarget).symm a =
      (planarRigidRotation θentry).symm
        ((S.normalizedRelativeHomeomorph r hr entrance he t ht).symm (planarRigidRotation θtarget a)) := rfl

theorem rotatingNormalizedRelativeHomeomorph_entrance (r : ℝ) (hr : r ≠ 0)
    (entrance : ℝ) (he : entrance ∈ Icc (0 : ℝ) T) (θ : ℝ) (a : R2) :
    S.rotatingNormalizedRelativeHomeomorph r hr entrance he entrance he θ θ a = a := by
  rw [S.rotatingNormalizedRelativeHomeomorph_apply, S.normalizedRelativeHomeomorph_entrance]
  simpa only [neg_neg] using planarRigidRotation_neg_cancel (-θ) a

theorem measurePreserving_rotatingNormalizedRelativeHomeomorph {r entrance t : ℝ}
    (hr : 0 < r) (he : entrance ∈ Icc (0 : ℝ) T) (ht : t ∈ Icc (0 : ℝ) T)
    (hentry : MeasurePreserving (S.backward entrance) volume volume)
    (htarget : MeasurePreserving (S.forward t) volume volume) (θentry θtarget : ℝ) :
    MeasurePreserving (S.rotatingNormalizedRelativeHomeomorph r hr.ne' entrance he t ht
      θentry θtarget) volume volume :=
  (planarRigidRotation θtarget).symm.measurePreserving.comp
    ((S.measurePreserving_normalizedRelativeHomeomorph hr he ht hentry htarget).comp
      (planarRigidRotation θentry).measurePreserving)

def rotatingNormalizedPlanarLabelSource (q₀ : R2 → ℝ) (A r θ t : ℝ) (z : R2) : ℝ :=
  S.normalizedPlanarLabelSource q₀ A r t (planarRigidRotation θ z)

theorem rotatingNormalizedPlanarLabelSource_transport (q₀ : R2 → ℝ) (A r : ℝ) (hr : r ≠ 0)
    (entrance : ℝ) (he : entrance ∈ Icc (0 : ℝ) T)
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) (θentry θtarget : ℝ) (z : R2) :
    S.rotatingNormalizedPlanarLabelSource q₀ A r θtarget t z =
      S.rotatingNormalizedPlanarLabelSource q₀ A r θentry entrance
        ((S.rotatingNormalizedRelativeHomeomorph r hr entrance he t ht θentry θtarget).symm z) := by
  rw [rotatingNormalizedPlanarLabelSource, rotatingNormalizedPlanarLabelSource,
    S.rotatingNormalizedRelativeHomeomorph_symm_apply, LinearIsometryEquiv.apply_symm_apply]
  exact S.normalizedPlanarLabelSource_transport q₀ A r hr entrance he t ht _

theorem integrable_rotatingNormalizedPlanarLabelSource (q₀ : R2 → ℝ) (A r θ t : ℝ)
    (hq : Integrable (S.normalizedPlanarLabelSource q₀ A r t)) :
    Integrable (S.rotatingNormalizedPlanarLabelSource q₀ A r θ t) :=
  (planarRigidRotation θ).measurePreserving.integrable_comp_of_integrable hq

theorem integral_norm_rotatingNormalizedPlanarLabelSource (q₀ : R2 → ℝ) (A r θ t : ℝ) :
    (∫ z, ‖S.rotatingNormalizedPlanarLabelSource q₀ A r θ t z‖) =
      ∫ z, ‖S.normalizedPlanarLabelSource q₀ A r t z‖ :=
  (planarRigidRotation θ).measurePreserving.integral_comp
    (planarRigidRotation θ).toHomeomorph.measurableEmbedding
    (fun z => ‖S.normalizedPlanarLabelSource q₀ A r t z‖)

theorem integral_norm_rotatingNormalizedPlanarLabelSource_eq_entrance
    (q₀ : R2 → ℝ) (A : ℝ) {r entrance t : ℝ}
    (hr : 0 < r) (he : entrance ∈ Icc (0 : ℝ) T) (ht : t ∈ Icc (0 : ℝ) T)
    (hentry : MeasurePreserving (S.backward entrance) volume volume)
    (htarget : MeasurePreserving (S.forward t) volume volume) (θentry θtarget : ℝ) :
    (∫ z, ‖S.rotatingNormalizedPlanarLabelSource q₀ A r θtarget t z‖) =
      ∫ z, ‖S.rotatingNormalizedPlanarLabelSource q₀ A r θentry entrance z‖ := by
  rw [S.integral_norm_rotatingNormalizedPlanarLabelSource,
    S.integral_norm_rotatingNormalizedPlanarLabelSource]
  exact S.integral_norm_normalizedPlanarLabelSource q₀ A hr he ht hentry htarget

def rotatingNormalizedRelativeParticleCurve (A r entrance Ω θentry : ℝ) (a : R2) (τ : ℝ) : R2 :=
  planarRigidRotation (-(θentry + (Ω / A) * τ))
    (S.normalizedRelativeParticleCurve A r entrance (planarRigidRotation θentry a) τ)

theorem rotatingNormalizedRelativeParticleCurve_eq_homeomorph
    (A r entrance Ω θentry : ℝ) (hr : r ≠ 0)
    (he : entrance ∈ Icc (0 : ℝ) T) (a : R2) {τ : ℝ}
    (ht : physicalTimeFromNormalized A entrance τ ∈ Icc (0 : ℝ) T) :
    S.rotatingNormalizedRelativeParticleCurve A r entrance Ω θentry a τ =
      S.rotatingNormalizedRelativeHomeomorph r hr entrance he
        (physicalTimeFromNormalized A entrance τ) ht θentry (θentry + (Ω / A) * τ) a := by
  rw [S.rotatingNormalizedRelativeHomeomorph_apply]
  rfl

theorem rotatingNormalizedRelativeParticleCurve_hasDerivAt
    (A r entrance Ω θentry : ℝ) (a : R2) {τ : ℝ}
    (ht : physicalTimeFromNormalized A entrance τ ∈ Icc (0 : ℝ) T) :
    HasDerivAt (S.rotatingNormalizedRelativeParticleCurve A r entrance Ω θentry a)
      (planarRigidRotation (-(θentry + (Ω / A) * τ))
        ((A * r)⁻¹ • particleVelocityRepresentative f S.backward S.backward_area
          (physicalTimeFromNormalized A entrance τ)
          (S.forward (physicalTimeFromNormalized A entrance τ)
            (S.backward entrance (r • planarRigidRotation θentry a + torusCenter)))) -
        (Ω / A) • perpJ (S.rotatingNormalizedRelativeParticleCurve A r entrance Ω θentry a τ)) τ :=
  hasDerivAt_planarRigidRotatedCurve
    (S.normalizedRelativeParticleCurve_hasDerivAt A r entrance (planarRigidRotation θentry a) ht)

def rotatingNormalizedParticleVelocity (A r entrance Ω θentry τ : ℝ) (z : R2) : R2 :=
  planarRigidRotation (-(θentry + (Ω / A) * τ))
    ((A * r)⁻¹ • particleVelocityRepresentative f S.backward S.backward_area
      (physicalTimeFromNormalized A entrance τ)
      (r • planarRigidRotation (θentry + (Ω / A) * τ) z + torusCenter)) -
    (Ω / A) • perpJ z

theorem rotatingNormalizedRelativeParticleCurve_hasDerivAt_velocity
    (A r entrance Ω θentry : ℝ) (hr : r ≠ 0) (a : R2) {τ : ℝ}
    (ht : physicalTimeFromNormalized A entrance τ ∈ Icc (0 : ℝ) T) :
    HasDerivAt (S.rotatingNormalizedRelativeParticleCurve A r entrance Ω θentry a)
      (S.rotatingNormalizedParticleVelocity A r entrance Ω θentry τ
        (S.rotatingNormalizedRelativeParticleCurve A r entrance Ω θentry a τ)) τ := by
  have hpoint : r • planarRigidRotation (θentry + (Ω / A) * τ)
      (S.rotatingNormalizedRelativeParticleCurve A r entrance Ω θentry a τ) + torusCenter =
      S.forward (physicalTimeFromNormalized A entrance τ)
        (S.backward entrance (r • planarRigidRotation θentry a + torusCenter)) := by
    rw [rotatingNormalizedRelativeParticleCurve, planarRigidRotation_neg_cancel]
    dsimp only [normalizedRelativeParticleCurve, normalizedPhysicalCurve]
    rw [smul_smul, mul_inv_cancel₀ hr, one_smul, sub_add_cancel]
  simpa only [rotatingNormalizedParticleVelocity, hpoint] using
    S.rotatingNormalizedRelativeParticleCurve_hasDerivAt A r entrance Ω θentry a ht

theorem continuous_rotatingNormalizedRelativeParticleCurve (A r entrance Ω θentry : ℝ) :
    Continuous (fun p : ℝ × R2 =>
      S.rotatingNormalizedRelativeParticleCurve A r entrance Ω θentry p.2 p.1) := by
  have hfwd := S.forward_continuous
  have hbwd := S.backward_continuous
  simp only [rotatingNormalizedRelativeParticleCurve, normalizedRelativeParticleCurve,
    normalizedPhysicalCurve, physicalTimeFromNormalized, planarRigidRotation_apply]
  fun_prop

theorem norm_rotatingNormalizedRelativeParticleCurve
    (A entrance Ω θentry : ℝ) {r : ℝ} (hr : 0 < r) (a : R2) (τ : ℝ) :
    ‖S.rotatingNormalizedRelativeParticleCurve A r entrance Ω θentry a τ‖ =
      ‖S.forward (physicalTimeFromNormalized A entrance τ)
        (S.backward entrance (r • planarRigidRotation θentry a + torusCenter)) - torusCenter‖ / r := by
  rw [rotatingNormalizedRelativeParticleCurve, LinearIsometryEquiv.norm_map]
  exact norm_normalizedPhysicalCurve hr _

end BoundedEulerParticleSystem
end Euler2D

end
