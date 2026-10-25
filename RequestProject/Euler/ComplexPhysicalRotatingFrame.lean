module

public import RequestProject.Euler.BanachPhysicalTimeSpaceRescaling
public import RequestProject.Euler.ComplexBanachRotatingFrame

/-! A physical trajectory is normalized at its actual entrance time
and its constant ancestor rigid velocity is removed. Both derivatives
and forcing norms retain the exact amplitude and length factors. -/

@[expose] public section

set_option maxHeartbeats 2000000

noncomputable section

open Complex

namespace Euler2D

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E]
  [IsScalarTower ℝ ℂ E]

theorem hasDerivAt_normalizedPhysicalRigidCurve
    {A r e τ Ω : ℝ} (hA : A ≠ 0) (hr : r ≠ 0)
    {z p : ℝ → E} {F : E → E}
    (hd : HasDerivAt z
      ((A * r) • F (r⁻¹ • z (physicalTimeFromNormalized A e τ)) +
        ((Ω : ℂ) * I) • z (physicalTimeFromNormalized A e τ) +
        p (physicalTimeFromNormalized A e τ)) (physicalTimeFromNormalized A e τ)) :
    HasDerivAt (normalizedPhysicalCurve A r e z)
      (F (normalizedPhysicalCurve A r e z τ) +
        (((Ω / A : ℝ) : ℂ) * I) • normalizedPhysicalCurve A r e z τ +
        (A * r)⁻¹ • p (physicalTimeFromNormalized A e τ)) τ := by
  have hnorm := hasDerivAt_normalizedPhysicalCurve (r := r) hd
  have hcoef : (((A * r)⁻¹ : ℝ) : ℂ) * ((Ω : ℂ) * I) =
      (((Ω / A : ℝ) : ℂ) * I) * (((r⁻¹ : ℝ) : ℂ)) := by
    push_cast
    field_simp
  convert hnorm using 1
  simp only [normalizedPhysicalCurve, smul_add, smul_smul,
    inv_mul_cancel₀ (mul_ne_zero hA hr), one_smul]
  congr 1
  simp only [RCLike.real_smul_eq_coe_smul (K := ℂ), smul_smul]
  congr 2
  exact hcoef.symm

theorem hasDerivAt_normalizedPhysicalRotatedCurve
    {A r e τ Ω : ℝ} (hA : A ≠ 0) (hr : r ≠ 0)
    {z p : ℝ → E} {F : E → E}
    (hd : HasDerivAt z
      ((A * r) • F (r⁻¹ • z (physicalTimeFromNormalized A e τ)) +
        ((Ω : ℂ) * I) • z (physicalTimeFromNormalized A e τ) +
        p (physicalTimeFromNormalized A e τ)) (physicalTimeFromNormalized A e τ))
    (hcov : F (rigidRotationGauge (Ω / A) 0 τ • normalizedPhysicalCurve A r e z τ) =
      rigidRotationGauge (Ω / A) 0 τ • F (normalizedPhysicalCurve A r e z τ)) :
    HasDerivAt (fun u => rigidRotationGauge (Ω / A) 0 u • normalizedPhysicalCurve A r e z u)
      (F (rigidRotationGauge (Ω / A) 0 τ • normalizedPhysicalCurve A r e z τ) +
        rigidRotationGauge (Ω / A) 0 τ • ((A * r)⁻¹ •
          p (physicalTimeFromNormalized A e τ))) τ := by
  have hh := hasDerivAt_rigidRotatedCurve
    (q := fun u _ => (A * r)⁻¹ • p (physicalTimeFromNormalized A e u))
    (Ω / A) 0 τ (hasDerivAt_normalizedPhysicalRigidCurve hA hr hd) hcov
  exact hh

theorem norm_normalizedPhysicalRotatedForcing
    {A r : ℝ} (hA : 0 < A) (hr : 0 < r) (Ω τ : ℝ) (v : E) :
    ‖rigidRotationGauge (Ω / A) 0 τ • ((A * r)⁻¹ • v)‖ = ‖v‖ / (A * r) := by
  rw [norm_smul, norm_rigidRotationGauge, one_mul, norm_smul, Real.norm_eq_abs,
    abs_inv, abs_of_pos (mul_pos hA hr)]
  ring

theorem rigidRotationGauge_normalized_physical_time
    {A e τ Ω : ℝ} (hA : A ≠ 0) :
    rigidRotationGauge (Ω / A) 0 τ =
      rigidRotationGauge Ω e (physicalTimeFromNormalized A e τ) := by
  unfold rigidRotationGauge physicalTimeFromNormalized
  congr 2
  congr 1
  field_simp
  ring

end Euler2D

end
