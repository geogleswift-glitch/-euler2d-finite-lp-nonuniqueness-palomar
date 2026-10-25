module

public import Mathlib

/-! Exact time and length changes for already existing physical
trajectories. The entrance remains an absolute physical time. -/

@[expose] public section

noncomputable section

namespace Euler2D

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def physicalTimeFromNormalized (A e τ : ℝ) : ℝ := e + τ / A

def normalizedPhysicalCurve (A r e : ℝ) (z : ℝ → E) (τ : ℝ) : E :=
  r⁻¹ • z (physicalTimeFromNormalized A e τ)

theorem hasDerivAt_normalizedPhysicalCurve {A r e τ : ℝ} {z : ℝ → E} {v : E}
    (hz : HasDerivAt z v (physicalTimeFromNormalized A e τ)) :
    HasDerivAt (normalizedPhysicalCurve A r e z) ((A * r)⁻¹ • v) τ := by
  have ht : HasDerivAt (physicalTimeFromNormalized A e) A⁻¹ τ := by
    unfold physicalTimeFromNormalized
    simpa only [physicalTimeFromNormalized, div_eq_mul_inv, one_mul, id_eq] using
      ((hasDerivAt_id τ).mul_const A⁻¹).const_add e
  have hd := (hz.scomp τ ht).const_smul r⁻¹
  unfold normalizedPhysicalCurve
  simpa only [normalizedPhysicalCurve, Pi.smul_def, Function.comp_def, smul_smul, mul_inv_rev] using hd

theorem normalizedPhysicalCurve_initial (A r e : ℝ) (z : ℝ → E) :
    normalizedPhysicalCurve A r e z 0 = r⁻¹ • z e := by
  simp only [normalizedPhysicalCurve, physicalTimeFromNormalized, zero_div, add_zero]

theorem norm_normalizedPhysicalCurve {A r e τ : ℝ} (hr : 0 < r) (z : ℝ → E) :
    ‖normalizedPhysicalCurve A r e z τ‖ = ‖z (physicalTimeFromNormalized A e τ)‖ / r := by
  rw [normalizedPhysicalCurve, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hr]
  ring

end Euler2D

end
