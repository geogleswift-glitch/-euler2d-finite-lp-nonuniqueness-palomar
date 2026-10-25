module

public import RequestProject.Euler.ContourStarGeometry

/-! The actual first-derivative identity underlying Green's formula on a
radial fan. Only a first derivative of the loop is used: a second
derivative is not introduced through an unnecessarily strong planar
divergence hypothesis. -/

@[expose] public section

noncomputable section

open Complex Set Filter Topology MeasureTheory intervalIntegral
open scoped ComplexConjugate

namespace Euler2D

def complexRealGradient (l : ℂ →L[ℝ] ℝ) : ℂ := (l 1 : ℂ) + (l I : ℂ) * I

theorem realLinearMap_complex_decomposition (l : ℂ →L[ℝ] ℝ) (w : ℂ) :
    l w = w.re * l 1 + w.im * l I := by
  have he : w = w.re • (1 : ℂ) + w.im • I := by
    apply Complex.ext <;> simp [Complex.real_smul]
  conv_lhs => rw [he]
  rw [map_add, map_smul, map_smul]
  rfl

theorem complex_gradient_fan_algebra (l : ℂ →L[ℝ] ℝ) (z a : ℂ) :
    (conj z * a).im • complexRealGradient l =
      l z • (-I * a) + l a • (I * z) := by
  rw [realLinearMap_complex_decomposition l z, realLinearMap_complex_decomposition l a]
  apply Complex.ext <;>
    simp [complexRealGradient, Complex.real_smul, Complex.mul_re, Complex.mul_im] <;> ring

def contourFanRadialPrimitive (ψ : ℂ → ℝ) (z dz : ℝ → ℂ) (θ s : ℝ) : ℂ :=
  (s * ψ (s • z θ)) • (-I * dz θ)

def contourFanAngularPrimitive (ψ : ℂ → ℝ) (z : ℝ → ℂ) (s θ : ℝ) : ℂ :=
  ψ (s • z θ) • (I * z θ)

def contourFanRadialDerivative (ψ : ℂ → ℝ) (dψ : ℂ → ℂ →L[ℝ] ℝ)
    (z dz : ℝ → ℂ) (θ s : ℝ) : ℂ :=
  (ψ (s • z θ) + s * dψ (s • z θ) (z θ)) • (-I * dz θ)

def contourFanAngularDerivative (ψ : ℂ → ℝ) (dψ : ℂ → ℂ →L[ℝ] ℝ)
    (z dz : ℝ → ℂ) (s θ : ℝ) : ℂ :=
  (s * dψ (s • z θ) (dz θ)) • (I * z θ) + ψ (s • z θ) • (I * dz θ)

theorem hasDerivAt_contourFanRadialPrimitive {ψ : ℂ → ℝ} {dψ : ℂ → ℂ →L[ℝ] ℝ}
    (hψ : ∀ x, HasFDerivAt ψ (dψ x) x) (z dz : ℝ → ℂ) (θ s : ℝ) :
    HasDerivAt (contourFanRadialPrimitive ψ z dz θ)
      (contourFanRadialDerivative ψ dψ z dz θ s) s := by
  have hs : HasDerivAt (fun t : ℝ => t • z θ) (z θ) s := by
    simpa only [one_smul] using (hasDerivAt_id s).smul_const (z θ)
  have hp := (hψ (s • z θ)).comp_hasDerivAt s hs
  have hh := ((hasDerivAt_id s).mul hp).smul_const (-I * dz θ)
  simpa only [contourFanRadialPrimitive, contourFanRadialDerivative,
    one_mul, id_eq] using hh

theorem hasDerivAt_contourFanAngularPrimitive {ψ : ℂ → ℝ} {dψ : ℂ → ℂ →L[ℝ] ℝ}
    {z dz : ℝ → ℂ} (hψ : ∀ x, HasFDerivAt ψ (dψ x) x)
    (hz : ∀ θ, HasDerivAt z (dz θ) θ) (s θ : ℝ) :
    HasDerivAt (contourFanAngularPrimitive ψ z s)
      (contourFanAngularDerivative ψ dψ z dz s θ) θ := by
  have hp := (hψ (s • z θ)).comp_hasDerivAt θ ((hz θ).const_smul s)
  have hh := hp.smul ((hz θ).const_mul I)
  simpa only [contourFanAngularPrimitive, contourFanAngularDerivative,
    Function.comp_def, Pi.smul_apply, map_smul, smul_eq_mul, add_comm] using hh

theorem contourFan_gradient_identity (ψ : ℂ → ℝ) (dψ : ℂ → ℂ →L[ℝ] ℝ)
    (z dz : ℝ → ℂ) (s θ : ℝ) :
    (s * contourAngularJacobian z dz θ) • complexRealGradient (dψ (s • z θ)) =
      contourFanRadialDerivative ψ dψ z dz θ s +
        contourFanAngularDerivative ψ dψ z dz s θ := by
  rw [mul_smul, contourAngularJacobian, complex_gradient_fan_algebra]
  simp only [contourFanRadialDerivative, contourFanAngularDerivative,
    smul_add, add_smul, mul_smul]
  rw [show -I * dz θ = -(I * dz θ) by ring]
  simp only [smul_neg]
  abel

theorem integral_contourFanRadialDerivative {ψ : ℂ → ℝ} {dψ : ℂ → ℂ →L[ℝ] ℝ}
    (hψ : ∀ x, HasFDerivAt ψ (dψ x) x) (hdψ : Continuous dψ)
    (z dz : ℝ → ℂ) (θ : ℝ) :
    (∫ s in (0 : ℝ)..1, contourFanRadialDerivative ψ dψ z dz θ s) =
      ψ (z θ) • (-I * dz θ) := by
  have hψc : Continuous ψ := continuous_iff_continuousAt.mpr (fun x => (hψ x).continuousAt)
  have hi : Continuous (contourFanRadialDerivative ψ dψ z dz θ) := by
    unfold contourFanRadialDerivative
    fun_prop
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s _ => hasDerivAt_contourFanRadialPrimitive hψ z dz θ s) (hi.intervalIntegrable 0 1)
  simpa only [contourFanRadialPrimitive, one_smul, zero_smul, one_mul,
    zero_mul, sub_zero] using he

theorem integral_contourFanAngularDerivative {ψ : ℂ → ℝ} {dψ : ℂ → ℂ →L[ℝ] ℝ}
    {z dz : ℝ → ℂ} (hψ : ∀ x, HasFDerivAt ψ (dψ x) x) (hdψ : Continuous dψ)
    (hz : ∀ θ, HasDerivAt z (dz θ) θ) (hdz : Continuous dz)
    (hp : Function.Periodic z (2 * Real.pi)) (s : ℝ) :
    (∫ θ in (0 : ℝ)..2 * Real.pi, contourFanAngularDerivative ψ dψ z dz s θ) = 0 := by
  have hψc : Continuous ψ := continuous_iff_continuousAt.mpr (fun x => (hψ x).continuousAt)
  have hzc : Continuous z := continuous_iff_continuousAt.mpr (fun θ => (hz θ).continuousAt)
  have hi : Continuous (contourFanAngularDerivative ψ dψ z dz s) := by
    unfold contourFanAngularDerivative
    fun_prop
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun θ _ => hasDerivAt_contourFanAngularPrimitive hψ hz s θ)
      (hi.intervalIntegrable 0 (2 * Real.pi))
  have hp0 : z (2 * Real.pi) = z 0 := by simpa only [zero_add] using hp 0
  simpa only [contourFanAngularPrimitive, hp0, sub_self] using he

end Euler2D
