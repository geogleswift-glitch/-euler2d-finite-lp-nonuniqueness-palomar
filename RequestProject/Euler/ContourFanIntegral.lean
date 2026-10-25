module

public import RequestProject.Euler.ContourFanGreen

/-! Actual Green integration on the parameter rectangle, proved from
first derivatives, the fundamental theorem of calculus and Fubini. -/

@[expose] public section

noncomputable section

open Complex Set Filter Topology MeasureTheory intervalIntegral
open scoped ComplexConjugate

namespace Euler2D

theorem integral_contourFan_gradient {ψ : ℂ → ℝ} {dψ : ℂ → ℂ →L[ℝ] ℝ}
    {z dz : ℝ → ℂ} (hψ : ∀ x, HasFDerivAt ψ (dψ x) x) (hdψ : Continuous dψ)
    (hz : ∀ θ, HasDerivAt z (dz θ) θ) (hdz : Continuous dz)
    (hp : Function.Periodic z (2 * Real.pi)) :
    (∫ p in Icc (0 : ℝ) (2 * Real.pi) ×ˢ Icc (0 : ℝ) 1,
      (p.2 * contourAngularJacobian z dz p.1) •
        complexRealGradient (dψ (p.2 • z p.1))) =
      -I * ∫ θ in (0 : ℝ)..2 * Real.pi, (ψ (z θ) : ℂ) * dz θ := by
  have hψc : Continuous ψ := continuous_iff_continuousAt.mpr (fun x => (hψ x).continuousAt)
  have hzc : Continuous z := continuous_iff_continuousAt.mpr (fun θ => (hz θ).continuousAt)
  let S : ℝ × ℝ → ℂ := fun p => contourFanRadialDerivative ψ dψ z dz p.1 p.2
  let A : ℝ × ℝ → ℂ := fun p => contourFanAngularDerivative ψ dψ z dz p.2 p.1
  have hSc : Continuous S := by
    unfold S contourFanRadialDerivative
    fun_prop
  have hAc : Continuous A := by
    unfold A contourFanAngularDerivative
    fun_prop
  have hSi : IntegrableOn S (Icc (0 : ℝ) (2 * Real.pi) ×ˢ Icc (0 : ℝ) 1) :=
    hSc.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
  have hAi : IntegrableOn A (Icc (0 : ℝ) (2 * Real.pi) ×ˢ Icc (0 : ℝ) 1) :=
    hAc.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
  have hAis : IntegrableOn (fun p : ℝ × ℝ => A p.swap)
      (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) (2 * Real.pi)) :=
    (hAc.comp continuous_swap).continuousOn.integrableOn_compact
      (isCompact_Icc.prod isCompact_Icc)
  have hS : (∫ p in Icc (0 : ℝ) (2 * Real.pi) ×ˢ Icc (0 : ℝ) 1, S p) =
      ∫ θ in Icc (0 : ℝ) (2 * Real.pi), ψ (z θ) • (-I * dz θ) := by
    rw [Measure.volume_eq_prod] at hSi ⊢
    rw [setIntegral_prod _ hSi]
    apply setIntegral_congr_fun measurableSet_Icc
    intro θ _
    change (∫ s in Icc (0 : ℝ) 1, contourFanRadialDerivative ψ dψ z dz θ s) = _
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact integral_contourFanRadialDerivative hψ hdψ z dz θ
  have hA : (∫ p in Icc (0 : ℝ) (2 * Real.pi) ×ˢ Icc (0 : ℝ) 1, A p) = 0 := by
    rw [Measure.volume_eq_prod] at hAis ⊢
    rw [← setIntegral_prod_swap (Icc (0 : ℝ) (2 * Real.pi)) (Icc (0 : ℝ) 1) A,
      setIntegral_prod _ hAis]
    have hzero : ∀ s : ℝ,
        (∫ θ in Icc (0 : ℝ) (2 * Real.pi), A (θ, s)) = 0 := by
      intro s
      change (∫ θ in Icc (0 : ℝ) (2 * Real.pi),
        contourFanAngularDerivative ψ dψ z dz s θ) = 0
      rw [integral_Icc_eq_integral_Ioc,
        ← intervalIntegral.integral_of_le (by positivity : (0 : ℝ) ≤ 2 * Real.pi)]
      exact integral_contourFanAngularDerivative hψ hdψ hz hdz hp s
    simp only [Prod.swap_prod_mk, hzero, integral_zero]
  have hpoint (p : ℝ × ℝ) :
      (p.2 * contourAngularJacobian z dz p.1) • complexRealGradient (dψ (p.2 • z p.1)) =
        S p + A p := contourFan_gradient_identity ψ dψ z dz p.2 p.1
  simp_rw [hpoint]
  rw [integral_add hSi hAi, hS, hA, add_zero, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by positivity : (0 : ℝ) ≤ 2 * Real.pi),
    ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro θ _
  simp only [Complex.real_smul]
  ring

end Euler2D
