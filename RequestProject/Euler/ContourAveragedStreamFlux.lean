module

public import RequestProject.Euler.ContourStreamFlux

/-! Actual zero flux survives averaging genuine stream gradients over
a bounded measurable planar source. This uses Fubini on the real
parameter–source product and actual spatial integrability. -/

@[expose] public section

noncomputable section

open Complex Set Filter Topology MeasureTheory
open scoped ComplexConjugate

namespace Euler2D

theorem continuous_complexRealGradient : Continuous (complexRealGradient : (ℂ →L[ℝ] ℝ) → ℂ) := by
  unfold complexRealGradient
  fun_prop

theorem integral_normalFlux_averaged_stream_zero
    {ψ : ℂ → ℂ → ℝ} {dψ : ℂ → ℂ → ℂ →L[ℝ] ℝ}
    {z dz : ℝ → ℂ} {Ω : Set ℂ} {R : ℝ}
    (hψ : ∀ y x, HasFDerivAt (ψ y) (dψ y x) x)
    (hdψ : Continuous (fun p : ℂ × ℂ => dψ p.1 p.2))
    (hΩ : Ω ⊆ Metric.closedBall (0 : ℂ) R)
    (hz : ∀ θ, HasDerivAt z (dz θ) θ) (hdzc : Continuous dz)
    (hp : Function.Periodic z (2 * Real.pi)) :
    (∫ θ in (0 : ℝ)..2 * Real.pi,
      (conj (I * ∫ y in Ω, complexRealGradient (dψ y (z θ))) * dz θ).im) = 0 := by
  have hzc : Continuous z := continuous_iff_continuousAt.mpr (fun θ => (hz θ).continuousAt)
  let G : ℝ × ℂ → ℂ := fun p => complexRealGradient (dψ p.2 (z p.1))
  have hGc : Continuous G := continuous_complexRealGradient.comp
    (hdψ.comp (continuous_snd.prodMk (hzc.comp continuous_fst)))
  let F : ℝ × ℂ → ℝ := fun p => (conj (I * G p) * dz p.1).im
  have hFc : Continuous F := by dsimp only [F]; fun_prop
  have hFi : IntegrableOn F (Icc (0 : ℝ) (2 * Real.pi) ×ˢ Ω) :=
    (hFc.continuousOn.integrableOn_compact
      (isCompact_Icc.prod (isCompact_closedBall (0 : ℂ) R))).mono_set (Set.prod_mono Subset.rfl hΩ)
  have hFis : IntegrableOn (fun p : ℂ × ℝ => F p.swap) (Ω ×ˢ Icc (0 : ℝ) (2 * Real.pi)) :=
    ((hFc.comp continuous_swap).continuousOn.integrableOn_compact
      ((isCompact_closedBall (0 : ℂ) R).prod isCompact_Icc)).mono_set (Set.prod_mono hΩ Subset.rfl)
  have hpoint (θ : ℝ) :
      (conj (I * ∫ y in Ω, complexRealGradient (dψ y (z θ))) * dz θ).im =
        ∫ y in Ω, F (θ, y) := by
    have hgi : IntegrableOn (fun y => G (θ, y)) Ω :=
      ((hGc.comp (continuous_const.prodMk continuous_id)).continuousOn.integrableOn_compact
        (isCompact_closedBall (0 : ℂ) R)).mono_set hΩ
    have hci := (Complex.conjCLE.toContinuousLinearMap.integrable_comp
      (hgi.const_mul I)).mul_const (dz θ)
    have hci' : Integrable (fun y => conj (I * G (θ, y)) * dz θ) (volume.restrict Ω) := hci
    have him : (∫ y in Ω, (conj (I * G (θ, y)) * dz θ).im) =
        (∫ y in Ω, conj (I * G (θ, y)) * dz θ).im := by
      simpa only [Function.comp_def, Complex.imCLM_apply] using
        Complex.imCLM.integral_comp_comm hci'
    change _ = ∫ y in Ω, (conj (I * G (θ, y)) * dz θ).im
    rw [him, integral_mul_const, integral_conj, integral_const_mul]
  rw [intervalIntegral.integral_of_le (by positivity : (0 : ℝ) ≤ 2 * Real.pi),
    ← integral_Icc_eq_integral_Ioc]
  simp_rw [hpoint]
  rw [Measure.volume_eq_prod] at hFi hFis
  rw [← setIntegral_prod F hFi,
    ← setIntegral_prod_swap (Icc (0 : ℝ) (2 * Real.pi)) Ω F,
    setIntegral_prod _ hFis]
  have hzero (y : ℂ) : (∫ θ in Icc (0 : ℝ) (2 * Real.pi), F (θ, y)) = 0 := by
    rw [integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (by positivity : (0 : ℝ) ≤ 2 * Real.pi)]
    change (∫ θ in (0 : ℝ)..2 * Real.pi,
      (conj (I * complexRealGradient (dψ y (z θ))) * dz θ).im) = 0
    exact integral_normalFlux_stream_zero (ψ := ψ y) (dψ := dψ y) (z := z) (dz := dz) (hψ y)
      (hdψ.comp (continuous_const.prodMk continuous_id)) hz hdzc hp
  simp only [Prod.swap_prod_mk, hzero, integral_zero]

end Euler2D
