module

public import RequestProject.Euler.ContourDomainFill
public import RequestProject.Euler.ContourFanJacobian

/-! The genuine injective radial fan chart of the actual enclosed domain.
The half-open angular interval includes the seam exactly once, and its
image omits only the origin, a Lebesgue null set. -/

@[expose] public section

noncomputable section

open Complex Set Filter Topology MeasureTheory
open scoped ComplexConjugate

namespace Euler2D

def contourFanParameterDomain : Set ℂ :=
  {p | p.re ∈ Ioo (0 : ℝ) 1 ∧ p.im ∈ Ico (0 : ℝ) (2 * Real.pi)}

theorem measurableSet_contourFanParameterDomain : MeasurableSet contourFanParameterDomain :=
  (measurableSet_Ioo.preimage Complex.measurable_re).inter
    (measurableSet_Ico.preimage Complex.measurable_im)

theorem contourFanMap_polar {z : ℝ → ℂ} {r : ℝ} (hr : 0 < r) (p : ℂ) :
    contourFanMap z p = ((p.re * ‖z p.im‖ : ℝ) : ℂ) *
      exp ((contourAngleLift z r p.im : ℝ) * I) := by
  rw [contourFanMap, Complex.real_smul]
  calc
    _ = (p.re : ℂ) * ((‖z p.im‖ : ℂ) * exp ((contourAngleLift z r p.im : ℝ) * I)) :=
      congrArg (fun w : ℂ => (p.re : ℂ) * w) (contour_polar_decomposition (z := z) hr p.im).symm
    _ = _ := by rw [Complex.ofReal_mul]; ring

section NearCircle

variable {z dz : ℝ → ℂ} {r ε : ℝ}
  (hr : 0 < r) (hε : 0 ≤ ε) (hsmall : ε ≤ r / 4)
  (hz : ∀ θ, HasDerivAt z (dz θ) θ)
  (hv : ∀ θ, ‖z θ - refCircle r θ‖ ≤ ε)
  (hd : ∀ θ, ‖dz θ - deriv (refCircle r) θ‖ ≤ ε)

include hr hε hsmall hz hv hd

theorem injOn_contourFanMap (hpz : Function.Periodic z (2 * Real.pi)) :
    Set.InjOn (contourFanMap z) contourFanParameterDomain := by
  intro p hp q hq heq
  have hp0 : 0 < p.re := hp.1.1
  have hq0 : 0 < q.re := hq.1.1
  have hzp : 0 < ‖z p.im‖ := norm_pos_iff.mpr (contour_ne_zero_of_quarter_radius hr hsmall (hv _))
  have hzq : 0 < ‖z q.im‖ := norm_pos_iff.mpr (contour_ne_zero_of_quarter_radius hr hsmall (hv _))
  have hAp : 0 < p.re * ‖z p.im‖ := mul_pos hp0 hzp
  have hAq : 0 < q.re * ‖z q.im‖ := mul_pos hq0 hzq
  have hpolar := heq
  rw [contourFanMap_polar hr, contourFanMap_polar hr] at hpolar
  have hamp : p.re * ‖z p.im‖ = q.re * ‖z q.im‖ := by
    have hn := congrArg norm hpolar
    simpa only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      Complex.norm_exp_ofReal_mul_I, mul_one, abs_mul, abs_of_pos hp0, abs_of_pos hq0,
      abs_of_nonneg (norm_nonneg (z p.im)), abs_of_nonneg (norm_nonneg (z q.im))] using hn
  have hexp : exp ((contourAngleLift z r p.im : ℝ) * I) =
      exp ((contourAngleLift z r q.im : ℝ) * I) := by
    rw [hamp] at hpolar
    exact mul_left_cancel₀ (by exact_mod_cast hAq.ne') hpolar
  have hm := strictMono_contourAngleLift hr hε hsmall hz hv hd
  have hαP : contourAngleLift z r (2 * Real.pi) = contourAngleLift z r 0 + 2 * Real.pi := by
    simpa only [zero_add] using contourAngleLift_add_period hpz r 0
  have hgap : |contourAngleLift z r p.im - contourAngleLift z r q.im| < 2 * Real.pi := by
    have hpLo := hm.monotone hp.2.1
    have hqLo := hm.monotone hq.2.1
    have hpHi := hm hp.2.2
    have hqHi := hm hq.2.2
    rw [hαP] at hpHi hqHi
    exact abs_lt.mpr ⟨by linarith, by linarith⟩
  have haeq : contourAngleLift z r p.im = contourAngleLift z r q.im :=
    eq_of_circleMap_eq (c := 0) (R := 1) (by norm_num) hgap
      (by simpa [circleMap] using hexp)
  have him : p.im = q.im := hm.injective haeq
  rw [him] at hamp
  have hre : p.re = q.re := (mul_left_inj' (ne_of_gt hzq)).mp hamp
  exact Complex.ext hre him

theorem image_contourFanParameterDomain (hpz : Function.Periodic z (2 * Real.pi)) :
    contourFanMap z '' contourFanParameterDomain =
      nearCircleEnclosedDomain hr hε hsmall hz hv hd \ {0} := by
  apply Set.Subset.antisymm
  · rintro x ⟨p, hp, rfl⟩
    constructor
    · rw [nearCircleEnclosedDomain_eq_contourRadialFill hr hε hsmall hz hv hd hpz]
      exact ⟨p.im, p.re, hp.1.1.le, hp.1.2, rfl⟩
    · change contourFanMap z p ≠ 0
      exact smul_ne_zero hp.1.1.ne' (contour_ne_zero_of_quarter_radius hr hsmall (hv p.im))
  · intro x hx
    have hx0 : x ≠ 0 := hx.2
    have hxD := hx.1
    rw [nearCircleEnclosedDomain_eq_contourRadialFill hr hε hsmall hz hv hd hpz] at hxD
    obtain ⟨θ, t, ht0, ht1, hxt⟩ := hxD
    have htne : t ≠ 0 := by
      intro ht
      apply hx0
      simpa only [ht, zero_smul] using hxt
    have htpos : 0 < t := lt_of_le_of_ne ht0 htne.symm
    obtain ⟨n, hn, -⟩ := existsUnique_add_zsmul_mem_Ico Real.two_pi_pos θ 0
    let φ : ℝ := θ + n • (2 * Real.pi)
    have hφ : φ ∈ Ico (0 : ℝ) (2 * Real.pi) := by
      simpa only [zero_add] using hn
    have hzφ : z φ = z θ := hpz.zsmul n θ
    refine ⟨⟨t, φ⟩, ⟨⟨htpos, ht1⟩, hφ⟩, ?_⟩
    change t • z φ = x
    rw [hzφ]
    exact hxt.symm

/-- Genuine change of variables on the actual enclosed domain. The
formula is the Jacobian theorem, and the omitted origin is a null set. -/
theorem integral_nearCircleEnclosedDomain_eq_fan {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (hpz : Function.Periodic z (2 * Real.pi)) (f : ℂ → E) :
    (∫ x in nearCircleEnclosedDomain hr hε hsmall hz hv hd, f x) =
      ∫ p in contourFanParameterDomain,
        (p.re * contourAngularJacobian z dz p.im) • f (contourFanMap z p) := by
  have hj := integral_image_eq_integral_abs_det_fderiv_smul volume
    measurableSet_contourFanParameterDomain
    (fun p _ => (hasFDerivAt_contourFanMap hz p).hasFDerivWithinAt)
    (injOn_contourFanMap hr hε hsmall hz hv hd hpz) f
  rw [image_contourFanParameterDomain hr hε hsmall hz hv hd hpz] at hj
  have hae : (nearCircleEnclosedDomain hr hε hsmall hz hv hd \ ({0} : Set ℂ)) =ᵐ[volume]
      nearCircleEnclosedDomain hr hε hsmall hz hv hd :=
    diff_ae_eq_self.mpr (measure_mono_null Set.inter_subset_right (measure_singleton 0))
  rw [setIntegral_congr_set hae] at hj
  refine hj.trans ?_
  apply setIntegral_congr_fun measurableSet_contourFanParameterDomain
  intro p hp
  dsimp only
  rw [det_contourFanMapDerivative,
    abs_of_pos (mul_pos hp.1.1
      (contourAngularJacobian_pos_of_quarter_radius hr hε hsmall (hv p.im) (hd p.im)))]

end NearCircle

end Euler2D
