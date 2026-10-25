module

public import RequestProject.Euler.CurlVelocityStability

/-!
# Fixed vorticity tests detect velocity departure

Integration by parts is the original distributional curl equation.
The test's rotated gradient is represented in the actual velocity L²
space, so Cauchy–Schwarz yields the uniform positive departure bound.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ContDiff

namespace Euler2D

def curlVelocityTest {ψ : R2 → ℝ} (hψ : ContDiff ℝ ∞ ψ) : L2T :=
  (continuous_vector_memLp_torus
    (continuous_torusVec.comp
      (((hψ.continuous_fderiv (by simp)).clm_apply continuous_const).prodMk
      (((hψ.continuous_fderiv (by simp)).clm_apply continuous_const).neg))) 2).toLp
        (fun x => torusVec (pd 1 ψ x) (-pd 0 ψ x))

lemma coeFn_curlVelocityTest {ψ : R2 → ℝ} (hψ : ContDiff ℝ ∞ ψ) :
    curlVelocityTest hψ =ᵐ[μT] fun x => torusVec (pd 1 ψ x) (-pd 0 ψ x) :=
  (continuous_vector_memLp_torus
    (continuous_torusVec.comp
      (((hψ.continuous_fderiv (by simp)).clm_apply continuous_const).prodMk
      (((hψ.continuous_fderiv (by simp)).clm_apply continuous_const).neg))) 2).coeFn_toLp

theorem curl_test_pairing_eq_inner {u : L2T} {w : R2 → ℝ}
    (hc : IsCurl u w) {ψ : R2 → ℝ} (hψ : IsScalarTest ψ) :
    (∫ x in torusBox, w x * ψ x) = inner ℝ u (curlVelocityTest hψ.1) := by
  rw [hc ψ hψ, MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [coeFn_curlVelocityTest hψ.1] with x hx
  rw [hx]
  simp [PiLp.inner_apply, Fin.sum_univ_two, torusVec_apply_zero,
    torusVec_apply_one, mul_comm, sub_eq_add_neg]

theorem abs_curl_test_difference_le {u v : L2T} {w z : Lp ℝ 2 μT}
    (hc : IsCurl u w) (hd : IsCurl v z) {ψ : R2 → ℝ} (hψ : IsScalarTest ψ) :
    |∫ x in torusBox, (w - z) x * ψ x| ≤ ‖u - v‖ * ‖curlVelocityTest hψ.1‖ := by
  rw [curl_test_pairing_eq_inner (hc.sub_L2 hd) hψ]
  exact abs_real_inner_le_norm _ _

/-- A fixed nonzero vorticity pairing gives a uniform L² departure.
Nondegeneracy of the gradient is derived from the positive pairing. -/
theorem velocity_departure_of_curl_test {u v : L2T} {w z : Lp ℝ 2 μT}
    (hc : IsCurl u w) (hd : IsCurl v z) {ψ : R2 → ℝ} (hψ : IsScalarTest ψ)
    {δ : ℝ} (hδ : 0 < δ) (hpair : δ ≤ |∫ x in torusBox, (w - z) x * ψ x|) :
    0 < ‖curlVelocityTest hψ.1‖ ∧ δ / ‖curlVelocityTest hψ.1‖ ≤ ‖u - v‖ := by
  have hb := hpair.trans (abs_curl_test_difference_le hc hd hψ)
  have hp : 0 < ‖curlVelocityTest hψ.1‖ := by
    by_contra hn
    have hz := le_antisymm (le_of_not_gt hn) (norm_nonneg (curlVelocityTest hψ.1))
    rw [hz, mul_zero] at hb
    exact (not_le_of_gt hδ) hb
  exact ⟨hp, (div_le_iff₀ hp).mpr hb⟩

def complexCurlTestBound {Ψ : R2 → ℂ} (hΨ : ContDiff ℝ ∞ Ψ) : ℝ :=
  ‖curlVelocityTest (Complex.reCLM.contDiff.comp hΨ)‖ +
    ‖curlVelocityTest (Complex.imCLM.contDiff.comp hΨ)‖

/-- The same fixed-test estimate for the complex fourth moment used in
the finite-stage departure argument. -/
theorem norm_complex_curl_test_difference_le {u v : L2T} {w z : Lp ℝ 2 μT}
    (hc : IsCurl u w) (hd : IsCurl v z) {Ψ : R2 → ℂ}
    (hΨ : ContDiff ℝ ∞ Ψ) (hp : IsTorusPeriodic Ψ) :
    ‖∫ x in torusBox, ((w - z) x : ℂ) * Ψ x‖ ≤
      ‖u - v‖ * complexCurlTestBound hΨ := by
  have hInt : Integrable (fun x => ((w - z) x : ℂ) * Ψ x) μT :=
    (Lp.memLp (w - z)).ofReal.integrable_mul (continuous_vector_memLp_torus hΨ.continuous 2)
  have hre : IsScalarTest (fun x => (Ψ x).re) :=
    ⟨Complex.reCLM.contDiff.comp hΨ, fun x i => congrArg Complex.re (hp x i)⟩
  have him : IsScalarTest (fun x => (Ψ x).im) :=
    ⟨Complex.imCLM.contDiff.comp hΨ, fun x i => congrArg Complex.im (hp x i)⟩
  have hR : (∫ x in torusBox, ((w - z) x : ℂ) * Ψ x).re =
      ∫ x in torusBox, (w - z) x * (Ψ x).re := by
    simpa only [RCLike.re_to_complex, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero] using (integral_re hInt).symm
  have hI : (∫ x in torusBox, ((w - z) x : ℂ) * Ψ x).im =
      ∫ x in torusBox, (w - z) x * (Ψ x).im := by
    simpa only [RCLike.im_to_complex, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, add_zero] using (integral_im hInt).symm
  calc
    _ ≤ |(∫ x in torusBox, ((w - z) x : ℂ) * Ψ x).re| +
        |(∫ x in torusBox, ((w - z) x : ℂ) * Ψ x).im| := Complex.norm_le_abs_re_add_abs_im _
    _ ≤ ‖u - v‖ * ‖curlVelocityTest hre.1‖ + ‖u - v‖ * ‖curlVelocityTest him.1‖ := by
      rw [hR, hI]
      exact add_le_add (abs_curl_test_difference_le hc hd hre) (abs_curl_test_difference_le hc hd him)
    _ = _ := by unfold complexCurlTestBound; ring

theorem velocity_departure_of_complex_curl_test {u v : L2T} {w z : Lp ℝ 2 μT}
    (hc : IsCurl u w) (hd : IsCurl v z) {Ψ : R2 → ℂ}
    (hΨ : ContDiff ℝ ∞ Ψ) (hp : IsTorusPeriodic Ψ)
    {δ : ℝ} (hδ : 0 < δ)
    (hpair : δ ≤ ‖∫ x in torusBox, ((w - z) x : ℂ) * Ψ x‖) :
    0 < complexCurlTestBound hΨ ∧ δ / complexCurlTestBound hΨ ≤ ‖u - v‖ := by
  have hb := hpair.trans (norm_complex_curl_test_difference_le hc hd hΨ hp)
  have hK : 0 ≤ complexCurlTestBound hΨ := add_nonneg (norm_nonneg _) (norm_nonneg _)
  have hpK : 0 < complexCurlTestBound hΨ := by
    by_contra hn
    have hz := le_antisymm (le_of_not_gt hn) hK
    rw [hz, mul_zero] at hb
    exact (not_le_of_gt hδ) hb
  exact ⟨hpK, (div_le_iff₀ hpK).mpr hb⟩

end Euler2D

end
