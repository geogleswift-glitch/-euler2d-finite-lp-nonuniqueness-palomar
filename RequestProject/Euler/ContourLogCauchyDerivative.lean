module

public import RequestProject.Euler.ContourCauchyUniformTruncation
public import RequestProject.Euler.ContourDerivativeLower
public import RequestProject.Euler.ContourDerivativePhase

/-!
# The genuine logarithmic spatial derivative from actual Cauchy principal values

The finite-cutoff identity uses the actual derivative phase density.
The constant-density principal-value terms cancel algebraically.
-/

@[expose] public section

noncomputable section

open Set MeasureTheory Filter Topology Complex
open scoped NNReal ComplexConjugate

namespace Euler2D

theorem realPart_div_smul_eq_half_phase {a b d f : ℂ} (hb : b ≠ 0)
    (hf : f = conj b / b) :
    (a / d).re • b = (1 / 2 : ℂ) * (a * (b / d) + conj a * conj ((b / d) * f)) := by
  have hw : (b / d) * f = conj b / d := by
    rw [hf]
    simp only [div_eq_mul_inv]
    calc
      _ = (conj b * d⁻¹) * (b * b⁻¹) := by ring
      _ = _ := by rw [mul_inv_cancel₀ hb, mul_one]
  rw [Complex.real_smul, Complex.re_eq_add_conj, hw]
  simp only [div_eq_mul_inv, map_mul, map_inv₀, Complex.conj_conj]
  ring

/-- The literal spatial-log derivative integrated over the actual symmetric cutoff. -/
def contourLogCauchyTruncated (z dz : ℝ → ℂ) (θ r ε : ℝ) : ℂ :=
  ∫ τ in symmetricContourTruncation r ε, (dz θ / (z θ - z (θ + τ))).re • dz (θ + τ)

/-- The exact finite-cutoff identity, with all terms genuinely integrable. -/
theorem contourLogCauchyTruncated_eq {z dz f : ℝ → ℂ} {θ r ε : ℝ}
    (hdz : ∀ s, dz s ≠ 0) (hphase : ∀ s, f s = conj (dz s) / dz s)
    (hK : IntegrableOn (fun τ => dz (θ + τ) / (z θ - z (θ + τ)))
      (symmetricContourTruncation r ε))
    (hW : IntegrableOn (fun τ => (dz (θ + τ) / (z θ - z (θ + τ))) * f (θ + τ))
      (symmetricContourTruncation r ε)) :
    contourLogCauchyTruncated z dz θ r ε =
      (1 / 2 : ℂ) * (dz θ * contourCauchyTruncated z dz θ r ε +
        conj (dz θ) * conj (contourCauchyWeightedTruncated z dz f θ r ε)) := by
  have hconj : IntegrableOn
      (fun τ => conj ((dz (θ + τ) / (z θ - z (θ + τ))) * f (θ + τ)))
      (symmetricContourTruncation r ε) := by
    simpa only [Complex.conjLIE_apply] using (Complex.conjLIE.integrable_comp_iff).mpr hW
  have heq : (fun τ => (dz θ / (z θ - z (θ + τ))).re • dz (θ + τ)) =
      fun τ => (1 / 2 : ℂ) * (dz θ * (dz (θ + τ) / (z θ - z (θ + τ))) +
        conj (dz θ) * conj ((dz (θ + τ) / (z θ - z (θ + τ))) * f (θ + τ))) := by
    ext τ
    exact realPart_div_smul_eq_half_phase (hdz (θ + τ)) (hphase (θ + τ))
  unfold contourLogCauchyTruncated
  rw [heq, integral_const_mul, integral_add (hK.const_mul (dz θ)) (hconj.const_mul (conj (dz θ))),
    integral_const_mul, integral_const_mul, integral_conj]
  rfl

theorem integrableOn_contourLogCauchyTruncatedIntegrand {z dz f : ℝ → ℂ} {θ r ε : ℝ}
    (hdz : ∀ s, dz s ≠ 0) (hphase : ∀ s, f s = conj (dz s) / dz s)
    (hK : IntegrableOn (fun τ => dz (θ + τ) / (z θ - z (θ + τ)))
      (symmetricContourTruncation r ε))
    (hW : IntegrableOn (fun τ => (dz (θ + τ) / (z θ - z (θ + τ))) * f (θ + τ))
      (symmetricContourTruncation r ε)) :
    IntegrableOn (fun τ => (dz θ / (z θ - z (θ + τ))).re • dz (θ + τ))
      (symmetricContourTruncation r ε) := by
  have hconj : IntegrableOn
      (fun τ => conj ((dz (θ + τ) / (z θ - z (θ + τ))) * f (θ + τ)))
      (symmetricContourTruncation r ε) := by
    simpa only [Complex.conjLIE_apply] using (Complex.conjLIE.integrable_comp_iff).mpr hW
  have hi := ((hK.const_mul (dz θ)).add (hconj.const_mul (conj (dz θ)))).const_mul (1 / 2 : ℂ)
  have heq : (fun τ => (1 / 2 : ℂ) * (dz θ * (dz (θ + τ) / (z θ - z (θ + τ))) +
      conj (dz θ) * conj ((dz (θ + τ) / (z θ - z (θ + τ))) * f (θ + τ)))) =
      fun τ => (dz θ / (z θ - z (θ + τ))).re • dz (θ + τ) := by
    ext τ
    exact (realPart_div_smul_eq_half_phase (hdz (θ + τ)) (hphase (θ + τ))).symm
  change IntegrableOn (fun τ => (1 / 2 : ℂ) *
    (dz θ * (dz (θ + τ) / (z θ - z (θ + τ))) +
      conj (dz θ) * conj ((dz (θ + τ) / (z θ - z (θ + τ))) * f (θ + τ))))
    (symmetricContourTruncation r ε) at hi
  rw [heq] at hi
  exact hi

theorem contourC1LogCauchyTruncated_eq {γ : ℝ≥0} (Z : ContourC1Space γ)
    (f : ContourHolderSpace γ) {c ε : ℝ} (hγ : 0 < (γ : ℝ)) (hc : 0 < c) (hε : 0 < ε)
    (hchord : ∀ θ τ : ℝ, |τ| ≤ Real.pi → c * |τ| ≤
      ‖ContourC1Space.lift γ Z θ - ContourC1Space.lift γ Z (θ + τ)‖)
    (hphase : ∀ s : ℝ, f (s : ContourCircle) = conj (deriv (ContourC1Space.lift γ Z) s) /
      deriv (ContourC1Space.lift γ Z) s) (θ : ℝ) :
    contourLogCauchyTruncated (ContourC1Space.lift γ Z) (deriv (ContourC1Space.lift γ Z)) θ Real.pi ε =
      (1 / 2 : ℂ) * (deriv (ContourC1Space.lift γ Z) θ *
          contourCauchyTruncated (ContourC1Space.lift γ Z) (deriv (ContourC1Space.lift γ Z)) θ Real.pi ε +
        conj (deriv (ContourC1Space.lift γ Z) θ) *
          conj (contourCauchyWeightedTruncated (ContourC1Space.lift γ Z)
            (deriv (ContourC1Space.lift γ Z)) (fun s : ℝ => f (s : ContourCircle)) θ Real.pi ε)) := by
  have hiR := integrableOn_contourCauchyPoleIntegrand (ContourC1Space.contDiff_lift Z).continuous
    (ContourC1Space.contDiff_lift Z).continuous_deriv_one hγ (norm_nonneg Z) hc Real.pi_pos.le
    (fun s => (ContourC1Space.hasDerivAt_lift Z s).differentiableAt.hasDerivAt)
    (norm_contourC1_deriv_lift_sub_le Z) hchord θ
  have hiI := integrableOn_contourC1CauchyIncrementIntegrand Z f hγ hc
    (fun τ hτ => hchord θ τ (abs_le.mpr hτ))
  exact contourLogCauchyTruncated_eq
    (z := ContourC1Space.lift γ Z) (dz := deriv (ContourC1Space.lift γ Z))
    (f := fun s : ℝ => f (s : ContourCircle)) (θ := θ) (r := Real.pi) (ε := ε)
    (contourC1_deriv_lift_ne_zero Z hc hchord) hphase
    (integrableOn_symmetricContourTruncation_of_integrable_remainder
      (g := fun τ => deriv (ContourC1Space.lift γ Z) (θ + τ) /
        (ContourC1Space.lift γ Z θ - ContourC1Space.lift γ Z (θ + τ))) hε hiR)
    (integrableOn_symmetricWeightedTruncated
      (g := fun τ => deriv (ContourC1Space.lift γ Z) (θ + τ) /
        (ContourC1Space.lift γ Z θ - ContourC1Space.lift γ Z (θ + τ)))
      (f := fun s : ℝ => f (s : ContourCircle)) hε hiR hiI)

private theorem tendstoUniformly_half_phase_combination
    {A ι : Type*} {l : Filter ι} {F G : ι → A → ℂ} {f g a : A → ℂ} {M : ℝ}
    (hF : TendstoUniformly F f l) (hG : TendstoUniformly G g l) (ha : ∀ x, ‖a x‖ ≤ M) :
    TendstoUniformly (fun i x => (1 / 2 : ℂ) * (a x * F i x + conj (a x) * conj (G i x)))
      (fun x => (1 / 2 : ℂ) * (a x * f x + conj (a x) * conj (g x))) l := by
  let C : ℝ := max 1 M
  have hC : 0 < C := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have haC (x : A) : ‖a x‖ ≤ C := (ha x).trans (le_max_right _ _)
  rw [Metric.tendstoUniformly_iff] at hF hG ⊢
  intro δ hδ
  filter_upwards [hF (δ / C) (div_pos hδ hC), hG (δ / C) (div_pos hδ hC)] with i hiF hiG x
  have hfnear := hiF x
  have hgnear := hiG x
  rw [dist_eq_norm] at hfnear hgnear ⊢
  have heq : (1 / 2 : ℂ) * (a x * f x + conj (a x) * conj (g x)) -
      (1 / 2 : ℂ) * (a x * F i x + conj (a x) * conj (G i x)) =
      (1 / 2 : ℂ) * (a x * (f x - F i x) + conj (a x) * conj (g x - G i x)) := by
    rw [map_sub]
    ring
  rw [heq, norm_mul, show ‖(1 / 2 : ℂ)‖ = (1 / 2 : ℝ) by norm_num]
  have hnorm : ‖a x * (f x - F i x) + conj (a x) * conj (g x - G i x)‖ ≤
      C * (‖f x - F i x‖ + ‖g x - G i x‖) := by
    calc
      _ ≤ ‖a x‖ * ‖f x - F i x‖ + ‖a x‖ * ‖g x - G i x‖ := by
        simpa only [norm_mul, Complex.norm_conj] using norm_add_le
          (a x * (f x - F i x)) (conj (a x) * conj (g x - G i x))
      _ ≤ C * ‖f x - F i x‖ + C * ‖g x - G i x‖ := add_le_add
        (mul_le_mul_of_nonneg_right (haC x) (norm_nonneg _))
        (mul_le_mul_of_nonneg_right (haC x) (norm_nonneg _))
      _ = _ := by ring
  calc
    _ ≤ (1 / 2 : ℝ) * (C * (‖f x - F i x‖ + ‖g x - G i x‖)) :=
      mul_le_mul_of_nonneg_left hnorm (by norm_num)
    _ < (1 / 2 : ℝ) * (C * (δ / C + δ / C)) := by
      exact mul_lt_mul_of_pos_left (mul_lt_mul_of_pos_left (add_lt_add hfnear hgnear) hC) (by norm_num)
    _ = δ := by field_simp <;> norm_num

theorem cauchy_phase_constant_cancel {a f : ℂ} (ha : a ≠ 0) (hf : f = conj a / a) :
    a * (-I * (Real.pi : ℂ)) + conj a * conj ((-I * (Real.pi : ℂ)) * f) = 0 := by
  have hac : conj a ≠ 0 := norm_pos_iff.mp (by
    simpa only [Complex.norm_conj] using norm_pos_iff.mpr ha)
  rw [hf]
  simp only [map_mul, map_div₀, map_neg, Complex.conj_I, Complex.conj_ofReal, Complex.conj_conj, neg_neg]
  field_simp
  ring

/-- Actual Cauchy principal values give the logarithmic spatial-derivative limit uniformly in angle. -/
theorem tendstoUniformly_contourC1LogCauchyTruncated_near_circle_with_phase
    {γ : ℝ≥0} (Z Z₀ : ContourC1Space γ) (f : ContourHolderSpace γ) {r : ℝ}
    (hγ : 0 < (γ : ℝ)) (hr : 0 < r)
    (href : ContourC1Space.lift γ Z₀ = refCircle r)
    (hsmall : ‖Z - Z₀‖ < 2 * r / Real.pi)
    (hphase : ∀ s : ℝ, f (s : ContourCircle) = conj (deriv (ContourC1Space.lift γ Z) s) /
      deriv (ContourC1Space.lift γ Z) s) :
    TendstoUniformly (fun ε θ => contourLogCauchyTruncated (ContourC1Space.lift γ Z)
      (deriv (ContourC1Space.lift γ Z)) θ Real.pi ε)
      (fun θ => (1 / 2 : ℂ) * conj (deriv (ContourC1Space.lift γ Z) θ) *
        conj (contourC1CauchyIncrement Z f θ)) (𝓝[>] (0 : ℝ)) := by
  have hc : 0 < 2 * r / Real.pi - ‖Z - Z₀‖ := sub_pos.mpr hsmall
  have hchord : ∀ θ τ : ℝ, |τ| ≤ Real.pi → (2 * r / Real.pi - ‖Z - Z₀‖) * |τ| ≤
      ‖ContourC1Space.lift γ Z θ - ContourC1Space.lift γ Z (θ + τ)‖ :=
    fun θ τ hτ => contourC1_chord_lower_of_norm_sub Z Z₀ hr.le href θ (abs_le.mp hτ)
  have hK := tendstoUniformly_contourC1CauchyTruncated_near_circle Z Z₀ hγ hr href hsmall
  have hW := tendstoUniformly_contourC1CauchyWeightedTruncated_near_circle Z Z₀ f hγ hr href hsmall
  have hu := tendstoUniformly_half_phase_combination hK hW (ContourC1Space.norm_deriv_lift_le Z)
  have helim : (fun θ : ℝ => (1 / 2 : ℂ) *
      (deriv (ContourC1Space.lift γ Z) θ * (-I * (Real.pi : ℂ)) +
        conj (deriv (ContourC1Space.lift γ Z) θ) *
          conj ((-I * (Real.pi : ℂ)) * f (θ : ContourCircle) + contourC1CauchyIncrement Z f θ))) =
      fun θ : ℝ => (1 / 2 : ℂ) * conj (deriv (ContourC1Space.lift γ Z) θ) *
        conj (contourC1CauchyIncrement Z f θ) := by
    ext θ
    have hcancel := cauchy_phase_constant_cancel (contourC1_deriv_lift_ne_zero Z hc hchord θ) (hphase θ)
    rw [map_add, mul_add]
    linear_combination (1 / 2 : ℂ) * hcancel
  rw [helim] at hu
  rw [Metric.tendstoUniformly_iff] at hu ⊢
  intro δ hδ
  filter_upwards [self_mem_nhdsWithin, hu δ hδ] with ε hε hnear θ
  rw [contourC1LogCauchyTruncated_eq Z f hγ hc hε hchord hphase θ]
  exact hnear θ

/-- The phase is the actual Hölder derivative quotient, with no separate phase-density assumption. -/
theorem tendstoUniformly_contourC1LogCauchyTruncated_near_circle
    {γ : ℝ≥0} (Z Z₀ : ContourC1Space γ) {c r : ℝ}
    (hγ : 0 < (γ : ℝ)) (hc : 0 < c)
    (hchord : ∀ θ τ : ℝ, |τ| ≤ Real.pi → c * |τ| ≤
      ‖ContourC1Space.lift γ Z θ - ContourC1Space.lift γ Z (θ + τ)‖)
    (hr : 0 < r) (href : ContourC1Space.lift γ Z₀ = refCircle r)
    (hsmall : ‖Z - Z₀‖ < 2 * r / Real.pi) :
    TendstoUniformly (fun ε θ => contourLogCauchyTruncated (ContourC1Space.lift γ Z)
      (deriv (ContourC1Space.lift γ Z)) θ Real.pi ε)
      (fun θ => (1 / 2 : ℂ) * conj (deriv (ContourC1Space.lift γ Z) θ) *
        conj (contourC1CauchyIncrement Z (contourDerivativePhase Z hc hchord) θ)) (𝓝[>] (0 : ℝ)) :=
  tendstoUniformly_contourC1LogCauchyTruncated_near_circle_with_phase Z Z₀
    (contourDerivativePhase Z hc hchord) hγ hr href hsmall (contourDerivativePhase_apply Z hc hchord)

theorem tendstoUniformly_contourC1LogCauchyTruncated_near_circle_filter
    {ι : Type*} {l : Filter ι} {ε : ι → ℝ} {γ : ℝ≥0}
    (Z Z₀ : ContourC1Space γ) {c r : ℝ}
    (hε : Tendsto ε l (𝓝 (0 : ℝ))) (hpos : ∀ᶠ i in l, 0 < ε i)
    (hγ : 0 < (γ : ℝ)) (hc : 0 < c)
    (hchord : ∀ θ τ : ℝ, |τ| ≤ Real.pi → c * |τ| ≤
      ‖ContourC1Space.lift γ Z θ - ContourC1Space.lift γ Z (θ + τ)‖)
    (hr : 0 < r) (href : ContourC1Space.lift γ Z₀ = refCircle r)
    (hsmall : ‖Z - Z₀‖ < 2 * r / Real.pi) :
    TendstoUniformly (fun i θ => contourLogCauchyTruncated (ContourC1Space.lift γ Z)
      (deriv (ContourC1Space.lift γ Z)) θ Real.pi (ε i))
      (fun θ => (1 / 2 : ℂ) * conj (deriv (ContourC1Space.lift γ Z) θ) *
        conj (contourC1CauchyIncrement Z (contourDerivativePhase Z hc hchord) θ)) l := by
  have hu := tendstoUniformly_contourC1LogCauchyTruncated_near_circle Z Z₀ hγ hc hchord hr href hsmall
  rw [Metric.tendstoUniformly_iff] at hu ⊢
  intro δ hδ
  exact (tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within ε hε hpos).eventually (hu δ hδ)

end Euler2D
