module

public import RequestProject.Euler.ContourCauchyIncrement

/-!
# Actual near and far estimates for the universal Hilbert increment

The operator below is the literal relative-angle `1/τ` increment.  The
scalar estimates isolate the far kernel difference and the cancellation
of its two constant-density integrals.  They are the numerical pieces
of the Hölder estimate, without assuming that estimate.
-/

@[expose] public section

noncomputable section

open Set MeasureTheory Filter Topology Real
open scoped NNReal Interval

namespace Euler2D

theorem abs_reciprocal_translation_sub_le {s h : ℝ}
    (hh : 0 < h) (hfar : 2 * h ≤ |s|) :
    |(s - h)⁻¹ - s⁻¹| ≤ 2 * h / |s| ^ 2 := by
  have hs : 0 < |s| := by linarith
  have htri : |s| ≤ |s - h| + h := by
    calc
      |s| = |(s - h) + h| := by congr 1; ring
      _ ≤ |s - h| + |h| := abs_add_le _ _
      _ = _ := by rw [abs_of_pos hh]
  have hd : 0 < |s - h| := by linarith
  have hsne : s ≠ 0 := abs_pos.mp hs
  have hdne : s - h ≠ 0 := abs_pos.mp hd
  rw [inv_sub_inv hdne hsne, abs_div, abs_mul,
    show s - (s - h) = h by ring, abs_of_pos hh]
  apply (div_le_div_iff₀ (mul_pos hd hs) (sq_pos_of_pos hs)).mpr
  have hhalf : |s| ≤ 2 * |s - h| := by linarith
  have hm := mul_le_mul_of_nonneg_left hhalf (mul_nonneg hh.le hs.le)
  nlinarith [hm]

theorem integral_far_rpow_le {γ a b : ℝ} (hγ : γ < 1)
    (ha : 0 < a) (hab : a ≤ b) :
    (∫ t in a..b, t ^ (γ - 2)) ≤ a ^ (γ - 1) / (1 - γ) := by
  have hnot : (0 : ℝ) ∉ uIcc a b := by
    rw [uIcc_of_le hab]
    intro h
    linarith [h.1]
  rw [integral_rpow (Or.inr ⟨by linarith, hnot⟩),
    show γ - 2 + 1 = γ - 1 by ring]
  have hden : 0 < 1 - γ := sub_pos.mpr hγ
  calc
    _ = (a ^ (γ - 1) - b ^ (γ - 1)) / (1 - γ) := by
      have hinv : (γ - 1)⁻¹ = -(1 - γ)⁻¹ := by
        rw [show γ - 1 = -(1 - γ) by ring, inv_neg]
      simp only [div_eq_mul_inv]
      rw [hinv]
      ring
    _ ≤ _ := div_le_div_of_nonneg_right
      (sub_le_self _ (Real.rpow_nonneg (ha.le.trans hab) _)) hden.le

/-- Exact cancellation of the two common far constant-density intervals. -/
theorem integral_common_far_reciprocal {P h : ℝ} (hP : 0 < P)
    (hh : 0 < h) (hsmall : h ≤ P / 4) :
    (∫ s in (h - P)..(-2 * h), (s - h)⁻¹) +
      (∫ s in (2 * h)..P, (s - h)⁻¹) = Real.log (3 * (P - h) / P) := by
  rw [intervalIntegral.integral_comp_sub_right (fun s : ℝ => s⁻¹),
    intervalIntegral.integral_comp_sub_right (fun s : ℝ => s⁻¹)]
  rw [show h - P - h = -P by ring, show -2 * h - h = -3 * h by ring,
    show 2 * h - h = h by ring]
  rw [integral_inv_of_neg (by linarith) (by linarith),
    integral_inv_of_pos hh (by linarith)]
  have hneg : (-3 * h) / -P = 3 * h / P := by ring
  have hratioA : 3 * h / P ≠ 0 := ne_of_gt (div_pos (by positivity) hP)
  have hratioB : (P - h) / h ≠ 0 := ne_of_gt (div_pos (by linarith) hh)
  rw [hneg, ← Real.log_mul hratioA hratioB]
  congr 1
  field_simp

theorem abs_integral_common_far_reciprocal_le {P h : ℝ} (hP : 0 < P)
    (hh : 0 < h) (hsmall : h ≤ P / 4) :
    |(∫ s in (h - P)..(-2 * h), (s - h)⁻¹) +
      (∫ s in (2 * h)..P, (s - h)⁻¹)| ≤ Real.log 3 := by
  rw [integral_common_far_reciprocal hP hh hsmall]
  have hr1 : 1 ≤ 3 * (P - h) / P := (le_div_iff₀ hP).mpr (by linarith)
  have hr3 : 3 * (P - h) / P ≤ 3 := (div_le_iff₀ hP).mpr (by linarith)
  rw [abs_of_nonneg (Real.log_nonneg hr1)]
  exact Real.log_le_log (by linarith) hr3

/-- The actual universal increment integrand. -/
def hilbertIncrementIntegrand (f : ℝ → ℂ) (θ τ : ℝ) : ℂ :=
  (τ : ℂ)⁻¹ * (f (θ + τ) - f θ)

@[simp] theorem hilbertIncrementIntegrand_zero (f : ℝ → ℂ) (θ : ℝ) :
    hilbertIncrementIntegrand f θ 0 = 0 := by simp [hilbertIncrementIntegrand]

theorem measurable_hilbertIncrementIntegrand {f : ℝ → ℂ} (hf : Measurable f) (θ : ℝ) :
    Measurable (hilbertIncrementIntegrand f θ) :=
  ((Complex.measurable_ofReal.comp measurable_id).inv).mul
    ((hf.comp (measurable_const.add measurable_id)).sub measurable_const)

theorem norm_hilbertIncrementIntegrand_le {f : ℝ → ℂ} {θ τ γ H : ℝ}
    (hH : 0 ≤ H) (hf : ‖f (θ + τ) - f θ‖ ≤ H * |τ| ^ γ) :
    ‖hilbertIncrementIntegrand f θ τ‖ ≤ H * |τ| ^ (γ - 1) := by
  by_cases hτ : τ = 0
  · subst τ
    rw [hilbertIncrementIntegrand_zero, norm_zero]
    exact mul_nonneg hH (Real.rpow_nonneg (abs_nonneg _) _)
  have ht : 0 < |τ| := abs_pos.mpr hτ
  rw [hilbertIncrementIntegrand, norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs]
  calc
    _ ≤ |τ|⁻¹ * (H * |τ| ^ γ) := mul_le_mul_of_nonneg_left hf (inv_nonneg.mpr ht.le)
    _ = _ := by rw [Real.rpow_sub_one ht.ne']; ring

theorem integrableOn_hilbertIncrementIntegrand {f : ℝ → ℂ} {θ γ H r : ℝ}
    (hf : Measurable f) (hγ : 0 < γ) (hH : 0 ≤ H) (hr : 0 ≤ r)
    (hholder : ∀ τ ∈ Icc (-r) r, ‖f (θ + τ) - f θ‖ ≤ H * |τ| ^ γ) :
    IntegrableOn (hilbertIncrementIntegrand f θ) (Icc (-r) r) := by
  refine ((integrableOn_abs_rpow_sub_one hγ hr).const_mul H).mono'
    (measurable_hilbertIncrementIntegrand hf θ).aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Icc] with τ hτ
  exact norm_hilbertIncrementIntegrand_le hH (hholder τ hτ)

theorem intervalIntegrable_hilbertIncrementIntegrand {f : ℝ → ℂ} {θ γ H a b : ℝ}
    (hf : Measurable f) (hγ : 0 < γ) (hH : 0 ≤ H)
    (hholder : ∀ τ, ‖f (θ + τ) - f θ‖ ≤ H * |τ| ^ γ) :
    IntervalIntegrable (hilbertIncrementIntegrand f θ) volume a b := by
  refine ((intervalIntegrable_abs_rpow_sub_one hγ).const_mul H).mono_fun'
    (measurable_hilbertIncrementIntegrand hf θ).aestronglyMeasurable ?_
  exact Eventually.of_forall (fun τ => norm_hilbertIncrementIntegrand_le hH (hholder τ))

theorem integral_norm_hilbertIncrementIntegrand_le {f : ℝ → ℂ} {θ γ H r : ℝ}
    (hf : Measurable f) (hγ : 0 < γ) (hH : 0 ≤ H) (hr : 0 ≤ r)
    (hholder : ∀ τ ∈ Icc (-r) r, ‖f (θ + τ) - f θ‖ ≤ H * |τ| ^ γ) :
    (∫ τ in Icc (-r) r, ‖hilbertIncrementIntegrand f θ τ‖) ≤ H * (2 * r ^ γ / γ) := by
  have hi := integrableOn_hilbertIncrementIntegrand hf hγ hH hr hholder
  calc
    _ ≤ ∫ τ in Icc (-r) r, H * |τ| ^ (γ - 1) := by
      apply integral_mono_ae hi.norm ((integrableOn_abs_rpow_sub_one hγ hr).const_mul H)
      filter_upwards [ae_restrict_mem measurableSet_Icc] with τ hτ
      exact norm_hilbertIncrementIntegrand_le hH (hholder τ hτ)
    _ = _ := by rw [integral_const_mul, integral_abs_rpow_sub_one hγ hr]

def hilbertIncrement (f : ℝ → ℂ) (θ : ℝ) : ℂ :=
  ∫ τ in Icc (-Real.pi) Real.pi, hilbertIncrementIntegrand f θ τ

theorem hilbertIncrement_eq_intervalIntegral (f : ℝ → ℂ) (θ : ℝ) :
    hilbertIncrement f θ = ∫ τ in (-Real.pi)..Real.pi, hilbertIncrementIntegrand f θ τ := by
  rw [hilbertIncrement, integral_Icc_eq_integral_Ioc,
    intervalIntegral.integral_of_le (by linarith [Real.pi_pos] : -Real.pi ≤ Real.pi)]

theorem norm_hilbertIncrement_le {f : ℝ → ℂ} {θ γ H : ℝ}
    (hf : Measurable f) (hγ : 0 < γ) (hH : 0 ≤ H)
    (hholder : ∀ τ ∈ Icc (-Real.pi) Real.pi,
      ‖f (θ + τ) - f θ‖ ≤ H * |τ| ^ γ) :
    ‖hilbertIncrement f θ‖ ≤ H * (2 * Real.pi ^ γ / γ) :=
  (norm_integral_le_integral_norm _).trans
    (integral_norm_hilbertIncrementIntegrand_le hf hγ hH Real.pi_pos.le hholder)

/-- The actual universal integral applied to a genuine Hölder loop. -/
def contourHilbertIncrement {γ : ℝ≥0} (f : ContourHolderSpace γ) (θ : ℝ) : ℂ :=
  hilbertIncrement (fun t : ℝ => f (t : ContourCircle)) θ

theorem norm_contourHilbertIncrement_le {γ : ℝ≥0} (f : ContourHolderSpace γ)
    (hγ : 0 < (γ : ℝ)) (θ : ℝ) :
    ‖contourHilbertIncrement f θ‖ ≤ ‖f‖ * (2 * Real.pi ^ (γ : ℝ) / (γ : ℝ)) := by
  exact norm_hilbertIncrement_le
    (((HolderFunctionSpace.toBCF γ f).continuous.comp
      (AddCircle.continuous_mk' (2 * Real.pi))).measurable)
    hγ (norm_nonneg f) (fun τ _ => norm_contourHolder_lift_sub_le f θ τ)

end Euler2D

end
