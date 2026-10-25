module

public import RequestProject.Euler.ContourHilbertNearFar

/-! # Genuine far-region integral bounds for the universal Hilbert kernel -/

@[expose] public section

noncomputable section

open Set MeasureTheory Filter Topology Real
open scoped NNReal Interval

namespace Euler2D

theorem intervalIntegrable_abs_rpow_of_away_zero {a b r δ : ℝ}
    (hδ : 0 < δ) (hab : a ≤ b) (hfar : ∀ s ∈ Icc a b, δ ≤ |s|) :
    IntervalIntegrable (fun s : ℝ => |s| ^ r) volume a b := by
  apply (continuous_abs.continuousOn.rpow_const ?_).intervalIntegrable
  intro s hs
  rw [uIcc_of_le hab] at hs
  exact Or.inl (ne_of_gt (hδ.trans_le (hfar s hs)))

theorem integral_positive_far_abs_rpow_le {γ P h : ℝ}
    (hγ : γ < 1) (hh : 0 < h) (hbound : 2 * h ≤ P) :
    (∫ s in (2 * h)..P, |s| ^ (γ - 2)) ≤ (2 * h) ^ (γ - 1) / (1 - γ) := by
  have he : (∫ s in (2 * h)..P, |s| ^ (γ - 2)) =
      ∫ s in (2 * h)..P, s ^ (γ - 2) := by
    apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_le hbound] at hs
    dsimp only
    rw [abs_of_nonneg (by linarith [hs.1])]
  rw [he]
  exact integral_far_rpow_le hγ (by positivity) hbound

theorem integral_negative_far_abs_rpow_le {γ P h : ℝ}
    (hγ : γ < 1) (hh : 0 < h) (hbound : 3 * h ≤ P) :
    (∫ s in (h - P)..(-2 * h), |s| ^ (γ - 2)) ≤
      (2 * h) ^ (γ - 1) / (1 - γ) := by
  have he : (∫ s in (h - P)..(-2 * h), |s| ^ (γ - 2)) =
      ∫ s in (2 * h)..(P - h), |s| ^ (γ - 2) := by
    have ht := intervalIntegral.integral_comp_neg
      (f := fun s : ℝ => |s| ^ (γ - 2)) (a := h - P) (b := -2 * h)
    simpa only [abs_neg, neg_sub, neg_mul, neg_neg] using ht
  rw [he]
  exact integral_positive_far_abs_rpow_le hγ hh (by linarith)

def hilbertFarDifferenceIntegrand (f : ℝ → ℂ) (θ h s : ℝ) : ℂ :=
  ((((s - h : ℝ) : ℂ)⁻¹ - (s : ℂ)⁻¹) * (f (θ + s) - f θ))

theorem measurable_hilbertFarDifferenceIntegrand {f : ℝ → ℂ}
    (hf : Measurable f) (θ h : ℝ) : Measurable (hilbertFarDifferenceIntegrand f θ h) :=
  (((Complex.measurable_ofReal.comp (measurable_id.sub measurable_const)).inv).sub
    ((Complex.measurable_ofReal.comp measurable_id).inv)).mul
      ((hf.comp (measurable_const.add measurable_id)).sub measurable_const)

theorem norm_hilbertFarDifferenceIntegrand_le {f : ℝ → ℂ} {θ h s γ H : ℝ}
    (hh : 0 < h) (_hH : 0 ≤ H) (hfar : 2 * h ≤ |s|)
    (hholder : ‖f (θ + s) - f θ‖ ≤ H * |s| ^ γ) :
    ‖hilbertFarDifferenceIntegrand f θ h s‖ ≤ (2 * h * H) * |s| ^ (γ - 2) := by
  have hs : 0 < |s| := by linarith
  have he : ‖((s - h : ℝ) : ℂ)⁻¹ - (s : ℂ)⁻¹‖ = |(s - h)⁻¹ - s⁻¹| := by
    rw [← Complex.ofReal_inv, ← Complex.ofReal_inv, ← Complex.ofReal_sub,
      Complex.norm_real, Real.norm_eq_abs]
  rw [hilbertFarDifferenceIntegrand, norm_mul, he]
  calc
    _ ≤ (2 * h / |s| ^ 2) * (H * |s| ^ γ) :=
      mul_le_mul (abs_reciprocal_translation_sub_le hh hfar) hholder
        (norm_nonneg _) (by positivity)
    _ = _ := by rw [Real.rpow_sub hs γ 2, Real.rpow_two]; ring

theorem norm_intervalIntegral_hilbertFarDifferenceIntegrand_le
    {f : ℝ → ℂ} {θ h a b γ H : ℝ}
    (hf : Measurable f) (hh : 0 < h) (hH : 0 ≤ H) (hab : a ≤ b)
    (hfar : ∀ s ∈ Icc a b, 2 * h ≤ |s|)
    (hholder : ∀ s, ‖f (θ + s) - f θ‖ ≤ H * |s| ^ γ) :
    ‖∫ s in a..b, hilbertFarDifferenceIntegrand f θ h s‖ ≤
      (2 * h * H) * (∫ s in a..b, |s| ^ (γ - 2)) := by
  have hp := intervalIntegrable_abs_rpow_of_away_zero (r := γ - 2)
    (by positivity : 0 < 2 * h) hab hfar
  have hi : IntervalIntegrable (hilbertFarDifferenceIntegrand f θ h) volume a b := by
    apply (hp.const_mul (2 * h * H)).mono_fun'
      (measurable_hilbertFarDifferenceIntegrand hf θ h).aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_uIoc] with s hs
    rw [uIoc_of_le hab] at hs
    exact norm_hilbertFarDifferenceIntegrand_le hh hH
      (hfar s ⟨hs.1.le, hs.2⟩) (hholder s)
  calc
    _ ≤ ∫ s in a..b, ‖hilbertFarDifferenceIntegrand f θ h s‖ :=
      intervalIntegral.norm_integral_le_integral_norm hab
    _ ≤ ∫ s in a..b, (2 * h * H) * |s| ^ (γ - 2) :=
      intervalIntegral.integral_mono_on hab hi.norm (hp.const_mul _) (fun s hs =>
        norm_hilbertFarDifferenceIntegrand_le hh hH (hfar s hs) (hholder s))
    _ = _ := by rw [intervalIntegral.integral_const_mul]

/-- The actual common far kernel-difference contribution has no logarithmic loss. -/
theorem norm_hilbert_common_far_difference_le {f : ℝ → ℂ} {θ h P γ H : ℝ}
    (hf : Measurable f) (hγ : γ < 1) (_hP : 0 < P) (hh : 0 < h)
    (hsmall : h ≤ P / 4) (hH : 0 ≤ H)
    (hholder : ∀ s, ‖f (θ + s) - f θ‖ ≤ H * |s| ^ γ) :
    ‖(∫ s in (h - P)..(-2 * h), hilbertFarDifferenceIntegrand f θ h s) +
        (∫ s in (2 * h)..P, hilbertFarDifferenceIntegrand f θ h s)‖ ≤
      (4 * h * H) * ((2 * h) ^ (γ - 1) / (1 - γ)) := by
  have hn := norm_intervalIntegral_hilbertFarDifferenceIntegrand_le hf hh hH
    (a := h - P) (b := -2 * h) (by linarith) (by
      intro s hs
      linarith [hs.2, neg_le_abs s]) hholder
  have hp := norm_intervalIntegral_hilbertFarDifferenceIntegrand_le hf hh hH
    (a := 2 * h) (b := P) (by linarith) (by
      intro s hs
      linarith [hs.1, le_abs_self s]) hholder
  have hn' := hn.trans (mul_le_mul_of_nonneg_left
    (integral_negative_far_abs_rpow_le hγ hh (by linarith)) (by positivity : 0 ≤ 2 * h * H))
  have hp' := hp.trans (mul_le_mul_of_nonneg_left
    (integral_positive_far_abs_rpow_le hγ hh (by linarith)) (by positivity : 0 ≤ 2 * h * H))
  calc
    _ ≤ _ := norm_add_le _ _
    _ ≤ _ := add_le_add hn' hp'
    _ = _ := by ring

end Euler2D

end
