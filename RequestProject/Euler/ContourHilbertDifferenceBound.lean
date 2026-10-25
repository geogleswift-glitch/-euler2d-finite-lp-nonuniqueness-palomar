module

public import RequestProject.Euler.ContourHilbertDifferenceIdentity
public import RequestProject.Euler.ContourHilbertFar
public import RequestProject.Euler.ContourHilbertBoundary

/-! # Assembly of the genuine near/far Hilbert difference estimate -/

@[expose] public section

noncomputable section

open Set MeasureTheory Filter Topology Real
open scoped Interval

namespace Euler2D

theorem intervalIntegrable_hilbertFarDifferenceIntegrand
    {f : ℝ → ℂ} {θ h a b γ H : ℝ}
    (hf : Measurable f) (hh : 0 < h) (hH : 0 ≤ H) (hab : a ≤ b)
    (hfar : ∀ s ∈ Icc a b, 2 * h ≤ |s|)
    (hholder : ∀ s, ‖f (θ + s) - f θ‖ ≤ H * |s| ^ γ) :
    IntervalIntegrable (hilbertFarDifferenceIntegrand f θ h) volume a b := by
  have hp := intervalIntegrable_abs_rpow_of_away_zero (r := γ - 2)
    (by positivity : 0 < 2 * h) hab hfar
  apply (hp.const_mul (2 * h * H)).mono_fun'
    (measurable_hilbertFarDifferenceIntegrand hf θ h).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_uIoc] with s hs
  rw [uIoc_of_le hab] at hs
  exact norm_hilbertFarDifferenceIntegrand_le hh hH
    (hfar s ⟨hs.1.le, hs.2⟩) (hholder s)

theorem hilbert_common_interval_difference
    {f : ℝ → ℂ} {θ h a b γ H : ℝ}
    (hf : Measurable f) (hγ : 0 < γ) (hh : 0 < h) (hH : 0 ≤ H) (hab : a ≤ b)
    (hfar : ∀ s ∈ Icc a b, 2 * h ≤ |s|)
    (hholder : ∀ θ τ, ‖f (θ + τ) - f θ‖ ≤ H * |τ| ^ γ) :
    (∫ s in a..b, translatedHilbertIncrementIntegrand f θ h s -
        hilbertIncrementIntegrand f θ s) =
      (∫ s in a..b, hilbertFarDifferenceIntegrand f θ h s) -
        (∫ s in a..b, ((s - h : ℝ) : ℂ)⁻¹ * (f (θ + h) - f θ)) := by
  have hF : IntervalIntegrable (hilbertIncrementIntegrand f θ) volume a b :=
    intervalIntegrable_hilbertIncrementIntegrand hf hγ hH (hholder θ)
  have hG : IntervalIntegrable (translatedHilbertIncrementIntegrand f θ h) volume a b :=
    intervalIntegrable_translatedHilbertIncrementIntegrand hf hγ hH hholder θ h a b
  have hK := intervalIntegrable_hilbertFarDifferenceIntegrand hf hh hH hab hfar (hholder θ)
  have hC : IntervalIntegrable
      (fun s : ℝ => ((s - h : ℝ) : ℂ)⁻¹ * (f (θ + h) - f θ)) volume a b := by
    apply (hK.sub (hG.sub hF)).congr_ae
    exact Eventually.of_forall (fun s => by
      dsimp only [Pi.sub_apply]
      rw [translatedHilbertIncrementIntegrand_sub]
      unfold hilbertFarDifferenceIntegrand
      ring)
  calc
    _ = ∫ s in a..b, hilbertFarDifferenceIntegrand f θ h s -
        ((s - h : ℝ) : ℂ)⁻¹ * (f (θ + h) - f θ) := by
      apply intervalIntegral.integral_congr
      intro s _
      exact translatedHilbertIncrementIntegrand_sub f θ h s
    _ = _ := intervalIntegral.integral_sub hK hC

theorem norm_hilbert_common_difference_le {f : ℝ → ℂ} {θ h P γ H : ℝ}
    (hf : Measurable f) (hγ : 0 < γ) (hγ1 : γ < 1) (hP : 0 < P) (hh : 0 < h)
    (hsmall : h ≤ P / 4) (hH : 0 ≤ H)
    (hholder : ∀ θ τ, ‖f (θ + τ) - f θ‖ ≤ H * |τ| ^ γ) :
    ‖(∫ s in (h - P)..(-2 * h), translatedHilbertIncrementIntegrand f θ h s -
        hilbertIncrementIntegrand f θ s) +
      (∫ s in (2 * h)..P, translatedHilbertIncrementIntegrand f θ h s -
        hilbertIncrementIntegrand f θ s)‖ ≤
      (4 * h * H) * ((2 * h) ^ (γ - 1) / (1 - γ)) + Real.log 3 * (H * h ^ γ) := by
  rw [hilbert_common_interval_difference hf hγ hh hH (a := h - P) (b := -2 * h) (by linarith) (by
      intro s hs
      linarith [hs.2, neg_le_abs s]) hholder,
    hilbert_common_interval_difference hf hγ hh hH (a := 2 * h) (b := P) (by linarith) (by
      intro s hs
      linarith [hs.1, le_abs_self s]) hholder]
  have he :
      ((∫ s in (h - P)..(-2 * h), hilbertFarDifferenceIntegrand f θ h s) -
          (∫ s in (h - P)..(-2 * h), ((s - h : ℝ) : ℂ)⁻¹ * (f (θ + h) - f θ))) +
      ((∫ s in (2 * h)..P, hilbertFarDifferenceIntegrand f θ h s) -
          (∫ s in (2 * h)..P, ((s - h : ℝ) : ℂ)⁻¹ * (f (θ + h) - f θ))) =
      ((∫ s in (h - P)..(-2 * h), hilbertFarDifferenceIntegrand f θ h s) +
          (∫ s in (2 * h)..P, hilbertFarDifferenceIntegrand f θ h s)) -
      ((∫ s in (h - P)..(-2 * h), ((s - h : ℝ) : ℂ)⁻¹ * (f (θ + h) - f θ)) +
          (∫ s in (2 * h)..P, ((s - h : ℝ) : ℂ)⁻¹ * (f (θ + h) - f θ))) := by abel
  rw [he]
  apply (norm_sub_le _ _).trans
  apply add_le_add
  · exact norm_hilbert_common_far_difference_le hf hγ1 hP hh hsmall hH (hholder θ)
  · apply (norm_hilbert_common_far_constant_le (f (θ + h) - f θ) hP hh hsmall).trans
    apply mul_le_mul_of_nonneg_left _ (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 3))
    simpa only [abs_of_pos hh] using hholder θ h

/-- The complete small-translation bound, obtained from the four literal
integral pieces.  The Hölder conclusion is not an input. -/
theorem norm_hilbertIncrement_sub_small_le {f : ℝ → ℂ} {θ h γ H M : ℝ}
    (hf : Measurable f) (hγ : 0 < γ) (hγ1 : γ < 1) (hh : 0 < h)
    (hsmall : h ≤ Real.pi / 4) (hH : 0 ≤ H) (hM0 : 0 ≤ M)
    (hholder : ∀ θ τ, ‖f (θ + τ) - f θ‖ ≤ H * |τ| ^ γ)
    (hM : ∀ t, ‖f t‖ ≤ M) :
    ‖hilbertIncrement f (θ + h) - hilbertIncrement f θ‖ ≤
      H * (4 * (3 * h) ^ γ / γ) +
      ((4 * h * H) * ((2 * h) ^ (γ - 1) / (1 - γ)) + Real.log 3 * (H * h ^ γ)) +
      (8 * M / Real.pi) * h := by
  rw [hilbertIncrement_difference_split hf hγ hH hholder θ h]
  refine norm_add₃_le.trans ?_
  apply add_le_add
  · apply add_le_add
    · apply (norm_sub_le _ _).trans
      have hnear := norm_translated_hilbert_near_integral_le hf hγ hH hh (hholder (θ + h))
      have hbase := norm_hilbert_near_integral_le hf hγ hH hh (hholder θ)
      exact (add_le_add hnear hbase).trans_eq (by ring)
    · exact norm_hilbert_common_difference_le hf hγ hγ1 Real.pi_pos hh hsmall hH hholder
  · exact norm_hilbert_endpoint_difference_le Real.pi_pos hh hsmall hM0 hM

end Euler2D

end
