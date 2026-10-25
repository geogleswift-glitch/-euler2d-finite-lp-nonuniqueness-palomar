module

public import RequestProject.Euler.ContourHilbertEstimates

/-! # Actual translation and near-region estimates for the Hilbert increment -/

@[expose] public section

noncomputable section

open Set MeasureTheory Filter Topology Real
open scoped NNReal Interval

namespace Euler2D

def translatedHilbertIncrementIntegrand (f : ℝ → ℂ) (θ h s : ℝ) : ℂ :=
  ((s - h : ℝ) : ℂ)⁻¹ * (f (θ + s) - f (θ + h))

theorem translatedHilbertIncrementIntegrand_eq (f : ℝ → ℂ) (θ h s : ℝ) :
    translatedHilbertIncrementIntegrand f θ h s =
      hilbertIncrementIntegrand f (θ + h) (s - h) := by
  unfold translatedHilbertIncrementIntegrand hilbertIncrementIntegrand
  rw [show θ + h + (s - h) = θ + s by ring]

theorem hilbertIncrement_translate (f : ℝ → ℂ) (θ h : ℝ) :
    hilbertIncrement f (θ + h) =
      ∫ s in (h - Real.pi)..(h + Real.pi), translatedHilbertIncrementIntegrand f θ h s := by
  rw [hilbertIncrement_eq_intervalIntegral]
  simp_rw [translatedHilbertIncrementIntegrand_eq]
  rw [intervalIntegral.integral_comp_sub_right,
    show h - Real.pi - h = -Real.pi by ring,
    show h + Real.pi - h = Real.pi by ring]

/-- The exact far algebra after translating the moving singularity. -/
theorem translatedHilbertIncrementIntegrand_sub (f : ℝ → ℂ) (θ h s : ℝ) :
    translatedHilbertIncrementIntegrand f θ h s - hilbertIncrementIntegrand f θ s =
      ((((s - h : ℝ) : ℂ)⁻¹ - (s : ℂ)⁻¹) * (f (θ + s) - f θ)) -
        ((s - h : ℝ) : ℂ)⁻¹ * (f (θ + h) - f θ) := by
  unfold translatedHilbertIncrementIntegrand hilbertIncrementIntegrand
  ring

theorem norm_intervalIntegral_hilbertIncrementIntegrand_le
    {f : ℝ → ℂ} {θ γ H a b r : ℝ}
    (hf : Measurable f) (hγ : 0 < γ) (hH : 0 ≤ H) (hr : 0 ≤ r)
    (hholder : ∀ τ, ‖f (θ + τ) - f θ‖ ≤ H * |τ| ^ γ)
    (ha : -r ≤ a) (hab : a ≤ b) (hb : b ≤ r) :
    ‖∫ τ in a..b, hilbertIncrementIntegrand f θ τ‖ ≤ H * (2 * r ^ γ / γ) := by
  have hi : IntervalIntegrable (hilbertIncrementIntegrand f θ) volume (-r) r :=
    intervalIntegrable_hilbertIncrementIntegrand hf hγ hH hholder
  calc
    _ ≤ ∫ τ in a..b, ‖hilbertIncrementIntegrand f θ τ‖ :=
      intervalIntegral.norm_integral_le_integral_norm hab
    _ ≤ ∫ τ in (-r)..r, ‖hilbertIncrementIntegrand f θ τ‖ :=
      intervalIntegral.integral_mono_interval ha hab hb
        (Eventually.of_forall (fun _ => norm_nonneg _)) hi.norm
    _ ≤ _ := by
      rw [intervalIntegral.integral_of_le (by linarith : -r ≤ r),
        ← integral_Icc_eq_integral_Ioc]
      exact integral_norm_hilbertIncrementIntegrand_le hf hγ hH hr (fun τ _ => hholder τ)

theorem norm_hilbert_near_integral_le {f : ℝ → ℂ} {θ γ H h : ℝ}
    (hf : Measurable f) (hγ : 0 < γ) (hH : 0 ≤ H) (hh : 0 < h)
    (hholder : ∀ τ, ‖f (θ + τ) - f θ‖ ≤ H * |τ| ^ γ) :
    ‖∫ s in (-2 * h)..(2 * h), hilbertIncrementIntegrand f θ s‖ ≤
      H * (2 * (3 * h) ^ γ / γ) :=
  norm_intervalIntegral_hilbertIncrementIntegrand_le hf hγ hH (by positivity)
    hholder (by linarith) (by linarith) (by linarith)

theorem norm_translated_hilbert_near_integral_le {f : ℝ → ℂ} {θ γ H h : ℝ}
    (hf : Measurable f) (hγ : 0 < γ) (hH : 0 ≤ H) (hh : 0 < h)
    (hholder : ∀ τ, ‖f (θ + h + τ) - f (θ + h)‖ ≤ H * |τ| ^ γ) :
    ‖∫ s in (-2 * h)..(2 * h), translatedHilbertIncrementIntegrand f θ h s‖ ≤
      H * (2 * (3 * h) ^ γ / γ) := by
  simp_rw [translatedHilbertIncrementIntegrand_eq]
  rw [intervalIntegral.integral_comp_sub_right,
    show -2 * h - h = -3 * h by ring, show 2 * h - h = h by ring]
  exact norm_intervalIntegral_hilbertIncrementIntegrand_le hf hγ hH (by positivity)
    hholder (by ring_nf; rfl) (by linarith) (by linarith)

end Euler2D

end
