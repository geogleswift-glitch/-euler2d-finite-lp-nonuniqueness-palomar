module

public import RequestProject.Euler.ContourHilbertNearFar

/-! # Exact near/far decomposition of the real-translation difference -/

@[expose] public section

noncomputable section

open Set MeasureTheory Filter Topology Real
open scoped Interval

namespace Euler2D

/-- A literal four-piece interval decomposition.  In particular, no
singular-integral estimate is hidden in this identity. -/
theorem intervalIntegral_difference_four_piece (F G : ℝ → ℂ)
    (hF : ∀ a b, IntervalIntegrable F volume a b)
    (hG : ∀ a b, IntervalIntegrable G volume a b) (a b c d e ℓ : ℝ) :
    (∫ s in b..ℓ, G s) - (∫ s in a..e, F s) =
      ((∫ s in c..d, G s) - (∫ s in c..d, F s)) +
      ((∫ s in b..c, G s - F s) + (∫ s in d..e, G s - F s)) +
      ((∫ s in e..ℓ, G s) - (∫ s in a..b, F s)) := by
  have heF : (∫ s in a..e, F s) = (∫ s in a..b, F s) +
      (∫ s in b..c, F s) + (∫ s in c..d, F s) + (∫ s in d..e, F s) := by
    rw [← intervalIntegral.integral_add_adjacent_intervals (hF a b) (hF b e),
      ← intervalIntegral.integral_add_adjacent_intervals (hF b c) (hF c e),
      ← intervalIntegral.integral_add_adjacent_intervals (hF c d) (hF d e)]
    abel
  have heG : (∫ s in b..ℓ, G s) = (∫ s in b..c, G s) +
      (∫ s in c..d, G s) + (∫ s in d..e, G s) + (∫ s in e..ℓ, G s) := by
    rw [← intervalIntegral.integral_add_adjacent_intervals (hG b c) (hG c ℓ),
      ← intervalIntegral.integral_add_adjacent_intervals (hG c d) (hG d ℓ),
      ← intervalIntegral.integral_add_adjacent_intervals (hG d e) (hG e ℓ)]
    abel
  rw [heF, heG, intervalIntegral.integral_sub (hG b c) (hF b c),
    intervalIntegral.integral_sub (hG d e) (hF d e)]
  abel

theorem intervalIntegrable_translatedHilbertIncrementIntegrand
    {f : ℝ → ℂ} {γ H : ℝ} (hf : Measurable f) (hγ : 0 < γ) (hH : 0 ≤ H)
    (hholder : ∀ θ τ, ‖f (θ + τ) - f θ‖ ≤ H * |τ| ^ γ) (θ h a b : ℝ) :
    IntervalIntegrable (translatedHilbertIncrementIntegrand f θ h) volume a b := by
  have ht := (intervalIntegrable_hilbertIncrementIntegrand hf hγ hH
    (hholder (θ + h)) (a := a - h) (b := b - h)).comp_sub_right h
  have he : (fun s : ℝ => hilbertIncrementIntegrand f (θ + h) (s - h)) =
      translatedHilbertIncrementIntegrand f θ h :=
    funext (fun s => (translatedHilbertIncrementIntegrand_eq f θ h s).symm)
  rw [he] at ht
  simpa only [sub_add_cancel] using ht

/-- The full actual Hilbert translation difference, with both moving
singularities in the same near interval and the two endpoint strips exposed. -/
theorem hilbertIncrement_difference_split {f : ℝ → ℂ} {γ H : ℝ}
    (hf : Measurable f) (hγ : 0 < γ) (hH : 0 ≤ H)
    (hholder : ∀ θ τ, ‖f (θ + τ) - f θ‖ ≤ H * |τ| ^ γ) (θ h : ℝ) :
    hilbertIncrement f (θ + h) - hilbertIncrement f θ =
      ((∫ s in (-2 * h)..(2 * h), translatedHilbertIncrementIntegrand f θ h s) -
        (∫ s in (-2 * h)..(2 * h), hilbertIncrementIntegrand f θ s)) +
      ((∫ s in (h - Real.pi)..(-2 * h),
          translatedHilbertIncrementIntegrand f θ h s - hilbertIncrementIntegrand f θ s) +
        (∫ s in (2 * h)..Real.pi,
          translatedHilbertIncrementIntegrand f θ h s - hilbertIncrementIntegrand f θ s)) +
      ((∫ s in Real.pi..(Real.pi + h), translatedHilbertIncrementIntegrand f θ h s) -
        (∫ s in (-Real.pi)..(h - Real.pi), hilbertIncrementIntegrand f θ s)) := by
  rw [hilbertIncrement_translate, hilbertIncrement_eq_intervalIntegral]
  rw [show h + Real.pi = Real.pi + h by ring]
  exact intervalIntegral_difference_four_piece (hilbertIncrementIntegrand f θ)
    (translatedHilbertIncrementIntegrand f θ h)
    (fun a b => intervalIntegrable_hilbertIncrementIntegrand hf hγ hH (hholder θ))
    (intervalIntegrable_translatedHilbertIncrementIntegrand hf hγ hH hholder θ h)
    (-Real.pi) (h - Real.pi) (-2 * h) (2 * h) Real.pi (Real.pi + h)

end Euler2D

end
