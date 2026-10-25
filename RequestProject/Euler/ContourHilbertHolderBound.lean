module

public import RequestProject.Euler.ContourHilbertDifferenceBound
public import RequestProject.Euler.ContourHilbertConstants

/-! # The actual universal Hilbert increment preserves the Hölder exponent -/

@[expose] public section

noncomputable section

open Set MeasureTheory Filter Topology Real
open scoped NNReal Interval

namespace Euler2D

theorem norm_hilbertIncrement_add_sub_le {f : ℝ → ℂ} {γ N θ h : ℝ}
    (hf : Measurable f) (hγ : 0 < γ) (hγ1 : γ < 1) (hN : 0 ≤ N) (hh : 0 ≤ h)
    (hholder : ∀ θ τ, ‖f (θ + τ) - f θ‖ ≤ N * |τ| ^ γ)
    (hM : ∀ t, ‖f t‖ ≤ N) :
    ‖hilbertIncrement f (θ + h) - hilbertIncrement f θ‖ ≤
      hilbertHolderConstant γ * N * h ^ γ := by
  by_cases hz : h = 0
  · simp [hz, Real.zero_rpow hγ.ne']
  have hhpos : 0 < h := lt_of_le_of_ne hh (Ne.symm hz)
  by_cases hsmall : h ≤ Real.pi / 4
  · have hb := norm_hilbertIncrement_sub_small_le (θ := θ) hf hγ hγ1 hhpos hsmall hN hN hholder hM
    have hn := hb.trans (hilbert_small_bound_normalize hγ hγ1 hhpos hsmall hN)
    have hc : hilbertSmallConstant γ ≤ hilbertHolderConstant γ := by
      unfold hilbertHolderConstant
      linarith [hilbertLargeConstant_nonneg hγ]
    exact hn.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc hN)
      (Real.rpow_nonneg hh γ))
  · have hleft := norm_hilbertIncrement_le hf hγ hN (θ := θ + h)
      (fun τ _ => hholder (θ + h) τ)
    have hright := norm_hilbertIncrement_le hf hγ hN (θ := θ)
      (fun τ _ => hholder θ τ)
    have hb : ‖hilbertIncrement f (θ + h) - hilbertIncrement f θ‖ ≤
        4 * N * Real.pi ^ γ / γ :=
      (norm_sub_le _ _).trans ((add_le_add hleft hright).trans_eq (by ring))
    have hn := hb.trans (hilbert_large_bound_normalize hγ (le_of_not_ge hsmall) hN)
    have hc : hilbertLargeConstant γ ≤ hilbertHolderConstant γ := by
      unfold hilbertHolderConstant
      linarith [hilbertSmallConstant_nonneg hγ hγ1]
    exact hn.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc hN)
      (Real.rpow_nonneg hh γ))

/-- The final real-parameter Hölder estimate, derived from the actual
near/far split and the exact two-sided constant cancellation. -/
theorem norm_hilbertIncrement_sub_le {f : ℝ → ℂ} {γ N : ℝ}
    (hf : Measurable f) (hγ : 0 < γ) (hγ1 : γ < 1) (hN : 0 ≤ N)
    (hholder : ∀ θ τ, ‖f (θ + τ) - f θ‖ ≤ N * |τ| ^ γ)
    (hM : ∀ t, ‖f t‖ ≤ N) (θ φ : ℝ) :
    ‖hilbertIncrement f θ - hilbertIncrement f φ‖ ≤
      hilbertHolderConstant γ * N * |θ - φ| ^ γ := by
  rcases le_total θ φ with hle | hle
  · have hb := norm_hilbertIncrement_add_sub_le hf hγ hγ1 hN
      (sub_nonneg.mpr hle) hholder hM (θ := θ) (h := φ - θ)
    rw [show θ + (φ - θ) = φ by ring] at hb
    have hgap : |θ - φ| = φ - θ := by
      rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hle)]
    rw [hgap, norm_sub_rev]
    exact hb
  · have hb := norm_hilbertIncrement_add_sub_le hf hγ hγ1 hN
      (sub_nonneg.mpr hle) hholder hM (θ := φ) (h := θ - φ)
    rw [show φ + (θ - φ) = θ by ring] at hb
    rwa [abs_of_nonneg (sub_nonneg.mpr hle)]

/-- The genuine Hölder density supplies all hypotheses of the universal
estimate through its actual graph norm and actual quotient metric. -/
theorem norm_contourHilbertIncrement_sub_le {γ : ℝ≥0} (f : ContourHolderSpace γ)
    (hγ : 0 < (γ : ℝ)) (hγ1 : (γ : ℝ) < 1) (θ φ : ℝ) :
    ‖contourHilbertIncrement f θ - contourHilbertIncrement f φ‖ ≤
      hilbertHolderConstant (γ : ℝ) * ‖f‖ * |θ - φ| ^ (γ : ℝ) := by
  exact norm_hilbertIncrement_sub_le
    (((HolderFunctionSpace.toBCF γ f).continuous.comp
      (AddCircle.continuous_mk' (2 * Real.pi))).measurable)
    hγ hγ1 (norm_nonneg f) (norm_contourHolder_lift_sub_le f)
    (fun t => HolderFunctionSpace.norm_eval_le f (t : ContourCircle)) θ φ

end Euler2D

end
