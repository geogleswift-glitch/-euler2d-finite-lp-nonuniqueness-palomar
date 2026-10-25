module

public import RequestProject.Euler.AreaChart

/-!
# Actual Taylor bounds from a Hölder continuous derivative

These estimates are derived from the genuine one-dimensional derivative
and the mean value theorem. They retain quantitative control of the
divided differences used in the contour kernels.
-/

@[expose] public section

noncomputable section

open Set

namespace Euler2D

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem norm_holder_derivative_taylor {z dz : ℝ → E} {γ H : ℝ}
    (hγ : 0 ≤ γ) (hH : 0 ≤ H) (hz : ∀ s, HasDerivAt z (dz s) s)
    (hd : ∀ s t, ‖dz s - dz t‖ ≤ H * |s - t| ^ γ) (θ τ : ℝ) :
    ‖z (θ + τ) - z θ - τ • dz θ‖ ≤ (H * |τ| ^ γ) * |τ| := by
  let g : ℝ → E := fun s => z s - s • dz θ
  have hg (s : ℝ) : HasDerivAt g (dz s - dz θ) s := by
    simpa only [g, Pi.sub_def, id_eq, one_smul] using
      (hz s).sub ((hasDerivAt_id s).smul_const (dz θ))
  have hbound (s : ℝ) (hs : s ∈ uIcc θ (θ + τ)) :
      ‖dz s - dz θ‖ ≤ H * |τ| ^ γ := by
    have hs' : |s - θ| ≤ |τ| := by
      simpa only [add_sub_cancel_left] using abs_sub_left_of_mem_uIcc hs
    exact (hd s θ).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (abs_nonneg _) hs' hγ) hH)
  have hm := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun s (_hs : s ∈ uIcc θ (θ + τ)) => (hg s).hasDerivWithinAt)
    hbound (convex_uIcc θ (θ + τ)) left_mem_uIcc right_mem_uIcc
  have he : g (θ + τ) - g θ = z (θ + τ) - z θ - τ • dz θ := by
    dsimp only [g]
    rw [add_smul]
    abel
  simpa only [he, add_sub_cancel_left, Real.norm_eq_abs] using hm

theorem norm_dividedDifference_sub_derivative {z dz : ℝ → E} {γ H : ℝ}
    (hγ : 0 ≤ γ) (hH : 0 ≤ H) (hz : ∀ s, HasDerivAt z (dz s) s)
    (hd : ∀ s t, ‖dz s - dz t‖ ≤ H * |s - t| ^ γ)
    (θ : ℝ) {τ : ℝ} (hτ : τ ≠ 0) :
    ‖τ⁻¹ • (z (θ + τ) - z θ) - dz θ‖ ≤ H * |τ| ^ γ := by
  have ht := norm_holder_derivative_taylor hγ hH hz hd θ τ
  have he : τ⁻¹ • (z (θ + τ) - z θ - τ • dz θ) =
      τ⁻¹ • (z (θ + τ) - z θ) - dz θ := by
    rw [smul_sub, smul_smul, inv_mul_cancel₀ hτ, one_smul]
  calc
    _ = |τ|⁻¹ * ‖z (θ + τ) - z θ - τ • dz θ‖ := by
      rw [← he, norm_smul, Real.norm_eq_abs, abs_inv]
    _ ≤ |τ|⁻¹ * ((H * |τ| ^ γ) * |τ|) :=
      mul_le_mul_of_nonneg_left ht (inv_nonneg.mpr (abs_nonneg _))
    _ = H * |τ| ^ γ := by
      field_simp

end Euler2D

end
