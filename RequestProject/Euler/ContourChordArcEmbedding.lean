module

public import RequestProject.Euler.ContourAdmissibility

/-! # Actual quotient-circle geometry of a positive chord bound -/

@[expose] public section

noncomputable section

open Complex Set Filter Topology Metric Real
open scoped NNReal

namespace Euler2D
namespace ContourC1Space

variable {γ : ℝ≥0}

theorem chordArc_lower (f : ContourC1Space γ) {c : ℝ} (hf : HasChordArcLower f c)
    (x y : ContourCircle) : c * dist x y ≤ ‖toBCF γ f x - toBCF γ f y‖ := by
  obtain ⟨θ, φ, hθ, hφ, hangle, hdist⟩ := exists_short_contour_representatives x y
  have hb := hf θ (φ - θ) (by rwa [abs_sub_comm])
  rw [show θ + (φ - θ) = φ by ring, abs_sub_comm] at hb
  change c * |θ - φ| ≤ ‖toBCF γ f (θ : ContourCircle) - toBCF γ f (φ : ContourCircle)‖ at hb
  rw [hθ, hφ] at hb
  rwa [hdist]

theorem injective_of_positiveChordArc (f : ContourC1Space γ) (hf : HasPositiveChordArc f) :
    Function.Injective (toBCF γ f) := by
  obtain ⟨c, hc, hfc⟩ := hf
  intro x y hxy
  have hb := chordArc_lower f hfc x y
  rw [hxy, sub_self, norm_zero] at hb
  have hd : dist x y ≤ 0 := (mul_le_mul_iff_right₀ hc).mp
    (by simpa only [mul_zero] using hb)
  exact dist_le_zero.mp hd

theorem isClosedEmbedding_of_positiveChordArc (f : ContourC1Space γ)
    (hf : HasPositiveChordArc f) : IsClosedEmbedding (toBCF γ f) :=
  (toBCF γ f).continuous.isClosedEmbedding (injective_of_positiveChordArc f hf)

end ContourC1Space
end Euler2D

end
