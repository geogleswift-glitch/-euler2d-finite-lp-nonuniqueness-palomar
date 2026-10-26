module

public import RequestProject.Euler.TorusForcedFinitePhaseFlow

/-! Every actual quarter-phase material contour stays away from the
centre, independently of the phase used to describe the same curve. -/

@[expose] public section

noncomputable section

open Set Complex
open scoped NNReal

namespace Euler2D

theorem quarterPhase_target_radius_lower {γ : ℝ≥0} {ι : Type*}
    (Z₀ : ι → ContourC1Space γ) (r : ι → ℝ) (hr : ∀ i, 0 < r i)
    (href : ∀ i, ContourC1Space.lift γ (Z₀ i) = refCircle (r i))
    {Z : ι → LittleContourSpace γ} (hZ : IsQuarterPhaseLittleContourFamily Z₀ r Z) :
    ∀ i x, r i / 2 ≤ ‖ContourC1Space.toBCF γ (Z i).val x‖ := by
  obtain ⟨b, hb⟩ := hZ
  intro i x
  obtain ⟨θ, rfl⟩ := QuotientAddGroup.mk_surjective x
  have hh := (contourC1_norm_sub_ref_le (contourParameterShiftC1 (b i) (Z i).val)
    (Z₀ i) (href i) (θ - b i)).trans (hb i).le
  have hdif : ‖LittleContourSpace.lift γ (Z i) θ - refCircle (r i) (θ - b i)‖ ≤ r i / 4 := by
    simp only [lift_contourParameterShiftC1, sub_add_cancel] at hh
    change ‖ContourC1Space.lift γ (Z i).val θ - refCircle (r i) (θ - b i)‖ ≤ r i / 4
    exact hh
  have hn := norm_sub_norm_le (refCircle (r i) (θ - b i)) (LittleContourSpace.lift γ (Z i) θ)
  rw [norm_refCircle_actual, abs_of_pos (hr i), norm_sub_rev] at hn
  change r i / 2 ≤ ‖LittleContourSpace.lift γ (Z i) θ‖
  linarith [hr i]

end Euler2D

end
