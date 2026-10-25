module

public import RequestProject.Euler.ContourCauchyIncrement
public import RequestProject.Euler.ContourHolderAlgebra

/-! Genuine quotient-circle density increments and their two Hölder bounds. -/

@[expose] public section

noncomputable section

open Set Filter Topology
open scoped NNReal

namespace Euler2D

def contourDensityIncrement {γ : ℝ≥0} (f : ContourHolderSpace γ)
    (x : ContourCircle) (τ : ℝ) : ℂ := f (x + (τ : ContourCircle)) - f x

theorem norm_contourDensityIncrement_le {γ : ℝ≥0} (f : ContourHolderSpace γ)
    (x : ContourCircle) (τ : ℝ) :
    ‖contourDensityIncrement f x τ‖ ≤ ‖f‖ * |τ| ^ (γ : ℝ) := by
  obtain ⟨θ, rfl⟩ := QuotientAddGroup.mk_surjective x
  exact norm_contourHolder_lift_sub_le f θ τ

theorem norm_contourDensityIncrement_parameter_sub_le {γ : ℝ≥0} (f : ContourHolderSpace γ)
    (x y : ContourCircle) (τ : ℝ) :
    ‖contourDensityIncrement f x τ - contourDensityIncrement f y τ‖ ≤
      2 * ‖f‖ * dist x y ^ (γ : ℝ) := by
  have he : contourDensityIncrement f x τ - contourDensityIncrement f y τ =
      (f (x + (τ : ContourCircle)) - f (y + (τ : ContourCircle))) - (f x - f y) := by
    dsimp only [contourDensityIncrement]
    ring
  rw [he]
  calc
    _ ≤ ‖f (x + (τ : ContourCircle)) - f (y + (τ : ContourCircle))‖ + ‖f x - f y‖ := norm_sub_le _ _
    _ ≤ ‖f‖ * dist x y ^ (γ : ℝ) + ‖f‖ * dist x y ^ (γ : ℝ) := by
      apply add_le_add
      · simpa only [dist_add_right] using HolderFunctionSpace.norm_sub_le_holder f
          (x + (τ : ContourCircle)) (y + (τ : ContourCircle))
      · exact HolderFunctionSpace.norm_sub_le_holder f x y
    _ = _ := by ring

theorem continuous_contourDensityIncrement {γ : ℝ≥0} (f : ContourHolderSpace γ) :
    Continuous (fun p : ContourCircle × ℝ => contourDensityIncrement f p.1 p.2) := by
  have hs : Continuous (fun p : ContourCircle × ℝ => p.1 + (p.2 : ContourCircle)) :=
    continuous_fst.add ((AddCircle.continuous_mk' (2 * Real.pi)).comp continuous_snd)
  exact ((HolderFunctionSpace.toBCF γ f).continuous.comp hs).sub
    ((HolderFunctionSpace.toBCF γ f).continuous.comp continuous_fst)

end Euler2D

end
