module

public import RequestProject.Euler.ContourComplexHolderSpace
public import Mathlib.Topology.Order.ProjIcc

/-! The actual compact circle-times-increment Hölder space, with a
continuous sampling convention that agrees with every short increment. -/

@[expose] public section

noncomputable section

open Set Filter Topology Metric
open scoped NNReal

namespace Euler2D

abbrev ContourIncrementInterval := Set.Icc (-Real.pi) Real.pi
abbrev ContourJointParameter := ContourCircle × ContourIncrementInterval
abbrev ContourJointHolderSpace (γ : ℝ≥0) := HolderFunctionSpace ContourJointParameter ℂ γ

def contourZeroIncrement : ContourIncrementInterval :=
  ⟨0, ⟨neg_nonpos.mpr Real.pi_pos.le, Real.pi_pos.le⟩⟩

def contourClippedIncrement (τ : ℝ) : ContourIncrementInterval :=
  Set.projIcc (-Real.pi) Real.pi (by linarith [Real.pi_pos]) τ

@[simp] theorem contourClippedIncrement_of_mem (τ : ℝ) (hτ : τ ∈ Icc (-Real.pi) Real.pi) :
    contourClippedIncrement τ = ⟨τ, hτ⟩ := Set.projIcc_of_mem _ hτ

@[simp] theorem contourClippedIncrement_zero : contourClippedIncrement 0 = contourZeroIncrement := by
  apply Subtype.ext
  rw [contourClippedIncrement_of_mem 0 contourZeroIncrement.property]
  rfl

theorem continuous_contourClippedIncrement : Continuous contourClippedIncrement :=
  by
    unfold contourClippedIncrement
    exact continuous_projIcc

def contourJointSample {γ : ℝ≥0} (r : ContourJointHolderSpace γ) (x : ContourCircle)
    (τ : ℝ) : ℂ := r (x, contourClippedIncrement τ)

@[simp] theorem contourJointSample_of_mem {γ : ℝ≥0} (r : ContourJointHolderSpace γ)
    (x : ContourCircle) (τ : ℝ) (hτ : τ ∈ Icc (-Real.pi) Real.pi) :
    contourJointSample r x τ = r (x, ⟨τ, hτ⟩) := by
  rw [contourJointSample, contourClippedIncrement_of_mem τ hτ]

@[simp] theorem contourJointSample_zero {γ : ℝ≥0} (r : ContourJointHolderSpace γ)
    (x : ContourCircle) : contourJointSample r x 0 = r (x, contourZeroIncrement) := by
  rw [contourJointSample, contourClippedIncrement_zero]

theorem continuous_contourJointSample {γ : ℝ≥0} (r : ContourJointHolderSpace γ) :
    Continuous (fun p : ContourCircle × ℝ => contourJointSample r p.1 p.2) := by
  exact (HolderFunctionSpace.toBCF γ r).continuous.comp
    (continuous_fst.prodMk (continuous_contourClippedIncrement.comp continuous_snd))

theorem norm_contourJointSample_le {γ : ℝ≥0} (r : ContourJointHolderSpace γ)
    (x : ContourCircle) (τ : ℝ) : ‖contourJointSample r x τ‖ ≤ ‖r‖ :=
  HolderFunctionSpace.norm_eval_le r _

theorem norm_contourJointSample_sub_theta_le {γ : ℝ≥0} (r : ContourJointHolderSpace γ)
    (x y : ContourCircle) (τ : ℝ) :
    ‖contourJointSample r x τ - contourJointSample r y τ‖ ≤
      ‖r‖ * dist x y ^ (γ : ℝ) := by
  change ‖r.val.1 (x, contourClippedIncrement τ) -
    r.val.1 (y, contourClippedIncrement τ)‖ ≤ _
  simpa only [Prod.dist_eq, dist_self, max_eq_left dist_nonneg] using
    HolderFunctionSpace.norm_sub_le_holder r (x, contourClippedIncrement τ)
      (y, contourClippedIncrement τ)

theorem norm_contourJointSample_sub_zero_le {γ : ℝ≥0} (r : ContourJointHolderSpace γ)
    (x : ContourCircle) (τ : ℝ) (hτ : |τ| ≤ Real.pi) :
    ‖contourJointSample r x τ - contourJointSample r x 0‖ ≤
      ‖r‖ * |τ| ^ (γ : ℝ) := by
  rw [contourJointSample_of_mem r x τ (abs_le.mp hτ), contourJointSample_zero]
  have hd : dist (x, (⟨τ, abs_le.mp hτ⟩ : ContourIncrementInterval))
      (x, contourZeroIncrement) = |τ| := by
    simp only [Prod.dist_eq, dist_self, Subtype.dist_eq, contourZeroIncrement,
      Real.dist_eq, sub_zero, max_eq_right (abs_nonneg τ)]
  simpa only [hd] using HolderFunctionSpace.norm_sub_le_holder r
    (x, (⟨τ, abs_le.mp hτ⟩ : ContourIncrementInterval)) (x, contourZeroIncrement)

end Euler2D

end
