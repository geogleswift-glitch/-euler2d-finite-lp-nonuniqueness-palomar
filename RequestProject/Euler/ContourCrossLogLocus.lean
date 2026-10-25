module

public import RequestProject.Euler.ContourCrossLogShapeLipschitz

/-! # Actual local Lipschitz regularity on the open separated-pair locus -/

@[expose] public section

noncomputable section

open Set Filter Topology Metric
open scoped NNReal

namespace Euler2D

local instance (priority := 2000) crossLocusC1_normedAddCommGroup (γ : ℝ≥0) :
    NormedAddCommGroup (ContourC1Space γ) :=
  Submodule.normedAddCommGroup (contourC1GraphSubmodule γ)

local instance (priority := 2000) crossLocusC1_normedSpace (γ : ℝ≥0) :
    NormedSpace ℝ (ContourC1Space γ) :=
  Submodule.normedSpace (contourC1GraphSubmodule γ)

theorem norm_contourCrossPair_sub_le_two_norm {γ : ℝ≥0}
    (p q : ContourC1Space γ × ContourC1Space γ) :
    ‖p.1 - q.1‖ + ‖p.2 - q.2‖ ≤ 2 * ‖p - q‖ := by
  have h1 : ‖p.1 - q.1‖ ≤ ‖p - q‖ := norm_fst_le (p - q)
  have h2 : ‖p.2 - q.2‖ ≤ ‖p - q‖ := norm_snd_le (p - q)
  linarith

theorem contourCrossSeparated_of_norm_sub_le {γ : ℝ≥0}
    (Z W Z' W' : ContourC1Space γ) {σ : ℝ} (hsep : ContourCrossSeparated Z W σ)
    (hδ : ‖Z - Z'‖ + ‖W - W'‖ ≤ σ / 2) : ContourCrossSeparated Z' W' (σ / 2) := by
  intro x y
  let a := ContourC1Space.toBCF γ Z x - ContourC1Space.toBCF γ W y
  let b := ContourC1Space.toBCF γ Z' x - ContourC1Space.toBCF γ W' y
  have hd : ‖a - b‖ ≤ ‖Z - Z'‖ + ‖W - W'‖ := by
    have he : a - b = (ContourC1Space.toBCF γ Z x - ContourC1Space.toBCF γ Z' x) -
        (ContourC1Space.toBCF γ W y - ContourC1Space.toBCF γ W' y) := by dsimp only [a, b]; abel
    rw [he]
    exact (norm_sub_le _ _).trans (add_le_add (ContourC1Space.norm_eval_le (Z - Z') x)
      (ContourC1Space.norm_eval_le (W - W') y))
  have hbase : σ ≤ ‖a‖ := hsep x y
  have hm := norm_sub_norm_le a b
  change σ / 2 ≤ ‖b‖
  linarith

abbrev PositiveSeparatedContourPair (γ : ℝ≥0) :=
  {p : ContourC1Space γ × ContourC1Space γ // ∃ σ > 0, ContourCrossSeparated p.1 p.2 σ}

theorem isOpen_positiveSeparatedContourPairs (γ : ℝ≥0) :
    IsOpen {p : ContourC1Space γ × ContourC1Space γ | ∃ σ > 0, ContourCrossSeparated p.1 p.2 σ} := by
  rw [Metric.isOpen_iff]
  intro p hp
  obtain ⟨σ, hσ, hsep⟩ := hp
  refine ⟨σ / 4, by positivity, ?_⟩
  intro q hq
  have hn : ‖p - q‖ < σ / 4 := by
    rw [← _root_.dist_eq_norm, dist_comm]
    exact hq
  have hδ : ‖p.1 - q.1‖ + ‖p.2 - q.2‖ ≤ σ / 2 := by
    linarith [norm_contourCrossPair_sub_le_two_norm p q]
  exact ⟨σ / 2, half_pos hσ, contourCrossSeparated_of_norm_sub_le p.1 p.2 q.1 q.2 hsep hδ⟩

def contourCrossLogC1OnLocus {γ : ℝ≥0} (hγ1 : (γ : ℝ) ≤ 1)
    (p : PositiveSeparatedContourPair γ) : ContourC1Space γ :=
  contourCrossLogC1 hγ1 p.val.1 p.val.2 p.property.choose_spec.1 p.property.choose_spec.2

theorem contourCrossLogC1OnLocus_eq {γ : ℝ≥0} (hγ1 : (γ : ℝ) ≤ 1)
    (p : PositiveSeparatedContourPair γ) {σ : ℝ} (hσ : 0 < σ)
    (hsep : ContourCrossSeparated p.val.1 p.val.2 σ) :
    contourCrossLogC1OnLocus hγ1 p = contourCrossLogC1 hγ1 p.val.1 p.val.2 hσ hsep :=
  contourCrossLogC1_independent_separation hγ1 p.val.1 p.val.2 p.property.choose_spec.1 hσ
    p.property.choose_spec.2 hsep

@[simp] theorem lift_contourCrossLogC1OnLocus {γ : ℝ≥0} (hγ1 : (γ : ℝ) ≤ 1)
    (p : PositiveSeparatedContourPair γ) :
    ContourC1Space.lift γ (contourCrossLogC1OnLocus hγ1 p) = contourC1CrossLogIntegral p.val.1 p.val.2 := rfl

theorem lipschitzOnWith_contourCrossLogC1OnLocus_of_bounds {γ : ℝ≥0} (hγ1 : (γ : ℝ) ≤ 1)
    (U : Set (PositiveSeparatedContourPair γ)) {σ M : ℝ} (hσ : 0 < σ) (hM : 0 ≤ M)
    (hsep : ∀ p ∈ U, ContourCrossSeparated p.val.1 p.val.2 σ)
    (hbound : ∀ p ∈ U, ‖p.val.1‖ ≤ M ∧ ‖p.val.2‖ ≤ M) :
    LipschitzOnWith (⟨2 * contourCrossLogShapeConstant (γ : ℝ) σ M,
      mul_nonneg (by norm_num) (contourCrossLogShapeConstant_nonneg hσ hM)⟩ : ℝ≥0)
      (contourCrossLogC1OnLocus hγ1) U := by
  have hC := contourCrossLogShapeConstant_nonneg (γ := (γ : ℝ)) hσ hM
  apply LipschitzOnWith.of_dist_le_mul
  intro p hp q hq
  change dist (contourCrossLogC1OnLocus hγ1 p) (contourCrossLogC1OnLocus hγ1 q) ≤
    (2 * contourCrossLogShapeConstant (γ : ℝ) σ M) * dist p.val q.val
  rw [_root_.dist_eq_norm, _root_.dist_eq_norm,
    contourCrossLogC1OnLocus_eq hγ1 p hσ (hsep p hp), contourCrossLogC1OnLocus_eq hγ1 q hσ (hsep q hq)]
  calc
    _ ≤ contourCrossLogShapeConstant (γ : ℝ) σ M * (‖p.val.1 - q.val.1‖ + ‖p.val.2 - q.val.2‖) :=
      norm_contourCrossLogC1_shape_sub_le hγ1 p.val.1 p.val.2 q.val.1 q.val.2 hσ (hsep p hp) (hsep q hq)
        hM (hbound p hp).1 (hbound p hp).2 (hbound q hq).1 (hbound q hq).2
    _ ≤ contourCrossLogShapeConstant (γ : ℝ) σ M * (2 * ‖p.val - q.val‖) :=
      mul_le_mul_of_nonneg_left (norm_contourCrossPair_sub_le_two_norm p.val q.val) hC
    _ = _ := by ring

theorem locallyLipschitz_contourCrossLogC1OnLocus {γ : ℝ≥0} (hγ1 : (γ : ℝ) ≤ 1) :
    LocallyLipschitz (contourCrossLogC1OnLocus hγ1) := by
  intro p
  obtain ⟨σ, hσ, hsep⟩ := p.property
  let M := max ‖p.val.1‖ ‖p.val.2‖ + 1
  have hM : 0 ≤ M := by dsimp [M]; positivity
  let ρ := min (σ / 4) 1
  have hρ : 0 < ρ := lt_min (by positivity) (by norm_num)
  have hball (q : PositiveSeparatedContourPair γ) (hq : q ∈ ball p ρ) :
      ContourCrossSeparated q.val.1 q.val.2 (σ / 2) ∧ ‖q.val.1‖ ≤ M ∧ ‖q.val.2‖ ≤ M := by
    have hn : ‖q.val - p.val‖ < ρ := by rw [← _root_.dist_eq_norm]; exact hq
    have hsum := norm_contourCrossPair_sub_le_two_norm p.val q.val
    rw [norm_sub_rev p.val q.val] at hsum
    have hsmall : ‖p.val.1 - q.val.1‖ + ‖p.val.2 - q.val.2‖ ≤ σ / 2 := by
      have hσsmall := hn.trans_le (min_le_left (σ / 4) 1)
      linarith
    have hn1 : ‖q.val.1 - p.val.1‖ < 1 :=
      (norm_fst_le (q.val - p.val)).trans_lt (hn.trans_le (min_le_right _ _))
    have hn2 : ‖q.val.2 - p.val.2‖ < 1 :=
      (norm_snd_le (q.val - p.val)).trans_lt (hn.trans_le (min_le_right _ _))
    refine ⟨contourCrossSeparated_of_norm_sub_le p.val.1 p.val.2 q.val.1 q.val.2 hsep hsmall, ?_, ?_⟩
    · change ‖q.val.1‖ ≤ max ‖p.val.1‖ ‖p.val.2‖ + 1
      linarith [norm_sub_norm_le q.val.1 p.val.1, le_max_left ‖p.val.1‖ ‖p.val.2‖]
    · change ‖q.val.2‖ ≤ max ‖p.val.1‖ ‖p.val.2‖ + 1
      linarith [norm_sub_norm_le q.val.2 p.val.2, le_max_right ‖p.val.1‖ ‖p.val.2‖]
  refine ⟨⟨2 * contourCrossLogShapeConstant (γ : ℝ) (σ / 2) M,
      mul_nonneg (by norm_num) (contourCrossLogShapeConstant_nonneg (half_pos hσ) hM)⟩,
    ball p ρ, ball_mem_nhds p hρ, ?_⟩
  exact lipschitzOnWith_contourCrossLogC1OnLocus_of_bounds hγ1 (ball p ρ) (half_pos hσ) hM
    (fun q hq => (hball q hq).1) (fun q hq => (hball q hq).2)

end Euler2D

end
