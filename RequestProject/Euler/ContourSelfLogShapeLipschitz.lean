module

public import RequestProject.Euler.ContourLogDerivativeShapeLipschitz
public import RequestProject.Euler.ContourLogShapeLipschitz
public import RequestProject.Euler.ContourNearCircleSelfLog

/-! # Genuine local Lipschitz regularity of the original self-log map

The actual value and actual derivative estimates are combined in the
true closed-graph max norm of C¹ Hölder contours.
-/

@[expose] public section

noncomputable section

open Set Filter Topology Metric
open scoped NNReal

namespace Euler2D

local instance (priority := 2000) selfLogShapeC1_normedAddCommGroup (γ : ℝ≥0) :
    NormedAddCommGroup (ContourC1Space γ) :=
  Submodule.normedAddCommGroup (contourC1GraphSubmodule γ)

local instance (priority := 2000) selfLogShapeLittle_normedAddCommGroup (γ : ℝ≥0) :
    NormedAddCommGroup (LittleContourSpace γ) :=
  Submodule.normedAddCommGroup (LittleContourSpace γ)

def contourSelfLogShapeConstant (γ c M : ℝ) : ℝ :=
  max (contourLogShapeConstant c M) (contourLogDerivativeShapeConstant γ c M)

theorem contourSelfLogShapeConstant_nonneg {γ c M : ℝ}
    (hγ : 0 < γ) (hγ1 : γ < 1) (hc : 0 < c) (hM : 0 ≤ M) :
    0 ≤ contourSelfLogShapeConstant γ c M :=
  (contourLogDerivativeShapeConstant_nonneg hγ hγ1 hc hM).trans (le_max_right _ _)

theorem norm_nearCircleSelfLogC1_shape_sub_le {γ : ℝ≥0}
    (hγ : 0 < (γ : ℝ)) (hγ1 : (γ : ℝ) < 1) (Z₀ : ContourC1Space γ)
    {r : ℝ} (hr : 0 < r) (href : ContourC1Space.lift γ Z₀ = refCircle r)
    (Z W : NearCircleLittleContour Z₀ r) {c M : ℝ} (hc : 0 < c) (hM : 0 ≤ M)
    (hZ : ContourC1Space.HasChordArcLower Z.val.val c)
    (hW : ContourC1Space.HasChordArcLower W.val.val c)
    (hZM : ‖Z.val.val‖ ≤ M) (hWM : ‖W.val.val‖ ≤ M) :
    ‖nearCircleSelfLogC1 hγ hγ1 Z₀ hr href Z - nearCircleSelfLogC1 hγ hγ1 Z₀ hr href W‖ ≤
      contourSelfLogShapeConstant (γ : ℝ) c M * ‖Z.val.val - W.val.val‖ := by
  let pZ := nearCirclePositiveContour Z₀ hr href Z
  let pW := nearCirclePositiveContour Z₀ hr href W
  have hF := norm_selfLogCircleBCF_sub_le pZ pW hc hZ hW hZM hWM
  have hG : ‖positiveContourLogDerivativeHolder hγ hγ1 pZ -
      positiveContourLogDerivativeHolder hγ hγ1 pW‖ ≤
      contourLogDerivativeShapeConstant (γ : ℝ) c M * ‖Z.val.val - W.val.val‖ := by
    rw [positiveContourLogDerivativeHolder_eq hγ hγ1 pZ hc hZ,
      positiveContourLogDerivativeHolder_eq hγ hγ1 pW hc hW]
    exact norm_contourLogDerivativeHolder_shape_sub_le hγ hγ1 Z.val.val W.val.val hc hM hZ hW hZM hWM
  change max ‖ContourC1Space.selfLogCircleBCF pZ - ContourC1Space.selfLogCircleBCF pW‖
      ‖positiveContourLogDerivativeHolder hγ hγ1 pZ - positiveContourLogDerivativeHolder hγ hγ1 pW‖ ≤ _
  apply max_le
  · exact hF.trans (by
      change ‖Z.val.val - W.val.val‖ * contourLogShapeConstant c M ≤ _
      rw [mul_comm ‖Z.val.val - W.val.val‖]
      exact mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
  · exact hG.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _))

theorem lipschitzOnWith_nearCircleSelfLogC1_of_bounds {γ : ℝ≥0}
    (hγ : 0 < (γ : ℝ)) (hγ1 : (γ : ℝ) < 1) (Z₀ : ContourC1Space γ)
    {r : ℝ} (hr : 0 < r) (href : ContourC1Space.lift γ Z₀ = refCircle r)
    (U : Set (NearCircleLittleContour Z₀ r)) {c M : ℝ} (hc : 0 < c) (hM : 0 ≤ M)
    (hchord : ∀ Z ∈ U, ContourC1Space.HasChordArcLower Z.val.val c)
    (hbound : ∀ Z ∈ U, ‖Z.val.val‖ ≤ M) :
    LipschitzOnWith (⟨contourSelfLogShapeConstant (γ : ℝ) c M,
      contourSelfLogShapeConstant_nonneg hγ hγ1 hc hM⟩ : ℝ≥0)
      (nearCircleSelfLogC1 hγ hγ1 Z₀ hr href) U := by
  apply LipschitzOnWith.of_dist_le_mul
  intro Z hZ W hW
  change dist (nearCircleSelfLogC1 hγ hγ1 Z₀ hr href Z)
      (nearCircleSelfLogC1 hγ hγ1 Z₀ hr href W) ≤
    contourSelfLogShapeConstant (γ : ℝ) c M * dist Z.val.val W.val.val
  rw [_root_.dist_eq_norm, _root_.dist_eq_norm]
  exact norm_nearCircleSelfLogC1_shape_sub_le hγ hγ1 Z₀ hr href Z W hc hM
    (hchord Z hZ) (hchord W hW) (hbound Z hZ) (hbound W hW)

/-- The original self-log integral is locally Lipschitz in its genuine
C¹ Hölder output norm on the true open near-circle little-contour domain. -/
theorem locallyLipschitz_nearCircleSelfLogC1 {γ : ℝ≥0}
    (hγ : 0 < (γ : ℝ)) (hγ1 : (γ : ℝ) < 1) (Z₀ : ContourC1Space γ)
    {r : ℝ} (hr : 0 < r) (href : ContourC1Space.lift γ Z₀ = refCircle r) :
    LocallyLipschitz (nearCircleSelfLogC1 hγ hγ1 Z₀ hr href) := by
  intro Z
  obtain ⟨c, hc, hZ⟩ := (nearCirclePositiveContour Z₀ hr href Z).property
  let M := ‖Z.val.val‖ + 1
  have hM : 0 ≤ M := by dsimp [M]; positivity
  let ρ := min (c / 2) 1
  have hρ : 0 < ρ := lt_min (half_pos hc) (by norm_num)
  have hball (W : NearCircleLittleContour Z₀ r) (hW : W ∈ ball Z ρ) :
      ContourC1Space.HasChordArcLower W.val.val (c / 2) ∧ ‖W.val.val‖ ≤ M := by
    have hd : dist W.val.val Z.val.val < ρ := hW
    have hWc : ContourC1Space.HasChordArcLower W.val.val (c / 2) :=
      ContourC1Space.hasChordArcLower_of_mem_ball W.val.val Z.val.val hZ
        (hd.trans_le (min_le_left _ _))
    have hn : ‖W.val.val - Z.val.val‖ < 1 := by
      rw [← _root_.dist_eq_norm]
      exact hd.trans_le (min_le_right _ _)
    refine ⟨hWc, ?_⟩
    change ‖W.val.val‖ ≤ ‖Z.val.val‖ + 1
    linarith [norm_sub_norm_le W.val.val Z.val.val]
  refine ⟨⟨contourSelfLogShapeConstant (γ : ℝ) (c / 2) M,
      contourSelfLogShapeConstant_nonneg hγ hγ1 (half_pos hc) hM⟩,
    ball Z ρ, ball_mem_nhds Z hρ, ?_⟩
  exact lipschitzOnWith_nearCircleSelfLogC1_of_bounds hγ hγ1 Z₀ hr href (ball Z ρ)
    (half_pos hc) hM (fun W hW => (hball W hW).1) (fun W hW => (hball W hW).2)

end Euler2D

end
