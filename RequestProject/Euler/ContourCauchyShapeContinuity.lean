module

public import RequestProject.Euler.ContourCauchyShapeEstimates
public import RequestProject.Euler.ContourCauchyOperator
public import RequestProject.Euler.ContourDerivativePhaseContinuity

/-! # Genuine Hölder operator-norm continuity in the contour -/

@[expose] public section

noncomputable section

open Set Filter Topology Metric
open scoped NNReal ENNReal BoundedContinuousFunction

namespace Euler2D

local instance (priority := 2000) shapeC1_normedAddCommGroup (γ : ℝ≥0) :
    NormedAddCommGroup (ContourC1Space γ) :=
  Submodule.normedAddCommGroup (contourC1GraphSubmodule γ)

local instance (priority := 2000) shapeC1_normedSpace (γ : ℝ≥0) :
    NormedSpace ℝ (ContourC1Space γ) :=
  Submodule.normedSpace (contourC1GraphSubmodule γ)

def contourCauchyShapeOperatorConstant (γ c M : ℝ) : ℝ :=
  contourCauchyShapeUniformIntegralConstant γ c M + contourCauchyShapeHolderIntegralConstant γ c M

theorem contourCauchyShapeOperatorConstant_nonneg {γ c M : ℝ}
    (hγ : 0 < γ) (hc : 0 < c) (hM : 0 ≤ M) :
    0 ≤ contourCauchyShapeOperatorConstant γ c M :=
  add_nonneg (contourCauchyShapeUniformIntegralConstant_nonneg hγ hc hM)
    (contourCauchyShapeHolderIntegralConstant_nonneg hγ hc hM)

theorem norm_contourCauchyResidualOperator_shape_sub_apply_le {γ : ℝ≥0}
    (hγ : 0 < (γ : ℝ)) (Z W : ContourC1Space γ) (f : ContourHolderSpace γ)
    {c M : ℝ} (hc : 0 < c) (hM : 0 ≤ M)
    (hZ : ContourC1Space.HasChordArcLower Z c) (hW : ContourC1Space.HasChordArcLower W c)
    (hZM : ‖Z‖ ≤ M) (hWM : ‖W‖ ≤ M) :
    ‖contourCauchyResidualOperator Z hγ hc hZ f - contourCauchyResidualOperator W hγ hc hW f‖ ≤
      (contourCauchyShapeOperatorConstant (γ : ℝ) c M * ‖Z - W‖) * ‖f‖ := by
  have hU := contourCauchyShapeUniformIntegralConstant_nonneg hγ hc hM
  have hV := contourCauchyShapeHolderIntegralConstant_nonneg hγ hc hM
  have hO := contourCauchyShapeOperatorConstant_nonneg hγ hc hM
  have hUC : contourCauchyShapeUniformIntegralConstant (γ : ℝ) c M ≤
      contourCauchyShapeOperatorConstant (γ : ℝ) c M := le_add_of_nonneg_right hV
  have hVC : contourCauchyShapeHolderIntegralConstant (γ : ℝ) c M ≤
      contourCauchyShapeOperatorConstant (γ : ℝ) c M := le_add_of_nonneg_left hU
  apply norm_contourHolder_le_of_bounds _ (by positivity)
  · intro x
    obtain ⟨θ, rfl⟩ := QuotientAddGroup.mk_surjective x
    change ‖contourC1CauchyResidualIncrement Z f θ - contourC1CauchyResidualIncrement W f θ‖ ≤ _
    exact (norm_contourC1CauchyResidualIncrement_shape_sub_le hγ Z W f hc hM hZ hW hWM θ).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hUC (norm_nonneg _)) (norm_nonneg _))
  · intro x y
    obtain ⟨θ, η, hθ, hη, _, hdist⟩ := exists_short_contour_representatives x y
    have hb := norm_contourC1CauchyResidualIncrement_shape_parameter_sub_le hγ Z W f hc hM
      hZ hW hZM hWM θ η
    rw [← contourCauchyResidualOperator_apply Z hγ hc hZ f θ,
      ← contourCauchyResidualOperator_apply W hγ hc hW f θ,
      ← contourCauchyResidualOperator_apply Z hγ hc hZ f η,
      ← contourCauchyResidualOperator_apply W hγ hc hW f η, hθ, hη, ← hdist] at hb
    exact hb.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hVC (norm_nonneg _)) (norm_nonneg _))
      (Real.rpow_nonneg dist_nonneg _))

theorem norm_contourCauchyResidualOperator_shape_sub_le {γ : ℝ≥0}
    (hγ : 0 < (γ : ℝ)) (Z W : ContourC1Space γ) {c M : ℝ} (hc : 0 < c) (hM : 0 ≤ M)
    (hZ : ContourC1Space.HasChordArcLower Z c) (hW : ContourC1Space.HasChordArcLower W c)
    (hZM : ‖Z‖ ≤ M) (hWM : ‖W‖ ≤ M) :
    ‖contourCauchyResidualOperator Z hγ hc hZ - contourCauchyResidualOperator W hγ hc hW‖ ≤
      contourCauchyShapeOperatorConstant (γ : ℝ) c M * ‖Z - W‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _
    (mul_nonneg (contourCauchyShapeOperatorConstant_nonneg hγ hc hM) (norm_nonneg _))
  intro f
  exact norm_contourCauchyResidualOperator_shape_sub_apply_le hγ Z W f hc hM hZ hW hZM hWM

theorem norm_contourCauchyIncrementOperator_shape_sub_le {γ : ℝ≥0}
    (hγ : 0 < (γ : ℝ)) (hγ1 : (γ : ℝ) < 1) (Z W : ContourC1Space γ)
    {c M : ℝ} (hc : 0 < c) (hM : 0 ≤ M)
    (hZ : ContourC1Space.HasChordArcLower Z c) (hW : ContourC1Space.HasChordArcLower W c)
    (hZM : ‖Z‖ ≤ M) (hWM : ‖W‖ ≤ M) :
    ‖contourCauchyIncrementOperator Z hγ hγ1 hc hZ - contourCauchyIncrementOperator W hγ hγ1 hc hW‖ ≤
      contourCauchyShapeOperatorConstant (γ : ℝ) c M * ‖Z - W‖ := by
  have he : contourCauchyIncrementOperator Z hγ hγ1 hc hZ -
      contourCauchyIncrementOperator W hγ hγ1 hc hW =
      contourCauchyResidualOperator Z hγ hc hZ - contourCauchyResidualOperator W hγ hc hW := by
    unfold contourCauchyIncrementOperator
    abel
  rw [he]
  exact norm_contourCauchyResidualOperator_shape_sub_le hγ Z W hc hM hZ hW hZM hWM

theorem contourCauchyIncrementOperator_independent_lower {γ : ℝ≥0}
    (hγ : 0 < (γ : ℝ)) (hγ1 : (γ : ℝ) < 1) (Z : ContourC1Space γ)
    {c d : ℝ} (hc : 0 < c) (hd : 0 < d)
    (hZc : ContourC1Space.HasChordArcLower Z c) (hZd : ContourC1Space.HasChordArcLower Z d) :
    contourCauchyIncrementOperator Z hγ hγ1 hc hZc = contourCauchyIncrementOperator Z hγ hγ1 hd hZd := by
  apply ContinuousLinearMap.ext
  intro f
  apply HolderFunctionSpace.ext
  intro x
  obtain ⟨θ, rfl⟩ := QuotientAddGroup.mk_surjective x
  rw [contourCauchyIncrementOperator_apply, contourCauchyIncrementOperator_apply]

abbrev ContourCauchyShapeDomain (γ : ℝ≥0) (c M : ℝ) :=
  {Z : ContourC1Space γ // ‖Z‖ ≤ M ∧ ContourC1Space.HasChordArcLower Z c}

def contourCauchyIncrementOperatorOnShapeDomain {γ : ℝ≥0}
    (hγ : 0 < (γ : ℝ)) (hγ1 : (γ : ℝ) < 1) {c M : ℝ} (hc : 0 < c)
    (Z : ContourCauchyShapeDomain γ c M) : ContourHolderSpace γ →L[ℝ] ContourHolderSpace γ :=
  contourCauchyIncrementOperator Z.val hγ hγ1 hc Z.property.2

theorem lipschitzWith_contourCauchyIncrementOperatorOnShapeDomain {γ : ℝ≥0}
    (hγ : 0 < (γ : ℝ)) (hγ1 : (γ : ℝ) < 1) {c M : ℝ} (hc : 0 < c) (hM : 0 ≤ M) :
    LipschitzWith (⟨contourCauchyShapeOperatorConstant (γ : ℝ) c M,
      contourCauchyShapeOperatorConstant_nonneg hγ hc hM⟩ : ℝ≥0)
      (contourCauchyIncrementOperatorOnShapeDomain hγ hγ1 (M := M) hc) := by
  apply LipschitzWith.of_dist_le_mul
  intro Z W
  change dist (contourCauchyIncrementOperator Z.val hγ hγ1 hc Z.property.2)
      (contourCauchyIncrementOperator W.val hγ hγ1 hc W.property.2) ≤
    contourCauchyShapeOperatorConstant (γ : ℝ) c M * dist Z.val W.val
  rw [_root_.dist_eq_norm, _root_.dist_eq_norm]
  exact norm_contourCauchyIncrementOperator_shape_sub_le hγ hγ1 Z.val W.val hc hM
    Z.property.2 W.property.2 Z.property.1 W.property.1

def contourCauchyIncrementOperatorOnLocus {γ : ℝ≥0}
    (hγ : 0 < (γ : ℝ)) (hγ1 : (γ : ℝ) < 1)
    (Z : PositiveChordContour γ) :
    ContourHolderSpace γ →L[ℝ] ContourHolderSpace γ :=
  contourCauchyIncrementOperator Z.val hγ hγ1 (positiveChordConstant_pos Z)
    (hasChordArcLower_positiveChordConstant Z)

theorem contourCauchyIncrementOperatorOnLocus_eq {γ : ℝ≥0}
    (hγ : 0 < (γ : ℝ)) (hγ1 : (γ : ℝ) < 1)
    (Z : {Z : ContourC1Space γ // ContourC1Space.HasPositiveChordArc Z})
    {c : ℝ} (hc : 0 < c) (hZc : ContourC1Space.HasChordArcLower Z.val c) :
    contourCauchyIncrementOperatorOnLocus hγ hγ1 Z = contourCauchyIncrementOperator Z.val hγ hγ1 hc hZc :=
  contourCauchyIncrementOperator_independent_lower hγ hγ1 Z.val Z.property.choose_spec.1 hc
    Z.property.choose_spec.2 hZc

@[simp] theorem contourCauchyIncrementOperatorOnLocus_apply {γ : ℝ≥0}
    (hγ : 0 < (γ : ℝ)) (hγ1 : (γ : ℝ) < 1) (Z : PositiveChordContour γ)
    (f : ContourHolderSpace γ) (θ : ℝ) :
    contourCauchyIncrementOperatorOnLocus hγ hγ1 Z f (θ : ContourCircle) =
      contourC1CauchyIncrement Z.val f θ :=
  contourCauchyIncrementOperator_apply Z.val hγ hγ1 (positiveChordConstant_pos Z)
    (hasChordArcLower_positiveChordConstant Z) f θ

/-- The actual increment depends continuously on the contour in the
genuine Hölder operator norm on the full positive-chord locus. -/
theorem continuous_contourCauchyIncrementOperatorOnLocus {γ : ℝ≥0}
    (hγ : 0 < (γ : ℝ)) (hγ1 : (γ : ℝ) < 1) :
    Continuous (contourCauchyIncrementOperatorOnLocus hγ hγ1) := by
  apply continuous_iff_continuousAt.mpr
  intro Z
  obtain ⟨c, hc, hZ⟩ := Z.property
  let M := ‖Z.val‖ + 1
  have hM : 0 ≤ M := by dsimp [M]; positivity
  let δ := min (c / 2) 1
  have hδ : 0 < δ := lt_min (half_pos hc) (by norm_num)
  have hZhalf : ContourC1Space.HasChordArcLower Z.val (c / 2) := by
    intro θ τ hτ
    exact (mul_le_mul_of_nonneg_right (by linarith : c / 2 ≤ c) (abs_nonneg τ)).trans (hZ θ τ hτ)
  have hnear : ∀ᶠ W : {Z : ContourC1Space γ // ContourC1Space.HasPositiveChordArc Z} in 𝓝 Z,
      W.val ∈ ball Z.val δ :=
    (continuous_subtype_val.tendsto Z).eventually (ball_mem_nhds _ hδ)
  have hb : ∀ᶠ W : {Z : ContourC1Space γ // ContourC1Space.HasPositiveChordArc Z} in 𝓝 Z,
      ‖contourCauchyIncrementOperatorOnLocus hγ hγ1 W -
          contourCauchyIncrementOperatorOnLocus hγ hγ1 Z‖ ≤
        contourCauchyShapeOperatorConstant (γ : ℝ) (c / 2) M * ‖W.val - Z.val‖ := by
    filter_upwards [hnear] with W hW
    have hd : dist W.val Z.val < δ := hW
    have hWc : ContourC1Space.HasChordArcLower W.val (c / 2) :=
      ContourC1Space.hasChordArcLower_of_mem_ball W.val Z.val hZ (hd.trans_le (min_le_left _ _))
    have hWn : ‖W.val - Z.val‖ < 1 := by
      rw [← _root_.dist_eq_norm]
      exact hd.trans_le (min_le_right _ _)
    have hWM : ‖W.val‖ ≤ M := by
      change ‖W.val‖ ≤ ‖Z.val‖ + 1
      linarith [norm_sub_norm_le W.val Z.val]
    rw [contourCauchyIncrementOperatorOnLocus_eq hγ hγ1 W (half_pos hc) hWc,
      contourCauchyIncrementOperatorOnLocus_eq hγ hγ1 Z (half_pos hc) hZhalf]
    exact norm_contourCauchyIncrementOperator_shape_sub_le hγ hγ1 W.val Z.val (half_pos hc) hM
      hWc hZhalf hWM (by change ‖Z.val‖ ≤ ‖Z.val‖ + 1; linarith)
  have hn : Tendsto (fun W : {Z : ContourC1Space γ // ContourC1Space.HasPositiveChordArc Z} =>
      ‖W.val - Z.val‖) (𝓝 Z) (𝓝 0) := by
    have hncont : Continuous
        (fun W : PositiveChordContour γ => ‖W.val - Z.val‖) :=
      (continuous_subtype_val.sub continuous_const).norm
    simpa only [sub_self, norm_zero] using
      hncont.tendsto Z
  have hm : Tendsto (fun W : {Z : ContourC1Space γ // ContourC1Space.HasPositiveChordArc Z} =>
      contourCauchyShapeOperatorConstant (γ : ℝ) (c / 2) M * ‖W.val - Z.val‖)
      (𝓝 Z) (𝓝 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul hn
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  exact squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) hb hm

end Euler2D

end
