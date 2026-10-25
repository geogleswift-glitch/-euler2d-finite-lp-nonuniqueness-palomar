module

public import RequestProject.Euler.ContourCauchyShapeKernel
public import RequestProject.Euler.ContourAdmissibility

/-! # Genuine integrated shape differences of the Cauchy remainder -/

@[expose] public section

noncomputable section

open Set Filter Topology Metric MeasureTheory
open scoped NNReal ENNReal BoundedContinuousFunction

namespace Euler2D

def contourCauchyShapeIntegrand {γ : ℝ≥0} (Z W : ContourC1Space γ)
    (f : ContourHolderSpace γ) (θ τ : ℝ) : ℂ :=
  (contourCauchyPoleIntegrand (ContourC1Space.lift γ Z) (deriv (ContourC1Space.lift γ Z)) θ τ -
    contourCauchyPoleIntegrand (ContourC1Space.lift γ W) (deriv (ContourC1Space.lift γ W)) θ τ) *
      (f ((θ + τ : ℝ) : ContourCircle) - f (θ : ContourCircle))

theorem contourCauchyResidualIncrement_sub_eq_integral_shape {γ : ℝ≥0}
    (Z W : ContourC1Space γ) (f : ContourHolderSpace γ) {c : ℝ}
    (hγ : 0 < (γ : ℝ)) (hc : 0 < c)
    (hZ : ContourC1Space.HasChordArcLower Z c) (hW : ContourC1Space.HasChordArcLower W c)
    (θ : ℝ) :
    contourC1CauchyResidualIncrement Z f θ - contourC1CauchyResidualIncrement W f θ =
      ∫ τ in Icc (-Real.pi) Real.pi, contourCauchyShapeIntegrand Z W f θ τ := by
  have hiZ := integrableOn_contourC1CauchyResidualIncrementIntegrand Z f hγ hc hZ θ
  have hiW := integrableOn_contourC1CauchyResidualIncrementIntegrand W f hγ hc hW θ
  unfold contourC1CauchyResidualIncrement contourCauchyResidualIncrement
  rw [← integral_sub hiZ hiW]
  apply integral_congr_ae
  filter_upwards [] with τ
  dsimp only [contourCauchyShapeIntegrand, contourCauchyResidualIncrementIntegrand, Pi.sub_apply]
  ring

theorem norm_contourCauchyShapeIntegrand_le {γ : ℝ≥0}
    (hγ : 0 < (γ : ℝ)) (Z W : ContourC1Space γ) (f : ContourHolderSpace γ)
    {c M θ τ : ℝ} (hc : 0 < c) (hM : 0 ≤ M)
    (hZ : ContourC1Space.HasChordArcLower Z c) (hW : ContourC1Space.HasChordArcLower W c)
    (hWM : ‖W‖ ≤ M) (hτ : |τ| ≤ Real.pi) :
    ‖contourCauchyShapeIntegrand Z W f θ τ‖ ≤
      ((contourCauchyShapeUniformConstant c M * ‖Z - W‖) *
        (‖f‖ * Real.pi ^ (γ : ℝ))) * |τ| ^ ((γ : ℝ) - 1) := by
  have hk := norm_contourCauchyPoleIntegrand_shape_sub_le hγ Z W hc hM
    (fun s => hZ s τ hτ) (fun s => hW s τ hτ) hWM (θ := θ)
  have hf : ‖f ((θ + τ : ℝ) : ContourCircle) - f (θ : ContourCircle)‖ ≤
      ‖f‖ * Real.pi ^ (γ : ℝ) :=
    (norm_contourHolder_lift_sub_le f θ τ).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (abs_nonneg _) hτ γ.coe_nonneg) (norm_nonneg _))
  rw [contourCauchyShapeIntegrand, norm_mul]
  calc
    _ ≤ ((contourCauchyShapeUniformConstant c M * ‖Z - W‖) * |τ| ^ ((γ : ℝ) - 1)) *
        (‖f‖ * Real.pi ^ (γ : ℝ)) :=
      mul_le_mul hk hf (norm_nonneg _) (mul_nonneg
        (mul_nonneg (contourCauchyShapeUniformConstant_nonneg hc hM) (norm_nonneg _))
        (Real.rpow_nonneg (abs_nonneg _) _))
    _ = _ := by ring

theorem norm_contourCauchyShapeIntegrand_parameter_sub_le {γ : ℝ≥0}
    (hγ : 0 < (γ : ℝ)) (Z W : ContourC1Space γ) (f : ContourHolderSpace γ)
    {c M θ η τ : ℝ} (hc : 0 < c) (hM : 0 ≤ M)
    (hZ : ContourC1Space.HasChordArcLower Z c) (hW : ContourC1Space.HasChordArcLower W c)
    (hZM : ‖Z‖ ≤ M) (hWM : ‖W‖ ≤ M) (hτπ : |τ| ≤ Real.pi) :
    ‖contourCauchyShapeIntegrand Z W f θ τ - contourCauchyShapeIntegrand Z W f η τ‖ ≤
      (((2 * contourCauchyShapeUniformConstant c M + contourCauchyShapeParameterConstant c M) *
        ‖Z - W‖ * ‖f‖) * |θ - η| ^ (γ : ℝ)) * |τ| ^ ((γ : ℝ) - 1) := by
  let S : ℝ → ℝ → ℂ := fun s t =>
    contourCauchyPoleIntegrand (ContourC1Space.lift γ Z) (deriv (ContourC1Space.lift γ Z)) s t -
      contourCauchyPoleIntegrand (ContourC1Space.lift γ W) (deriv (ContourC1Space.lift γ W)) s t
  have hA := contourCauchyShapeUniformConstant_nonneg hc hM
  have hP := contourCauchyShapeParameterConstant_nonneg hc hM
  by_cases hτ : τ = 0
  · subst τ
    simp only [contourCauchyShapeIntegrand, add_zero, sub_self, mul_zero, norm_zero]
    positivity
  have ht : 0 < |τ| := abs_pos.mpr hτ
  have hk : ‖S θ τ‖ ≤ (contourCauchyShapeUniformConstant c M * ‖Z - W‖) *
      |τ| ^ ((γ : ℝ) - 1) :=
    norm_contourCauchyPoleIntegrand_shape_sub_le hγ Z W hc hM
      (fun s => hZ s τ hτπ) (fun s => hW s τ hτπ) hWM
  have hkp : ‖S θ τ - S η τ‖ ≤
      (contourCauchyShapeParameterConstant c M * ‖Z - W‖) * |θ - η| ^ (γ : ℝ) / |τ| :=
    norm_contourCauchyPoleIntegrand_shape_parameter_sub_le hγ Z W hc hM
      (fun s => hZ s τ hτπ) (fun s => hW s τ hτπ) hZM hWM
  have hi : ‖(f ((θ + τ : ℝ) : ContourCircle) - f (θ : ContourCircle)) -
      (f ((η + τ : ℝ) : ContourCircle) - f (η : ContourCircle))‖ ≤
      2 * ‖f‖ * |θ - η| ^ (γ : ℝ) := by
    have he : (f ((θ + τ : ℝ) : ContourCircle) - f (θ : ContourCircle)) -
        (f ((η + τ : ℝ) : ContourCircle) - f (η : ContourCircle)) =
        (f ((θ + τ : ℝ) : ContourCircle) - f ((η + τ : ℝ) : ContourCircle)) -
          (f (θ : ContourCircle) - f (η : ContourCircle)) := by abel
    rw [he]
    calc
      _ ≤ ‖f ((θ + τ : ℝ) : ContourCircle) - f ((η + τ : ℝ) : ContourCircle)‖ +
          ‖f (θ : ContourCircle) - f (η : ContourCircle)‖ := norm_sub_le _ _
      _ ≤ ‖f‖ * |θ - η| ^ (γ : ℝ) + ‖f‖ * |θ - η| ^ (γ : ℝ) := by
        apply add_le_add
        · simpa only [add_sub_add_right_eq_sub] using norm_contourHolder_lift_sub_global_le f (θ + τ) (η + τ)
        · exact norm_contourHolder_lift_sub_global_le f θ η
      _ = _ := by ring
  have hif := norm_contourHolder_lift_sub_le f η τ
  have he : contourCauchyShapeIntegrand Z W f θ τ - contourCauchyShapeIntegrand Z W f η τ =
      S θ τ * ((f ((θ + τ : ℝ) : ContourCircle) - f (θ : ContourCircle)) -
        (f ((η + τ : ℝ) : ContourCircle) - f (η : ContourCircle))) +
      (S θ τ - S η τ) * (f ((η + τ : ℝ) : ContourCircle) - f (η : ContourCircle)) := by
    dsimp only [contourCauchyShapeIntegrand, S]
    ring
  rw [he]
  calc
    _ ≤ ‖S θ τ‖ * ‖(f ((θ + τ : ℝ) : ContourCircle) - f (θ : ContourCircle)) -
        (f ((η + τ : ℝ) : ContourCircle) - f (η : ContourCircle))‖ +
        ‖S θ τ - S η τ‖ * ‖f ((η + τ : ℝ) : ContourCircle) - f (η : ContourCircle)‖ := by
      simpa only [norm_mul] using norm_add_le
        (S θ τ * ((f ((θ + τ : ℝ) : ContourCircle) - f (θ : ContourCircle)) -
          (f ((η + τ : ℝ) : ContourCircle) - f (η : ContourCircle))))
        ((S θ τ - S η τ) * (f ((η + τ : ℝ) : ContourCircle) - f (η : ContourCircle)))
    _ ≤ ((contourCauchyShapeUniformConstant c M * ‖Z - W‖) * |τ| ^ ((γ : ℝ) - 1)) *
        (2 * ‖f‖ * |θ - η| ^ (γ : ℝ)) +
        ((contourCauchyShapeParameterConstant c M * ‖Z - W‖) * |θ - η| ^ (γ : ℝ) / |τ|) *
          (‖f‖ * |τ| ^ (γ : ℝ)) := by
      apply add_le_add
      · exact mul_le_mul hk hi (norm_nonneg _) (by positivity)
      · exact mul_le_mul hkp hif (norm_nonneg _) (by positivity)
    _ = _ := by rw [Real.rpow_sub_one ht.ne']; ring

def contourCauchyShapeUniformIntegralConstant (γ c M : ℝ) : ℝ :=
  (contourCauchyShapeUniformConstant c M * Real.pi ^ γ) * (2 * Real.pi ^ γ / γ)

def contourCauchyShapeHolderIntegralConstant (γ c M : ℝ) : ℝ :=
  (2 * contourCauchyShapeUniformConstant c M + contourCauchyShapeParameterConstant c M) *
    (2 * Real.pi ^ γ / γ)

theorem contourCauchyShapeUniformIntegralConstant_nonneg {γ c M : ℝ}
    (hγ : 0 < γ) (hc : 0 < c) (hM : 0 ≤ M) :
    0 ≤ contourCauchyShapeUniformIntegralConstant γ c M := by
  have hA := contourCauchyShapeUniformConstant_nonneg hc hM
  unfold contourCauchyShapeUniformIntegralConstant
  positivity

theorem contourCauchyShapeHolderIntegralConstant_nonneg {γ c M : ℝ}
    (hγ : 0 < γ) (hc : 0 < c) (hM : 0 ≤ M) :
    0 ≤ contourCauchyShapeHolderIntegralConstant γ c M := by
  have hA := contourCauchyShapeUniformConstant_nonneg hc hM
  have hP := contourCauchyShapeParameterConstant_nonneg hc hM
  unfold contourCauchyShapeHolderIntegralConstant
  positivity

theorem norm_contourC1CauchyResidualIncrement_shape_sub_le {γ : ℝ≥0}
    (hγ : 0 < (γ : ℝ)) (Z W : ContourC1Space γ) (f : ContourHolderSpace γ)
    {c M : ℝ} (hc : 0 < c) (hM : 0 ≤ M)
    (hZ : ContourC1Space.HasChordArcLower Z c) (hW : ContourC1Space.HasChordArcLower W c)
    (hWM : ‖W‖ ≤ M) (θ : ℝ) :
    ‖contourC1CauchyResidualIncrement Z f θ - contourC1CauchyResidualIncrement W f θ‖ ≤
      (contourCauchyShapeUniformIntegralConstant (γ : ℝ) c M * ‖Z - W‖) * ‖f‖ := by
  rw [contourCauchyResidualIncrement_sub_eq_integral_shape Z W f hγ hc hZ hW θ]
  calc
    _ ≤ ∫ τ in Icc (-Real.pi) Real.pi,
        ((contourCauchyShapeUniformConstant c M * ‖Z - W‖) * (‖f‖ * Real.pi ^ (γ : ℝ))) *
          |τ| ^ ((γ : ℝ) - 1) := by
      apply norm_integral_le_of_norm_le ((integrableOn_abs_rpow_sub_one hγ Real.pi_pos.le).const_mul _)
      filter_upwards [ae_restrict_mem measurableSet_Icc] with τ hτ
      exact norm_contourCauchyShapeIntegrand_le hγ Z W f hc hM hZ hW hWM (abs_le.mpr hτ)
    _ = _ := by
      rw [integral_const_mul, integral_abs_rpow_sub_one hγ Real.pi_pos.le]
      unfold contourCauchyShapeUniformIntegralConstant
      ring

theorem integrableOn_contourCauchyShapeIntegrand {γ : ℝ≥0}
    (hγ : 0 < (γ : ℝ)) (Z W : ContourC1Space γ) (f : ContourHolderSpace γ)
    {c : ℝ} (hc : 0 < c)
    (hZ : ContourC1Space.HasChordArcLower Z c) (hW : ContourC1Space.HasChordArcLower W c) (θ : ℝ) :
    IntegrableOn (contourCauchyShapeIntegrand Z W f θ) (Icc (-Real.pi) Real.pi) := by
  apply ((integrableOn_contourC1CauchyResidualIncrementIntegrand Z f hγ hc hZ θ).sub
    (integrableOn_contourC1CauchyResidualIncrementIntegrand W f hγ hc hW θ)).congr
  filter_upwards [] with τ
  dsimp only [contourCauchyShapeIntegrand, contourCauchyResidualIncrementIntegrand, Pi.sub_apply]
  ring

theorem norm_contourC1CauchyResidualIncrement_shape_parameter_sub_le {γ : ℝ≥0}
    (hγ : 0 < (γ : ℝ)) (Z W : ContourC1Space γ) (f : ContourHolderSpace γ)
    {c M : ℝ} (hc : 0 < c) (hM : 0 ≤ M)
    (hZ : ContourC1Space.HasChordArcLower Z c) (hW : ContourC1Space.HasChordArcLower W c)
    (hZM : ‖Z‖ ≤ M) (hWM : ‖W‖ ≤ M) (θ η : ℝ) :
    ‖(contourC1CauchyResidualIncrement Z f θ - contourC1CauchyResidualIncrement W f θ) -
      (contourC1CauchyResidualIncrement Z f η - contourC1CauchyResidualIncrement W f η)‖ ≤
      ((contourCauchyShapeHolderIntegralConstant (γ : ℝ) c M * ‖Z - W‖) * ‖f‖) *
        |θ - η| ^ (γ : ℝ) := by
  rw [contourCauchyResidualIncrement_sub_eq_integral_shape Z W f hγ hc hZ hW θ,
    contourCauchyResidualIncrement_sub_eq_integral_shape Z W f hγ hc hZ hW η,
    ← integral_sub (integrableOn_contourCauchyShapeIntegrand hγ Z W f hc hZ hW θ)
      (integrableOn_contourCauchyShapeIntegrand hγ Z W f hc hZ hW η)]
  calc
    _ ≤ ∫ τ in Icc (-Real.pi) Real.pi,
        (((2 * contourCauchyShapeUniformConstant c M + contourCauchyShapeParameterConstant c M) *
          ‖Z - W‖ * ‖f‖) * |θ - η| ^ (γ : ℝ)) * |τ| ^ ((γ : ℝ) - 1) := by
      apply norm_integral_le_of_norm_le ((integrableOn_abs_rpow_sub_one hγ Real.pi_pos.le).const_mul _)
      filter_upwards [ae_restrict_mem measurableSet_Icc] with τ hτ
      exact norm_contourCauchyShapeIntegrand_parameter_sub_le hγ Z W f hc hM hZ hW hZM hWM
        (abs_le.mpr hτ)
    _ = _ := by
      rw [integral_const_mul, integral_abs_rpow_sub_one hγ Real.pi_pos.le]
      unfold contourCauchyShapeHolderIntegralConstant
      ring

end Euler2D

end
