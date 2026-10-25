module

public import RequestProject.Euler.ContourCauchyShapeContinuity
public import RequestProject.Euler.ContourLogDerivativeHolder

/-! # Quantitative genuine Hölder shape bounds for the logarithmic derivative -/

@[expose] public section

noncomputable section

open Set Filter Topology Metric
open scoped NNReal ComplexConjugate

namespace Euler2D

open HolderFunctionSpace

local instance (priority := 2000) logShapeC1_normedAddCommGroup (γ : ℝ≥0) :
    NormedAddCommGroup (ContourC1Space γ) :=
  Submodule.normedAddCommGroup (contourC1GraphSubmodule γ)

theorem norm_conjugate_sub (γ : ℝ≥0) (f g : ContourHolderSpace γ) :
    ‖conjugate f - conjugate g‖ = ‖f - g‖ := by
  have he : conjugate f - conjugate g = conjugate (f - g) := by
    apply HolderFunctionSpace.ext
    intro x
    change conj (f x) - conj (g x) = conj (f x - g x)
    exact (map_sub _ _ _).symm
  rw [he, norm_conjugate]

def contourDerivativePhaseUniformConstant (c M : ℝ) : ℝ := 2 * M * inverseBound c M

theorem contourDerivativePhaseUniformConstant_nonneg {c M : ℝ} (hc : 0 < c) (hM : 0 ≤ M) :
    0 ≤ contourDerivativePhaseUniformConstant c M := by
  have hB := (inverseBound_pos hc M).le
  unfold contourDerivativePhaseUniformConstant
  positivity

theorem norm_contourDerivativePhase_le_uniform {γ : ℝ≥0}
    (Z : ContourC1Space γ) {c M : ℝ} (hc : 0 < c) (hM : 0 ≤ M)
    (hZ : ContourC1Space.HasChordArcLower Z c) (hZM : ‖Z‖ ≤ M) :
    ‖contourDerivativePhase Z hc hZ‖ ≤ contourDerivativePhaseUniformConstant c M := by
  have hd : ‖ContourC1Space.derivative γ Z‖ ≤ M := (ContourC1Space.norm_derivative_le Z).trans hZM
  have hi := norm_inverseOfNormLower_le_uniform (ContourC1Space.derivative γ Z) hc
    (contourC1_derivative_norm_lower Z hZ) hd
  have hB := (inverseBound_pos hc M).le
  unfold contourDerivativePhase divideOfNormLower
  apply (norm_pointwiseMul_le _ _).trans
  rw [norm_conjugate]
  exact mul_le_mul (mul_le_mul_of_nonneg_left hd (by norm_num)) hi (norm_nonneg _) (by positivity)

/-- The literal phase conj(Z')/Z' varies Lipschitz continuously in the
actual Hölder norm, under the true common chord and contour bounds. -/
theorem norm_contourDerivativePhase_shape_sub_le {γ : ℝ≥0}
    (Z W : ContourC1Space γ) {c M : ℝ} (hc : 0 < c) (hM : 0 ≤ M)
    (hZ : ContourC1Space.HasChordArcLower Z c) (hW : ContourC1Space.HasChordArcLower W c)
    (hZM : ‖Z‖ ≤ M) (hWM : ‖W‖ ≤ M) :
    ‖contourDerivativePhase Z hc hZ - contourDerivativePhase W hc hW‖ ≤
      contourCauchyShapeParameterConstant c M * ‖Z - W‖ := by
  apply norm_divideOfNormLower_sub_le_uniform _ _ _ _ hc hM
    (contourC1_derivative_norm_lower Z hZ) (contourC1_derivative_norm_lower W hW)
  · rw [norm_conjugate]
    exact (ContourC1Space.norm_derivative_le W).trans hWM
  · exact (ContourC1Space.norm_derivative_le Z).trans hZM
  · exact (ContourC1Space.norm_derivative_le W).trans hWM
  · rw [norm_conjugate_sub, ← map_sub]
    exact ContourC1Space.norm_derivative_le (Z - W)
  · rw [← map_sub]
    exact ContourC1Space.norm_derivative_le (Z - W)

theorem contourCauchyIncrementOperatorConstant_nonneg {γ c M : ℝ}
    (hγ : 0 < γ) (hγ1 : γ < 1) (hc : 0 < c) (hM : 0 ≤ M) :
    0 ≤ contourCauchyIncrementOperatorConstant γ M c :=
  add_nonneg (add_nonneg (contourRemainderUniformConstant_nonneg hγ hM hc Real.pi_pos.le)
    (contourRemainderHolderConstant_nonneg hγ hM hM hc Real.pi_pos.le))
    (hilbertOperatorConstant_nonneg hγ hγ1)

theorem norm_contourCauchyIncrementOperator_le_uniform {γ : ℝ≥0}
    (hγ : 0 < (γ : ℝ)) (hγ1 : (γ : ℝ) < 1) (Z : ContourC1Space γ)
    {c M : ℝ} (hc : 0 < c) (hM : 0 ≤ M)
    (hZ : ContourC1Space.HasChordArcLower Z c) (hZM : ‖Z‖ ≤ M) :
    ‖contourCauchyIncrementOperator Z hγ hγ1 hc hZ‖ ≤
      contourCauchyIncrementOperatorConstant (γ : ℝ) M c := by
  apply (norm_contourCauchyIncrementOperator_le Z hγ hγ1 hc hZ).trans
  unfold contourCauchyIncrementOperatorConstant contourRemainderUniformConstant contourRemainderHolderConstant
  gcongr

def contourCauchyPhaseShapeConstant (γ c M : ℝ) : ℝ :=
  contourCauchyShapeOperatorConstant γ c M * contourDerivativePhaseUniformConstant c M +
    contourCauchyIncrementOperatorConstant γ M c * contourCauchyShapeParameterConstant c M

theorem contourCauchyPhaseShapeConstant_nonneg {γ c M : ℝ}
    (hγ : 0 < γ) (hγ1 : γ < 1) (hc : 0 < c) (hM : 0 ≤ M) :
    0 ≤ contourCauchyPhaseShapeConstant γ c M :=
  add_nonneg (mul_nonneg (contourCauchyShapeOperatorConstant_nonneg hγ hc hM)
    (contourDerivativePhaseUniformConstant_nonneg hc hM))
    (mul_nonneg (contourCauchyIncrementOperatorConstant_nonneg hγ hγ1 hc hM)
      (contourCauchyShapeParameterConstant_nonneg hc hM))

theorem norm_contourCauchyIncrement_phase_shape_sub_le {γ : ℝ≥0}
    (hγ : 0 < (γ : ℝ)) (hγ1 : (γ : ℝ) < 1) (Z W : ContourC1Space γ)
    {c M : ℝ} (hc : 0 < c) (hM : 0 ≤ M)
    (hZ : ContourC1Space.HasChordArcLower Z c) (hW : ContourC1Space.HasChordArcLower W c)
    (hZM : ‖Z‖ ≤ M) (hWM : ‖W‖ ≤ M) :
    ‖contourCauchyIncrementOperator Z hγ hγ1 hc hZ (contourDerivativePhase Z hc hZ) -
      contourCauchyIncrementOperator W hγ hγ1 hc hW (contourDerivativePhase W hc hW)‖ ≤
      contourCauchyPhaseShapeConstant (γ : ℝ) c M * ‖Z - W‖ := by
  let AZ := contourCauchyIncrementOperator Z hγ hγ1 hc hZ
  let AW := contourCauchyIncrementOperator W hγ hγ1 hc hW
  let pZ := contourDerivativePhase Z hc hZ
  let pW := contourDerivativePhase W hc hW
  have hA := norm_contourCauchyIncrementOperator_shape_sub_le hγ hγ1 Z W hc hM hZ hW hZM hWM
  have hWop := norm_contourCauchyIncrementOperator_le_uniform hγ hγ1 W hc hM hW hWM
  have hp := norm_contourDerivativePhase_le_uniform Z hc hM hZ hZM
  have hpd := norm_contourDerivativePhase_shape_sub_le Z W hc hM hZ hW hZM hWM
  have hC := contourCauchyShapeOperatorConstant_nonneg hγ hc hM
  have hK := contourCauchyIncrementOperatorConstant_nonneg hγ hγ1 hc hM
  have he : AZ pZ - AW pW = (AZ - AW) pZ + AW (pZ - pW) := by
    rw [map_sub]
    change AZ pZ - AW pW = (AZ pZ - AW pZ) + (AW pZ - AW pW)
    abel
  change ‖AZ pZ - AW pW‖ ≤ _
  rw [he]
  calc
    _ ≤ ‖(AZ - AW) pZ‖ + ‖AW (pZ - pW)‖ := norm_add_le _ _
    _ ≤ ‖AZ - AW‖ * ‖pZ‖ + ‖AW‖ * ‖pZ - pW‖ :=
      add_le_add ((AZ - AW).le_opNorm _) (AW.le_opNorm _)
    _ ≤ (contourCauchyShapeOperatorConstant (γ : ℝ) c M * ‖Z - W‖) *
        contourDerivativePhaseUniformConstant c M +
      contourCauchyIncrementOperatorConstant (γ : ℝ) M c *
        (contourCauchyShapeParameterConstant c M * ‖Z - W‖) := by
      apply add_le_add
      · exact mul_le_mul hA hp (norm_nonneg _) (by positivity)
      · exact mul_le_mul hWop hpd (norm_nonneg _) hK
    _ = _ := by unfold contourCauchyPhaseShapeConstant; ring

theorem norm_contourHolder_pointwiseMul_sub_le {γ : ℝ≥0} (f g a b : ContourHolderSpace γ) :
    ‖pointwiseMul f a - pointwiseMul g b‖ ≤
      2 * ‖f - g‖ * ‖a‖ + 2 * ‖g‖ * ‖a - b‖ := by
  have he : pointwiseMul f a - pointwiseMul g b =
      pointwiseMul (f - g) a + pointwiseMul g (a - b) := by
    apply HolderFunctionSpace.ext
    intro x
    change f x * a x - g x * b x = (f x - g x) * a x + g x * (a x - b x)
    ring
  rw [he]
  exact (norm_add_le _ _).trans (add_le_add (norm_pointwiseMul_le _ _) (norm_pointwiseMul_le _ _))

def contourLogDerivativeShapeConstant (γ c M : ℝ) : ℝ :=
  contourCauchyIncrementOperatorConstant γ M c * contourDerivativePhaseUniformConstant c M +
    M * contourCauchyPhaseShapeConstant γ c M

theorem contourLogDerivativeShapeConstant_nonneg {γ c M : ℝ}
    (hγ : 0 < γ) (hγ1 : γ < 1) (hc : 0 < c) (hM : 0 ≤ M) :
    0 ≤ contourLogDerivativeShapeConstant γ c M :=
  add_nonneg (mul_nonneg (contourCauchyIncrementOperatorConstant_nonneg hγ hγ1 hc hM)
    (contourDerivativePhaseUniformConstant_nonneg hc hM))
    (mul_nonneg hM (contourCauchyPhaseShapeConstant_nonneg hγ hγ1 hc hM))

/-- A quantitative Hölder-norm Lipschitz estimate for the actual density
which has already been identified as the spatial derivative of self-log. -/
theorem norm_contourLogDerivativeHolder_shape_sub_le {γ : ℝ≥0}
    (hγ : 0 < (γ : ℝ)) (hγ1 : (γ : ℝ) < 1) (Z W : ContourC1Space γ)
    {c M : ℝ} (hc : 0 < c) (hM : 0 ≤ M)
    (hZ : ContourC1Space.HasChordArcLower Z c) (hW : ContourC1Space.HasChordArcLower W c)
    (hZM : ‖Z‖ ≤ M) (hWM : ‖W‖ ≤ M) :
    ‖contourLogDerivativeHolder Z hγ hγ1 hc hZ - contourLogDerivativeHolder W hγ hγ1 hc hW‖ ≤
      contourLogDerivativeShapeConstant (γ : ℝ) c M * ‖Z - W‖ := by
  let qZ := contourCauchyIncrementOperator Z hγ hγ1 hc hZ (contourDerivativePhase Z hc hZ)
  let qW := contourCauchyIncrementOperator W hγ hγ1 hc hW (contourDerivativePhase W hc hW)
  have hK := contourCauchyIncrementOperatorConstant_nonneg hγ hγ1 hc hM
  have hF := contourDerivativePhaseUniformConstant_nonneg hc hM
  have hD := contourCauchyPhaseShapeConstant_nonneg hγ hγ1 hc hM
  have hqZ : ‖qZ‖ ≤ contourCauchyIncrementOperatorConstant (γ : ℝ) M c *
      contourDerivativePhaseUniformConstant c M :=
    ((contourCauchyIncrementOperator Z hγ hγ1 hc hZ).le_opNorm _).trans
      (mul_le_mul (norm_contourCauchyIncrementOperator_le_uniform hγ hγ1 Z hc hM hZ hZM)
        (norm_contourDerivativePhase_le_uniform Z hc hM hZ hZM) (norm_nonneg _) hK)
  have hqdiff : ‖qZ - qW‖ ≤ contourCauchyPhaseShapeConstant (γ : ℝ) c M * ‖Z - W‖ :=
    norm_contourCauchyIncrement_phase_shape_sub_le hγ hγ1 Z W hc hM hZ hW hZM hWM
  have hd : ‖ContourC1Space.derivative γ Z - ContourC1Space.derivative γ W‖ ≤ ‖Z - W‖ := by
    rw [← map_sub]
    exact ContourC1Space.norm_derivative_le (Z - W)
  have hdW : ‖ContourC1Space.derivative γ W‖ ≤ M := (ContourC1Space.norm_derivative_le W).trans hWM
  unfold contourLogDerivativeHolder
  rw [← smul_sub, norm_smul]
  norm_num only [Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
  have hp := norm_contourHolder_pointwiseMul_sub_le
    (conjugate (ContourC1Space.derivative γ Z)) (conjugate (ContourC1Space.derivative γ W))
    (conjugate qZ) (conjugate qW)
  rw [norm_conjugate_sub, norm_conjugate, norm_conjugate, norm_conjugate_sub] at hp
  calc
    _ ≤ (1 / 2 : ℝ) * (2 * ‖ContourC1Space.derivative γ Z - ContourC1Space.derivative γ W‖ * ‖qZ‖ +
        2 * ‖ContourC1Space.derivative γ W‖ * ‖qZ - qW‖) :=
      mul_le_mul_of_nonneg_left hp (by norm_num)
    _ ≤ (1 / 2 : ℝ) * (2 * ‖Z - W‖ *
        (contourCauchyIncrementOperatorConstant (γ : ℝ) M c * contourDerivativePhaseUniformConstant c M) +
        2 * M * (contourCauchyPhaseShapeConstant (γ : ℝ) c M * ‖Z - W‖)) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply add_le_add
      · exact mul_le_mul (mul_le_mul_of_nonneg_left hd (by norm_num)) hqZ (norm_nonneg _) (by positivity)
      · exact mul_le_mul (mul_le_mul_of_nonneg_left hdW (by norm_num)) hqdiff (norm_nonneg _) (by positivity)
    _ = _ := by unfold contourLogDerivativeShapeConstant; ring

def contourLogDerivativeHolderOnShapeDomain {γ : ℝ≥0}
    (hγ : 0 < (γ : ℝ)) (hγ1 : (γ : ℝ) < 1) {c M : ℝ} (hc : 0 < c)
    (Z : ContourCauchyShapeDomain γ c M) : ContourHolderSpace γ :=
  contourLogDerivativeHolder Z.val hγ hγ1 hc Z.property.2

theorem lipschitzWith_contourLogDerivativeHolderOnShapeDomain {γ : ℝ≥0}
    (hγ : 0 < (γ : ℝ)) (hγ1 : (γ : ℝ) < 1) {c M : ℝ} (hc : 0 < c) (hM : 0 ≤ M) :
    LipschitzWith (⟨contourLogDerivativeShapeConstant (γ : ℝ) c M,
      contourLogDerivativeShapeConstant_nonneg hγ hγ1 hc hM⟩ : ℝ≥0)
      (contourLogDerivativeHolderOnShapeDomain hγ hγ1 (M := M) hc) := by
  apply LipschitzWith.of_dist_le_mul
  intro Z W
  change dist (contourLogDerivativeHolder Z.val hγ hγ1 hc Z.property.2)
      (contourLogDerivativeHolder W.val hγ hγ1 hc W.property.2) ≤
    contourLogDerivativeShapeConstant (γ : ℝ) c M * dist Z.val W.val
  rw [_root_.dist_eq_norm, _root_.dist_eq_norm]
  exact norm_contourLogDerivativeHolder_shape_sub_le hγ hγ1 Z.val W.val hc hM
    Z.property.2 W.property.2 Z.property.1 W.property.1

end Euler2D

end
