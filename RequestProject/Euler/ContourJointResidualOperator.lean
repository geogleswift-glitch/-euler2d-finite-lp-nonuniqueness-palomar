module

public import RequestProject.Euler.ContourJointResidualKernel

/-! The actual joint remainder integral is a bounded complex bilinear
operator. Its values are obtained from scalar integrals and proved
Hölder bounds, without assuming strong measurability in a nonseparable
Hölder space. -/

@[expose] public section

noncomputable section

open Set Filter Topology MeasureTheory
open scoped NNReal ENNReal

namespace Euler2D

def contourJointResidualOperatorConstant (γ : ℝ) : ℝ :=
  4 * (2 * Real.pi ^ γ / γ)

theorem contourJointResidualOperatorConstant_nonneg {γ : ℝ} (hγ : 0 < γ) :
    0 ≤ contourJointResidualOperatorConstant γ := by
  unfold contourJointResidualOperatorConstant
  positivity

theorem holderWith_contourJointResidualIntegral {γ : ℝ≥0} (hγ : 0 < (γ : ℝ))
    (r : ContourJointHolderSpace γ) (f : ContourHolderSpace γ) :
    HolderWith (⟨contourJointResidualOperatorConstant (γ : ℝ) * ‖r‖ * ‖f‖,
      by have hc := contourJointResidualOperatorConstant_nonneg hγ; positivity⟩ : ℝ≥0) γ
      (contourJointResidualIntegral r f) := by
  let C : ℝ≥0 := ⟨contourJointResidualOperatorConstant (γ : ℝ) * ‖r‖ * ‖f‖,
    by have hc := contourJointResidualOperatorConstant_nonneg hγ; positivity⟩
  change HolderWith C γ (contourJointResidualIntegral r f)
  intro x y
  rw [edist_nndist, edist_nndist, ← ENNReal.coe_rpow_of_nonneg _ γ.coe_nonneg,
    ← ENNReal.coe_mul, ENNReal.coe_le_coe]
  have hb : dist (contourJointResidualIntegral r f x) (contourJointResidualIntegral r f y) ≤
      (contourJointResidualOperatorConstant (γ : ℝ) * ‖r‖ * ‖f‖) * dist x y ^ (γ : ℝ) := by
    rw [dist_eq_norm]
    exact (norm_contourJointResidualIntegral_parameter_sub_le hγ r f x y).trans_eq (by
      unfold contourJointResidualOperatorConstant
      ring)
  change dist (contourJointResidualIntegral r f x) (contourJointResidualIntegral r f y) ≤
    (C : ℝ) * dist x y ^ (γ : ℝ) at hb
  exact_mod_cast hb

def contourJointResidualHolder {γ : ℝ≥0} (hγ : 0 < (γ : ℝ))
    (r : ContourJointHolderSpace γ) (f : ContourHolderSpace γ) : ContourHolderSpace γ :=
  contourHolderOfMemHolder (by exact_mod_cast hγ) (contourJointResidualIntegral r f)
    (holderWith_contourJointResidualIntegral hγ r f).memHolder

@[simp] theorem contourJointResidualHolder_apply {γ : ℝ≥0} (hγ : 0 < (γ : ℝ))
    (r : ContourJointHolderSpace γ) (f : ContourHolderSpace γ) (x : ContourCircle) :
    contourJointResidualHolder hγ r f x = contourJointResidualIntegral r f x := rfl

theorem norm_contourJointResidualHolder_le {γ : ℝ≥0} (hγ : 0 < (γ : ℝ))
    (r : ContourJointHolderSpace γ) (f : ContourHolderSpace γ) :
    ‖contourJointResidualHolder hγ r f‖ ≤
      contourJointResidualOperatorConstant (γ : ℝ) * ‖r‖ * ‖f‖ := by
  apply HolderFunctionSpace.norm_le_of_pointwise_holder_bounds
    (C := ⟨contourJointResidualOperatorConstant (γ : ℝ) * ‖r‖ * ‖f‖,
      by have hc := contourJointResidualOperatorConstant_nonneg hγ; positivity⟩)
  · intro x
    change ‖contourJointResidualIntegral r f x‖ ≤
      contourJointResidualOperatorConstant (γ : ℝ) * ‖r‖ * ‖f‖
    calc
      _ ≤ (2 * ‖r‖ * ‖f‖) * (2 * Real.pi ^ (γ : ℝ) / (γ : ℝ)) :=
        norm_contourJointResidualIntegral_le hγ r f x
      _ ≤ (4 * ‖r‖ * ‖f‖) * (2 * Real.pi ^ (γ : ℝ) / (γ : ℝ)) := by gcongr <;> norm_num
      _ = _ := by unfold contourJointResidualOperatorConstant; ring
  · exact holderWith_contourJointResidualIntegral hγ r f

attribute [local instance] HolderFunctionSpace.complexScalarNormedSpace
  HolderFunctionSpace.complexScalarTower

theorem contourJointResidualHolder_add_right {γ : ℝ≥0} (hγ : 0 < (γ : ℝ))
    (r : ContourJointHolderSpace γ) (f g : ContourHolderSpace γ) :
    contourJointResidualHolder hγ r (f + g) =
      contourJointResidualHolder hγ r f + contourJointResidualHolder hγ r g := by
  apply HolderFunctionSpace.ext
  intro x
  change contourJointResidualIntegral r (f + g) x =
    contourJointResidualIntegral r f x + contourJointResidualIntegral r g x
  rw [contourJointResidualIntegral, contourJointResidualIntegral, contourJointResidualIntegral,
    ← integral_add (integrableOn_contourJointResidualIntegrand hγ r f x)
      (integrableOn_contourJointResidualIntegrand hγ r g x)]
  apply integral_congr_ae
  exact ae_of_all _ (fun τ => by
    simp only [contourJointResidualIntegrand, contourDensityIncrement, HolderFunctionSpace.add_apply,
      Complex.real_smul]
    ring)

theorem contourJointResidualHolder_add_left {γ : ℝ≥0} (hγ : 0 < (γ : ℝ))
    (r s : ContourJointHolderSpace γ) (f : ContourHolderSpace γ) :
    contourJointResidualHolder hγ (r + s) f =
      contourJointResidualHolder hγ r f + contourJointResidualHolder hγ s f := by
  apply HolderFunctionSpace.ext
  intro x
  change contourJointResidualIntegral (r + s) f x =
    contourJointResidualIntegral r f x + contourJointResidualIntegral s f x
  rw [contourJointResidualIntegral, contourJointResidualIntegral, contourJointResidualIntegral,
    ← integral_add (integrableOn_contourJointResidualIntegrand hγ r f x)
      (integrableOn_contourJointResidualIntegrand hγ s f x)]
  apply integral_congr_ae
  exact ae_of_all _ (fun τ => by
    simp only [contourJointResidualIntegrand, contourJointSample, HolderFunctionSpace.add_apply,
      Complex.real_smul]
    ring)

theorem contourJointResidualHolder_smul_right {γ : ℝ≥0} (hγ : 0 < (γ : ℝ))
    (a : ℂ) (r : ContourJointHolderSpace γ) (f : ContourHolderSpace γ) :
    contourJointResidualHolder hγ r (a • f) = a • contourJointResidualHolder hγ r f := by
  apply HolderFunctionSpace.ext
  intro x
  change contourJointResidualIntegral r (a • f) x = a * contourJointResidualIntegral r f x
  rw [contourJointResidualIntegral, contourJointResidualIntegral, ← integral_const_mul]
  apply integral_congr_ae
  exact ae_of_all _ (fun τ => by
    simp only [contourJointResidualIntegrand, contourDensityIncrement,
      HolderFunctionSpace.complex_smul_apply, Complex.real_smul]
    ring)

theorem contourJointResidualHolder_smul_left {γ : ℝ≥0} (hγ : 0 < (γ : ℝ))
    (a : ℂ) (r : ContourJointHolderSpace γ) (f : ContourHolderSpace γ) :
    contourJointResidualHolder hγ (a • r) f = a • contourJointResidualHolder hγ r f := by
  apply HolderFunctionSpace.ext
  intro x
  change contourJointResidualIntegral (a • r) f x = a * contourJointResidualIntegral r f x
  rw [contourJointResidualIntegral, contourJointResidualIntegral, ← integral_const_mul]
  apply integral_congr_ae
  exact ae_of_all _ (fun τ => by
    simp only [contourJointResidualIntegrand, contourJointSample,
      HolderFunctionSpace.complex_smul_apply, Complex.real_smul]
    ring)

def contourJointResidualLinearMap {γ : ℝ≥0} (hγ : 0 < (γ : ℝ)) :
    ContourJointHolderSpace γ →ₗ[ℂ] ContourHolderSpace γ →ₗ[ℂ] ContourHolderSpace γ where
  toFun r :=
    { toFun := contourJointResidualHolder hγ r
      map_add' := contourJointResidualHolder_add_right hγ r
      map_smul' := fun a f => contourJointResidualHolder_smul_right hγ a r f }
  map_add' := fun r s => LinearMap.ext (fun f => contourJointResidualHolder_add_left hγ r s f)
  map_smul' := fun a r => LinearMap.ext (fun f => contourJointResidualHolder_smul_left hγ a r f)

/-- The actual complex bilinear integral operator, in the unchanged
genuine Hölder norms on source and target. -/
def contourJointResidualOperator {γ : ℝ≥0} (hγ : 0 < (γ : ℝ)) :
    ContourJointHolderSpace γ →L[ℂ] ContourHolderSpace γ →L[ℂ] ContourHolderSpace γ :=
  (contourJointResidualLinearMap hγ).mkContinuous₂
    (contourJointResidualOperatorConstant (γ : ℝ)) (norm_contourJointResidualHolder_le hγ)

@[simp] theorem contourJointResidualOperator_apply {γ : ℝ≥0} (hγ : 0 < (γ : ℝ))
    (r : ContourJointHolderSpace γ) (f : ContourHolderSpace γ) (x : ContourCircle) :
    contourJointResidualOperator hγ r f x = contourJointResidualIntegral r f x := rfl

theorem norm_contourJointResidualOperator_le {γ : ℝ≥0} (hγ : 0 < (γ : ℝ)) :
    ‖contourJointResidualOperator hγ‖ ≤ contourJointResidualOperatorConstant (γ : ℝ) :=
  LinearMap.mkContinuous₂_norm_le (contourJointResidualLinearMap hγ)
    (contourJointResidualOperatorConstant_nonneg hγ) (norm_contourJointResidualHolder_le hγ)

end Euler2D

end
