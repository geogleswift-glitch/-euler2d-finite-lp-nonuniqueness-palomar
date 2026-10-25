module

public import RequestProject.Euler.ContourComplexHolderSpace
public import RequestProject.Euler.ContourHolderInverseAnalytic

/-! Genuine complex analyticity of the actual Hölder reciprocal, with
the unchanged norm and the explicitly activated complex scalar structure. -/

@[expose] public section

noncomputable section

open Set Filter Topology
open scoped NNReal

namespace Euler2D.HolderFunctionSpace

attribute [local instance] complexScalarNormedSpace
attribute [local instance] complexScalarTower

variable {X : Type*} [MetricSpace X] {γ : ℝ≥0}

def complexLeftMulUnit (f : HolderFunctionSpace X ℂ γ) {c : ℝ}
    (hc : 0 < c) (hf : ∀ x, c ≤ ‖f x‖) :
    (HolderFunctionSpace X ℂ γ →L[ℂ] HolderFunctionSpace X ℂ γ)ˣ where
  val := complexPointwiseMulCLM γ f
  inv := complexPointwiseMulCLM γ (inverseOfNormLower f hc hf)
  val_inv := by
    apply ContinuousLinearMap.ext
    intro g
    apply HolderFunctionSpace.ext
    intro x
    change f x * ((f x)⁻¹ * g x) = g x
    rw [← mul_assoc, mul_inv_cancel₀ (norm_pos_iff.mp (hc.trans_le (hf x))), one_mul]
  inv_val := by
    apply ContinuousLinearMap.ext
    intro g
    apply HolderFunctionSpace.ext
    intro x
    change (f x)⁻¹ * (f x * g x) = g x
    rw [← mul_assoc, inv_mul_cancel₀ (norm_pos_iff.mp (hc.trans_le (hf x))), one_mul]

def complexReciprocal (γ : ℝ≥0) (f : HolderFunctionSpace X ℂ γ) : HolderFunctionSpace X ℂ γ :=
  Ring.inverse (complexPointwiseMulCLM γ f) (const γ 1)

theorem complexReciprocal_eq_inverseOfNormLower (f : HolderFunctionSpace X ℂ γ)
    {c : ℝ} (hc : 0 < c) (hf : ∀ x, c ≤ ‖f x‖) :
    complexReciprocal γ f = inverseOfNormLower f hc hf := by
  have hi : Ring.inverse (complexPointwiseMulCLM γ f) =
      complexPointwiseMulCLM γ (inverseOfNormLower f hc hf) :=
    Ring.inverse_unit (complexLeftMulUnit f hc hf)
  unfold complexReciprocal
  rw [hi]
  apply HolderFunctionSpace.ext
  intro x
  change (f x)⁻¹ * 1 = (f x)⁻¹
  exact mul_one _

theorem complexReciprocal_eq_reciprocal (f : HolderFunctionSpace X ℂ γ)
    {c : ℝ} (hc : 0 < c) (hf : ∀ x, c ≤ ‖f x‖) : complexReciprocal γ f = reciprocal γ f :=
  (complexReciprocal_eq_inverseOfNormLower f hc hf).trans
    (reciprocal_eq_inverseOfNormLower f hc hf).symm

theorem complexReciprocal_apply (f : HolderFunctionSpace X ℂ γ) {c : ℝ}
    (hc : 0 < c) (hf : ∀ x, c ≤ ‖f x‖) (x : X) : complexReciprocal γ f x = (f x)⁻¹ := by
  rw [complexReciprocal_eq_inverseOfNormLower f hc hf]
  rfl

private theorem complex_analyticAt_inverseOperator_eval {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]
    (L : V →L[ℂ] (V →L[ℂ] V)) (f e : V) (U : (V →L[ℂ] V)ˣ) (hU : U.val = L f) :
    AnalyticAt ℂ (fun g => Ring.inverse (L g) e) f := by
  have hi : AnalyticAt ℂ Ring.inverse (L f) := by
    rw [← hU]
    exact analyticAt_inverse (𝕜 := ℂ) U
  have hm : AnalyticAt ℂ (fun g : V => Ring.inverse (L g)) f := hi.comp (L.analyticAt f)
  have he : AnalyticAt ℂ (ContinuousLinearMap.apply ℂ V e) (Ring.inverse (L f)) :=
    (ContinuousLinearMap.apply ℂ V e).analyticAt _
  exact (he.comp (f := fun g : V => Ring.inverse (L g)) hm).congr
    (Eventually.of_forall (fun _ => rfl))

theorem analyticAt_complexReciprocal (f : HolderFunctionSpace X ℂ γ) {c : ℝ}
    (hc : 0 < c) (hf : ∀ x, c ≤ ‖f x‖) : AnalyticAt ℂ (complexReciprocal γ) f := by
  exact (complex_analyticAt_inverseOperator_eval (complexPointwiseMulCLM (X := X) γ)
    f (const (X := X) γ 1) (complexLeftMulUnit f hc hf) rfl).congr
      (Eventually.of_forall (fun _ => rfl))

end Euler2D.HolderFunctionSpace

end
