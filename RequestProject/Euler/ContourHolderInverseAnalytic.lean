module

public import RequestProject.Euler.ContourHolderInverseContinuity
public import RequestProject.Euler.ContourHolderScalar
public import Mathlib.Analysis.Analytic.Constructions

/-!
# Actual real analyticity of Hölder inversion and boundary phases

The actual bounded pointwise product sends a Hölder function to its left
multiplication operator.  A genuine positive pointwise lower bound gives
an explicit inverse operator, namely multiplication by the actual reciprocal.
Analytic inversion in the standard Banach endomorphism ring, evaluated on
the actual constant function one, therefore gives actual Hölder inversion.
No equivalent norm or assumed Banach-algebra structure is used.
-/

@[expose] public section

noncomputable section

open Set Filter Topology
open scoped NNReal ComplexConjugate ContDiff

namespace Euler2D.HolderFunctionSpace

variable {X : Type*} [MetricSpace X] {γ : ℝ≥0}

/-- The true bounded multiplication operator, as an actual unit in the
real Banach ring of continuous endomorphisms. -/
def leftMulUnit (f : HolderFunctionSpace X ℂ γ) {c : ℝ}
    (hc : 0 < c) (hf : ∀ x, c ≤ ‖f x‖) :
    (HolderFunctionSpace X ℂ γ →L[ℝ] HolderFunctionSpace X ℂ γ)ˣ where
  val := pointwiseMulCLM γ f
  inv := pointwiseMulCLM γ (inverseOfNormLower f hc hf)
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

@[simp] theorem leftMulUnit_val (f : HolderFunctionSpace X ℂ γ) {c : ℝ}
    (hc : 0 < c) (hf : ∀ x, c ≤ ‖f x‖) :
    (leftMulUnit f hc hf).val = pointwiseMulCLM γ f := rfl

/-- A total presentation of the genuine reciprocal on its open domain.
Its value elsewhere is immaterial to the local analyticity theorem. -/
def reciprocal (γ : ℝ≥0) (f : HolderFunctionSpace X ℂ γ) : HolderFunctionSpace X ℂ γ :=
  Ring.inverse (pointwiseMulCLM γ f) (const γ 1)

theorem reciprocal_eq_inverseOfNormLower (f : HolderFunctionSpace X ℂ γ) {c : ℝ}
    (hc : 0 < c) (hf : ∀ x, c ≤ ‖f x‖) :
    reciprocal γ f = inverseOfNormLower f hc hf := by
  have hi : Ring.inverse (pointwiseMulCLM γ f) =
      pointwiseMulCLM γ (inverseOfNormLower f hc hf) :=
    Ring.inverse_unit (leftMulUnit f hc hf)
  unfold reciprocal
  rw [hi]
  apply HolderFunctionSpace.ext
  intro x
  change (f x)⁻¹ * 1 = (f x)⁻¹
  exact mul_one _

theorem reciprocal_apply (f : HolderFunctionSpace X ℂ γ) {c : ℝ}
    (hc : 0 < c) (hf : ∀ x, c ≤ ‖f x‖) (x : X) :
    reciprocal γ f x = (f x)⁻¹ := by
  rw [reciprocal_eq_inverseOfNormLower f hc hf]
  rfl

private theorem analyticAt_inverseOperator_eval {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    (L : V →L[ℝ] (V →L[ℝ] V)) (f e : V) (U : (V →L[ℝ] V)ˣ) (hU : U.val = L f) :
    AnalyticAt ℝ (fun g => Ring.inverse (L g) e) f := by
  have hi : AnalyticAt ℝ Ring.inverse (L f) := by
    rw [← hU]
    exact analyticAt_inverse (𝕜 := ℝ) U
  have hm : AnalyticAt ℝ (fun g : V => Ring.inverse (L g)) f :=
    hi.comp (L.analyticAt f)
  have he : AnalyticAt ℝ (ContinuousLinearMap.apply ℝ V e) (Ring.inverse (L f)) :=
    (ContinuousLinearMap.apply ℝ V e).analyticAt _
  exact (he.comp (f := fun g : V => Ring.inverse (L g)) hm).congr
    (Eventually.of_forall (fun _ => rfl))

/-- Real analyticity of the actual reciprocal in the genuine Hölder norm. -/
theorem analyticAt_reciprocal (f : HolderFunctionSpace X ℂ γ) {c : ℝ}
    (hc : 0 < c) (hf : ∀ x, c ≤ ‖f x‖) : AnalyticAt ℝ (reciprocal γ) f := by
  exact (analyticAt_inverseOperator_eval (pointwiseMulCLM (X := X) γ)
    f (const (X := X) γ 1) (leftMulUnit f hc hf) rfl).congr
      (Eventually.of_forall (fun _ => rfl))

/-- The total local presentation of the true phase `conj f / f`. -/
def phase (γ : ℝ≥0) (f : HolderFunctionSpace X ℂ γ) : HolderFunctionSpace X ℂ γ :=
  pointwiseMul (conjugate f) (reciprocal γ f)

theorem phase_eq_phaseOfNormLower (f : HolderFunctionSpace X ℂ γ) {c : ℝ}
    (hc : 0 < c) (hf : ∀ x, c ≤ ‖f x‖) :
    phase γ f = phaseOfNormLower f hc hf := by
  unfold phase phaseOfNormLower
  rw [reciprocal_eq_inverseOfNormLower f hc hf]

theorem phase_apply (f : HolderFunctionSpace X ℂ γ) {c : ℝ}
    (hc : 0 < c) (hf : ∀ x, c ≤ ‖f x‖) (x : X) :
    phase γ f x = conj (f x) / f x := by
  rw [phase_eq_phaseOfNormLower f hc hf, phaseOfNormLower_apply]

/-- Real analyticity of the actual boundary phase in the genuine Hölder
norm, proved from the constructed multiplication and reciprocal. -/
theorem analyticAt_phase (f : HolderFunctionSpace X ℂ γ) {c : ℝ}
    (hc : 0 < c) (hf : ∀ x, c ≤ ‖f x‖) : AnalyticAt ℝ (phase γ) f := by
  have hcj : AnalyticAt ℝ (fun g : HolderFunctionSpace X ℂ γ => conjugate g) f :=
    ((conjugateCLM (X := X) γ).analyticAt f).congr (Eventually.of_forall (fun _ => rfl))
  have hp := hcj.prod (analyticAt_reciprocal f hc hf)
  exact (((pointwiseMulCLM (X := X) γ).analyticAt_bilinear (conjugate f, reciprocal γ f)).comp
    (f := fun g : HolderFunctionSpace X ℂ γ => (conjugate g, reciprocal γ g)) hp).congr
    (Eventually.of_forall (fun _ => rfl))

theorem contDiffAt_reciprocal (f : HolderFunctionSpace X ℂ γ) {c : ℝ}
    (hc : 0 < c) (hf : ∀ x, c ≤ ‖f x‖) (n : WithTop ℕ∞) :
    ContDiffAt ℝ n (reciprocal γ) f := (analyticAt_reciprocal f hc hf).contDiffAt

theorem contDiffAt_phase (f : HolderFunctionSpace X ℂ γ) {c : ℝ}
    (hc : 0 < c) (hf : ∀ x, c ≤ ‖f x‖) (n : WithTop ℕ∞) :
    ContDiffAt ℝ n (phase γ) f := (analyticAt_phase f hc hf).contDiffAt

end Euler2D.HolderFunctionSpace

end
