module

public import RequestProject.Euler.ContourHolderNorm
public import Mathlib.Analysis.Calculus.UniformLimitsDeriv

/-!
# The actual complete C¹ Hölder space of periodic contours

The derivative is the derivative of the genuine real periodic lift, not an
independent formal variable.  Uniform convergence of functions and their
derivatives proves that its graph is closed.  The inherited max norm is
equivalent to the usual C¹ Hölder norm with explicit constants.
-/

@[expose] public section

noncomputable section

open Set Filter Topology Metric
open scoped NNReal ENNReal BoundedContinuousFunction

namespace Euler2D

abbrev ContourC1Ambient (γ : ℝ≥0) := (ContourCircle →ᵇ ℂ) × ContourHolderSpace γ

/-- The genuine graph of differentiation along the parameter circle. -/
def contourC1GraphSubmodule (γ : ℝ≥0) : Submodule ℝ (ContourC1Ambient γ) where
  carrier := {u | ∀ θ : ℝ, HasDerivAt (fun t : ℝ => u.1 (t : ContourCircle))
    (u.2 (θ : ContourCircle)) θ}
  zero_mem' := fun θ => hasDerivAt_const θ 0
  add_mem' := fun hf hg θ => (hf θ).add (hg θ)
  smul_mem' := fun c _ hf θ => (hf θ).const_smul c

/-- Differentiation is a closed operator in the actual uniform norms. -/
theorem isClosed_contourC1GraphSubmodule (γ : ℝ≥0) :
    IsClosed (contourC1GraphSubmodule γ : Set (ContourC1Ambient γ)) := by
  apply IsSeqClosed.isClosed
  intro u p hu hp
  have hf : Tendsto (fun n => (u n).1) atTop (𝓝 p.1) :=
    (continuous_fst.tendsto p).comp hp
  have hd : Tendsto (fun n => HolderFunctionSpace.toBCF γ (u n).2)
      atTop (𝓝 (HolderFunctionSpace.toBCF γ p.2)) :=
    (((HolderFunctionSpace.toBCF γ).continuous.comp continuous_snd).tendsto p).comp hp
  have hfu := (BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mp hf).comp
    (fun θ : ℝ => (θ : ContourCircle))
  have hdu := (BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mp hd).comp
    (fun θ : ℝ => (θ : ContourCircle))
  intro θ
  exact hasDerivAt_of_tendstoUniformly hdu (Eventually.of_forall hu) hfu.tendsto_at θ

/-- Actual complex-valued C¹ loops whose genuine derivative is Hölder. -/
abbrev ContourC1Space (γ : ℝ≥0) := contourC1GraphSubmodule γ

instance contourC1Space_complete (γ : ℝ≥0) : CompleteSpace (ContourC1Space γ) :=
  (isClosed_contourC1GraphSubmodule γ).completeSpace_coe

namespace ContourC1Space

variable (γ : ℝ≥0)

/-- The genuine underlying function on the quotient circle. -/
def toBCF : ContourC1Space γ →L[ℝ] (ContourCircle →ᵇ ℂ) :=
  (ContinuousLinearMap.fst ℝ (ContourCircle →ᵇ ℂ) (ContourHolderSpace γ)).comp
    (contourC1GraphSubmodule γ).subtypeL

/-- The genuine derivative as a Hölder function on the quotient circle. -/
def derivative : ContourC1Space γ →L[ℝ] ContourHolderSpace γ :=
  (ContinuousLinearMap.snd ℝ (ContourCircle →ᵇ ℂ) (ContourHolderSpace γ)).comp
    (contourC1GraphSubmodule γ).subtypeL

def eval (x : ContourCircle) : ContourC1Space γ →L[ℝ] ℂ :=
  (BoundedContinuousFunction.evalCLM ℝ x).comp (toBCF γ)

def derivativeEval (x : ContourCircle) : ContourC1Space γ →L[ℝ] ℂ :=
  (HolderFunctionSpace.eval γ x).comp (derivative γ)

/-- The actual 2π-periodic real lift, to be used in all contour integrals. -/
def lift (f : ContourC1Space γ) (θ : ℝ) : ℂ := toBCF γ f (θ : ContourCircle)

@[simp] lemma toBCF_apply (f : ContourC1Space γ) : toBCF γ f = f.val.1 := rfl
@[simp] lemma derivative_apply (f : ContourC1Space γ) : derivative γ f = f.val.2 := rfl
@[simp] lemma eval_apply (x : ContourCircle) (f : ContourC1Space γ) :
    eval γ x f = toBCF γ f x := rfl
@[simp] lemma derivativeEval_apply (x : ContourCircle) (f : ContourC1Space γ) :
    derivativeEval γ x f = derivative γ f x := rfl

variable {γ}

theorem hasDerivAt_lift (f : ContourC1Space γ) (θ : ℝ) :
    HasDerivAt (lift γ f) (derivative γ f (θ : ContourCircle)) θ := f.property θ

theorem deriv_lift (f : ContourC1Space γ) (θ : ℝ) :
    deriv (lift γ f) θ = derivative γ f (θ : ContourCircle) := (hasDerivAt_lift f θ).deriv

/-- The actual derivative is uniquely determined by the underlying loop. -/
@[ext] theorem ext {f g : ContourC1Space γ}
    (h : ∀ x, toBCF γ f x = toBCF γ g x) : f = g := by
  apply Subtype.ext
  apply Prod.ext
  · exact BoundedContinuousFunction.ext h
  · apply HolderFunctionSpace.ext
    intro x
    obtain ⟨θ, rfl⟩ := QuotientAddGroup.mk_surjective x
    have heq : lift γ f = lift γ g := funext (fun θ => h (θ : ContourCircle))
    have hd := hasDerivAt_lift f θ
    rw [heq] at hd
    exact hd.unique (hasDerivAt_lift g θ)

/-- Embed an actual function and its actual Hölder derivative. -/
def ofHasDerivAt (f : ContourCircle →ᵇ ℂ) (g : ContourHolderSpace γ)
    (hf : ∀ θ : ℝ, HasDerivAt (fun t : ℝ => f (t : ContourCircle))
      (g (θ : ContourCircle)) θ) : ContourC1Space γ := ⟨(f, g), hf⟩

@[simp] theorem lift_ofHasDerivAt (f : ContourCircle →ᵇ ℂ) (g : ContourHolderSpace γ)
    (hf : ∀ θ : ℝ, HasDerivAt (fun t : ℝ => f (t : ContourCircle))
      (g (θ : ContourCircle)) θ) (θ : ℝ) :
    lift γ (ofHasDerivAt f g hf) θ = f (θ : ContourCircle) := rfl

theorem contDiff_lift (f : ContourC1Space γ) : ContDiff ℝ 1 (lift γ f) := by
  apply contDiff_one_iff_deriv.mpr
  constructor
  · exact fun θ => (hasDerivAt_lift f θ).differentiableAt
  · have hd : deriv (lift γ f) = fun θ : ℝ => derivative γ f (θ : ContourCircle) :=
      funext (deriv_lift f)
    rw [hd]
    exact (HolderFunctionSpace.toBCF γ (derivative γ f)).continuous.comp
      (AddCircle.continuous_mk' (2 * Real.pi))

theorem periodic_lift (f : ContourC1Space γ) :
    Function.Periodic (lift γ f) (2 * Real.pi) := by
  intro θ
  exact congrArg (toBCF γ f) (AddCircle.coe_add_period (2 * Real.pi) θ)

@[simp] theorem lift_zero : lift γ (0 : ContourC1Space γ) = 0 := rfl
@[simp] theorem lift_add (f g : ContourC1Space γ) : lift γ (f + g) = lift γ f + lift γ g := rfl
@[simp] theorem lift_smul (c : ℝ) (f : ContourC1Space γ) : lift γ (c • f) = c • lift γ f := rfl
@[simp] theorem lift_sub (f g : ContourC1Space γ) : lift γ (f - g) = lift γ f - lift γ g := rfl

lemma norm_toBCF_le (f : ContourC1Space γ) : ‖toBCF γ f‖ ≤ ‖f‖ :=
  le_max_left _ _

lemma norm_derivative_le (f : ContourC1Space γ) : ‖derivative γ f‖ ≤ ‖f‖ :=
  le_max_right _ _

lemma norm_eval_le (f : ContourC1Space γ) (x : ContourCircle) :
    ‖eval γ x f‖ ≤ ‖f‖ :=
  ((toBCF γ f).norm_coe_le_norm x).trans (norm_toBCF_le f)

lemma norm_derivativeEval_le (f : ContourC1Space γ) (x : ContourCircle) :
    ‖derivativeEval γ x f‖ ≤ ‖f‖ :=
  (HolderFunctionSpace.norm_eval_le (derivative γ f) x).trans (norm_derivative_le f)

lemma norm_deriv_lift_le (f : ContourC1Space γ) (θ : ℝ) :
    ‖deriv (lift γ f) θ‖ ≤ ‖f‖ := by
  rw [deriv_lift]
  exact norm_derivativeEval_le f _

theorem norm_derivative_sub_le_holder (f : ContourC1Space γ) (x y : ContourCircle) :
    ‖derivative γ f x - derivative γ f y‖ ≤ ‖f‖ * dist x y ^ (γ : ℝ) :=
  (HolderFunctionSpace.norm_sub_le_holder (derivative γ f) x y).trans
    (mul_le_mul_of_nonneg_right (norm_derivative_le f) (Real.rpow_nonneg dist_nonneg _))

/-- The literal usual C¹ Hölder norm used for the contour chart. -/
def standardNorm (f : ContourC1Space γ) : ℝ :=
  ‖toBCF γ f‖ + ‖HolderFunctionSpace.toBCF γ (derivative γ f)‖ +
    (nnHolderNorm γ (fun x => derivative γ f x) : ℝ)

theorem norm_le_standardNorm (f : ContourC1Space γ) : ‖f‖ ≤ standardNorm f := by
  have hd := HolderFunctionSpace.norm_le_uniform_add_holder (derivative γ f)
  change max ‖toBCF γ f‖ ‖derivative γ f‖ ≤ _
  unfold standardNorm
  apply max_le
  · linarith [norm_nonneg (HolderFunctionSpace.toBCF γ (derivative γ f)),
      NNReal.coe_nonneg (nnHolderNorm γ (fun x => derivative γ f x))]
  · linarith [norm_nonneg (toBCF γ f)]

theorem standardNorm_le_three_norm (f : ContourC1Space γ) : standardNorm f ≤ 3 * ‖f‖ := by
  have hv := norm_toBCF_le f
  have hd := HolderFunctionSpace.uniform_add_holder_le_two_norm (derivative γ f)
  have hdn := norm_derivative_le f
  unfold standardNorm
  linarith

end ContourC1Space

end Euler2D

end
