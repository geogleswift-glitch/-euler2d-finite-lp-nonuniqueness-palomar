module

public import Mathlib
public import Mathlib.Topology.MetricSpace.HolderNorm

/-!
# The actual Hölder Banach space for contour functions

A function is stored together with its genuine off-diagonal difference
quotient.  The equations defining that quotient are kernels of actual
continuous linear maps.  Their closed intersection is therefore complete
in the inherited product norm.  The first component is the function itself;
the second component is uniquely determined and bounds its Hölder modulus.
-/

@[expose] public section

noncomputable section

open Set Filter Topology Metric
open scoped NNReal ENNReal BoundedContinuousFunction

namespace Euler2D

variable (X E : Type*) [MetricSpace X] [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The actual pairs of distinct domain points. -/
abbrev HolderDifferencePair := {p : X × X // p.1 ≠ p.2}

abbrev HolderGraphAmbient := (X →ᵇ E) × (HolderDifferencePair X →ᵇ E)

/-- A difference-quotient equation at a fixed actual pair of distinct points. -/
def holderGraphOperator (γ : ℝ≥0) (p : HolderDifferencePair X) :
    HolderGraphAmbient X E →L[ℝ] E :=
  (BoundedContinuousFunction.evalCLM ℝ p).comp
      (ContinuousLinearMap.snd ℝ (X →ᵇ E) (HolderDifferencePair X →ᵇ E)) -
    (dist p.val.1 p.val.2 ^ (γ : ℝ))⁻¹ •
      (((BoundedContinuousFunction.evalCLM ℝ p.val.1 : (X →ᵇ E) →L[ℝ] E) -
          BoundedContinuousFunction.evalCLM ℝ p.val.2).comp
        (ContinuousLinearMap.fst ℝ (X →ᵇ E) (HolderDifferencePair X →ᵇ E)))

/-- The actual closed graph of all off-diagonal Hölder difference quotients. -/
def holderGraphSubmodule (γ : ℝ≥0) : Submodule ℝ (HolderGraphAmbient X E) :=
  ⨅ p : HolderDifferencePair X, (holderGraphOperator X E γ p).ker

theorem isClosed_holderGraphSubmodule (γ : ℝ≥0) :
    IsClosed (holderGraphSubmodule X E γ : Set (HolderGraphAmbient X E)) := by
  have hc : IsClosed (⋂ p : HolderDifferencePair X,
      {u : HolderGraphAmbient X E | holderGraphOperator X E γ p u = 0}) :=
    isClosed_iInter (fun p => isClosed_eq (holderGraphOperator X E γ p).continuous continuous_const)
  convert hc using 1
  ext u
  simp [holderGraphSubmodule]

/-- Genuine bounded Hölder functions, with their uniquely determined
difference quotient and the inherited complete norm. -/
abbrev HolderFunctionSpace (γ : ℝ≥0) := holderGraphSubmodule X E γ

instance holderFunctionSpace_complete [CompleteSpace E] (γ : ℝ≥0) :
    CompleteSpace (HolderFunctionSpace X E γ) :=
  (isClosed_holderGraphSubmodule X E γ).completeSpace_coe

variable {X E}

lemma holderFunctionSpace_quotient_eq {γ : ℝ≥0}
    (f : HolderFunctionSpace X E γ) (p : HolderDifferencePair X) :
    f.val.2 p = (dist p.val.1 p.val.2 ^ (γ : ℝ))⁻¹ •
      (f.val.1 p.val.1 - f.val.1 p.val.2) := by
  have hp := ((Submodule.mem_iInf _).mp f.property) p
  change holderGraphOperator X E γ p f.val = 0 at hp
  change f.val.2 p - (dist p.val.1 p.val.2 ^ (γ : ℝ))⁻¹ •
    (f.val.1 p.val.1 - f.val.1 p.val.2) = 0 at hp
  exact sub_eq_zero.mp hp

@[ext] theorem HolderFunctionSpace.ext {γ : ℝ≥0}
    {f g : HolderFunctionSpace X E γ} (h : ∀ x, f.val.1 x = g.val.1 x) : f = g := by
  apply Subtype.ext
  apply Prod.ext
  · exact BoundedContinuousFunction.ext h
  · apply BoundedContinuousFunction.ext
    intro p
    rw [holderFunctionSpace_quotient_eq, holderFunctionSpace_quotient_eq, h, h]

instance holderFunctionSpace_coeFun (γ : ℝ≥0) :
    CoeFun (HolderFunctionSpace X E γ) (fun _ => X → E) :=
  ⟨fun f => f.val.1⟩

namespace HolderFunctionSpace

variable (γ : ℝ≥0)

/-- The actual underlying function as a bounded continuous function. -/
def toBCF : HolderFunctionSpace X E γ →L[ℝ] (X →ᵇ E) :=
  (ContinuousLinearMap.fst ℝ (X →ᵇ E) (HolderDifferencePair X →ᵇ E)).comp
    (holderGraphSubmodule X E γ).subtypeL

/-- Evaluation is an actual continuous linear functional. -/
def eval (x : X) : HolderFunctionSpace X E γ →L[ℝ] E :=
  (BoundedContinuousFunction.evalCLM ℝ x).comp (toBCF γ)

@[simp] lemma toBCF_apply (f : HolderFunctionSpace X E γ) : toBCF γ f = f.val.1 := rfl

@[simp] lemma eval_apply (x : X) (f : HolderFunctionSpace X E γ) : eval γ x f = f x := rfl

@[simp] lemma zero_apply (x : X) : (0 : HolderFunctionSpace X E γ) x = 0 := rfl

@[simp] lemma add_apply (f g : HolderFunctionSpace X E γ) (x : X) :
    (f + g) x = f x + g x := rfl

@[simp] lemma smul_apply (c : ℝ) (f : HolderFunctionSpace X E γ) (x : X) :
    (c • f) x = c • f x := rfl

@[simp] lemma sub_apply (f g : HolderFunctionSpace X E γ) (x : X) :
    (f - g) x = f x - g x := rfl

variable {γ}

lemma norm_toBCF_le (f : HolderFunctionSpace X E γ) : ‖toBCF γ f‖ ≤ ‖f‖ := by
  change ‖f.val.1‖ ≤ max ‖f.val.1‖ ‖f.val.2‖
  exact le_max_left _ _

lemma norm_quotient_le (f : HolderFunctionSpace X E γ) : ‖f.val.2‖ ≤ ‖f‖ := by
  change ‖f.val.2‖ ≤ max ‖f.val.1‖ ‖f.val.2‖
  exact le_max_right _ _

lemma norm_eval_le (f : HolderFunctionSpace X E γ) (x : X) : ‖f x‖ ≤ ‖f‖ :=
  (f.val.1.norm_coe_le_norm x).trans (norm_toBCF_le f)

lemma norm_eval_operator_le (x : X) : ‖eval γ (E := E) x‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro f
  simpa only [eval_apply, one_mul] using norm_eval_le f x

/-- The actual uniform Hölder estimate encoded by the graph, using the
genuine metric distance on the domain. -/
theorem norm_sub_le_holder (f : HolderFunctionSpace X E γ) (x y : X) :
    ‖f x - f y‖ ≤ ‖f‖ * dist x y ^ (γ : ℝ) := by
  by_cases hxy : x = y
  · simp only [hxy, sub_self, norm_zero]
    exact mul_nonneg (norm_nonneg _) (Real.rpow_nonneg dist_nonneg _)
  let p : HolderDifferencePair X := ⟨(x, y), hxy⟩
  have hpow : 0 < dist x y ^ (γ : ℝ) := Real.rpow_pos_of_pos (dist_pos.mpr hxy) _
  have hq : ‖f.val.2 p‖ ≤ ‖f‖ :=
    (f.val.2.norm_coe_le_norm p).trans (norm_quotient_le f)
  rw [holderFunctionSpace_quotient_eq] at hq
  change ‖(dist x y ^ (γ : ℝ))⁻¹ • (f x - f y)‖ ≤ ‖f‖ at hq
  rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hpow] at hq
  apply (div_le_iff₀ hpow).mp
  simpa only [div_eq_mul_inv, mul_comm] using hq

/-- Membership in the constructed closed graph implies genuine Hölder
continuity, with the actual inherited norm as a Hölder constant. -/
theorem holderWith (f : HolderFunctionSpace X E γ) : HolderWith ‖f‖₊ γ (fun x => f x) := by
  intro x y
  rw [edist_nndist, edist_nndist,
    ← ENNReal.coe_rpow_of_nonneg _ γ.coe_nonneg, ← ENNReal.coe_mul, ENNReal.coe_le_coe]
  have hb : dist (f x) (f y) ≤ ‖f‖ * dist x y ^ (γ : ℝ) := by
    simpa only [dist_eq_norm] using norm_sub_le_holder f x y
  exact_mod_cast hb

theorem memHolder (f : HolderFunctionSpace X E γ) : MemHolder γ (fun x => f x) :=
  (holderWith f).memHolder

end HolderFunctionSpace

/-- The actual parameter circle, with its quotient (geodesic) metric. -/
abbrev ContourCircle := AddCircle (2 * Real.pi)

instance contourCircle_period_pos : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

/-- The actual complex-valued Hölder space on the parameter circle. -/
abbrev ContourHolderSpace (γ : ℝ≥0) := HolderFunctionSpace ContourCircle ℂ γ

end Euler2D

end
