module

public import RequestProject.Euler.ContourC1Space

/-!
# The actual little C¹ Hölder contour Banach space

This is the closure of the actual smooth periodic loops in the genuine
C¹ Hölder norm.  Completeness and evaluation bounds follow from the
closed-subspace construction.  Smooth approximation is stated both in
the inherited equivalent norm and in the literal usual contour norm.
-/

@[expose] public section

noncomputable section

open Set Filter Topology Metric
open scoped NNReal ENNReal BoundedContinuousFunction ContDiff

namespace Euler2D

-- Short-circuit the generic submodule/topological-group instance search.
instance contourC1Space_topologicalAddGroup (γ : ℝ≥0) :
    IsTopologicalAddGroup (ContourC1Space γ) :=
  SeminormedAddCommGroup.toIsTopologicalAddGroup (E := ContourC1Space γ)

instance contourC1Space_continuousAdd (γ : ℝ≥0) : ContinuousAdd (ContourC1Space γ) :=
  (contourC1Space_topologicalAddGroup γ).toContinuousAdd

/-- Actual smooth loops that belong to the actual C¹ Hölder space. -/
def smoothContourSubmodule (γ : ℝ≥0) : Submodule ℝ (ContourC1Space γ) where
  carrier := {f | ContDiff ℝ ∞ (ContourC1Space.lift γ f)}
  zero_mem' := by
    change ContDiff ℝ ∞ (ContourC1Space.lift γ (0 : ContourC1Space γ))
    simpa only [ContourC1Space.lift_zero, Pi.zero_def] using
      (contDiff_const : ContDiff ℝ ∞ (fun _ : ℝ => (0 : ℂ)))
  add_mem' := by
    intro f g hf hg
    change ContDiff ℝ ∞ (ContourC1Space.lift γ f) at hf
    change ContDiff ℝ ∞ (ContourC1Space.lift γ g) at hg
    change ContDiff ℝ ∞ (ContourC1Space.lift γ (f + g))
    rw [ContourC1Space.lift_add]
    exact hf.add hg
  smul_mem' := by
    intro c f hf
    change ContDiff ℝ ∞ (ContourC1Space.lift γ f) at hf
    change ContDiff ℝ ∞ (ContourC1Space.lift γ (c • f))
    rw [ContourC1Space.lift_smul]
    exact contDiff_const.smul hf

/-- The genuine little Hölder space: the actual closure of smooth loops. -/
abbrev LittleContourSpace (γ : ℝ≥0) := (smoothContourSubmodule γ).topologicalClosure

-- The norm is precisely the restricted norm of the actual C¹ graph.
-- Naming it directly avoids repeatedly searching through two nested graphs.
instance littleContourSpace_norm (γ : ℝ≥0) : Norm (LittleContourSpace γ) :=
  ⟨fun f => ‖f.val‖⟩

theorem isClosed_littleContourSpace (γ : ℝ≥0) :
    IsClosed (LittleContourSpace γ : Set (ContourC1Space γ)) :=
  (smoothContourSubmodule γ).isClosed_topologicalClosure

instance littleContourSpace_complete (γ : ℝ≥0) : CompleteSpace (LittleContourSpace γ) :=
  (isClosed_littleContourSpace γ).completeSpace_coe

namespace LittleContourSpace

variable (γ : ℝ≥0)

/-- The actual inclusion into the C¹ Hölder contour space. -/
def inclusion : LittleContourSpace γ →L[ℝ] ContourC1Space γ :=
  (LittleContourSpace γ).subtypeL

def eval (x : ContourCircle) : LittleContourSpace γ →L[ℝ] ℂ :=
  (ContourC1Space.eval γ x).comp (inclusion γ)

def derivativeEval (x : ContourCircle) : LittleContourSpace γ →L[ℝ] ℂ :=
  (ContourC1Space.derivativeEval γ x).comp (inclusion γ)

def lift (f : LittleContourSpace γ) : ℝ → ℂ := ContourC1Space.lift γ f.val

/-- Every actual smooth C¹ Hölder loop is in the little space. -/
def ofSmooth (f : ContourC1Space γ) (hf : ContDiff ℝ ∞ (ContourC1Space.lift γ f)) :
    LittleContourSpace γ :=
  ⟨f, (smoothContourSubmodule γ).le_topologicalClosure hf⟩

@[simp] theorem inclusion_apply (f : LittleContourSpace γ) : inclusion γ f = f.val := rfl
@[simp] theorem inclusion_ofSmooth (f : ContourC1Space γ)
    (hf : ContDiff ℝ ∞ (ContourC1Space.lift γ f)) :
    inclusion γ (ofSmooth γ f hf) = f := rfl

variable {γ}

theorem contDiff_lift (f : LittleContourSpace γ) : ContDiff ℝ 1 (lift γ f) :=
  ContourC1Space.contDiff_lift f.val

theorem periodic_lift (f : LittleContourSpace γ) :
    Function.Periodic (lift γ f) (2 * Real.pi) := ContourC1Space.periodic_lift f.val

theorem hasDerivAt_lift (f : LittleContourSpace γ) (θ : ℝ) :
    HasDerivAt (lift γ f) (derivativeEval γ (θ : ContourCircle) f) θ :=
  ContourC1Space.hasDerivAt_lift f.val θ

lemma norm_eval_le (f : LittleContourSpace γ) (x : ContourCircle) :
    ‖eval γ x f‖ ≤ ‖f‖ := ContourC1Space.norm_eval_le f.val x

lemma norm_derivativeEval_le (f : LittleContourSpace γ) (x : ContourCircle) :
    ‖derivativeEval γ x f‖ ≤ ‖f‖ := ContourC1Space.norm_derivativeEval_le f.val x

/-- Little-space membership gives genuine smooth approximation. -/
theorem exists_smooth_approximation (f : LittleContourSpace γ) {ε : ℝ} (hε : 0 < ε) :
    ∃ g : ContourC1Space γ, ContDiff ℝ ∞ (ContourC1Space.lift γ g) ∧ ‖f.val - g‖ < ε := by
  have hcl : f.val ∈ closure (smoothContourSubmodule γ : Set (ContourC1Space γ)) := f.property
  obtain ⟨g, hg, hdist⟩ := Metric.mem_closure_iff.mp hcl ε hε
  refine ⟨g, hg, ?_⟩
  have heq : dist f.val g = ‖f.val - g‖ :=
    @dist_eq_norm (ContourC1Space γ) inferInstance f.val g
  rwa [← heq]

/-- The same actual smooth approximation in the literal usual contour norm. -/
theorem exists_smooth_standardNorm_approximation (f : LittleContourSpace γ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ g : ContourC1Space γ, ContDiff ℝ ∞ (ContourC1Space.lift γ g) ∧
      ContourC1Space.standardNorm (f.val - g) < ε := by
  obtain ⟨g, hg, hnorm⟩ := exists_smooth_approximation f (div_pos hε (by norm_num : (0:ℝ) < 3))
  refine ⟨g, hg, (ContourC1Space.standardNorm_le_three_norm _).trans_lt ?_⟩
  linarith

end LittleContourSpace

end Euler2D

end
