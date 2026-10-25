module

public import RequestProject.Euler.AnalyticContourComposition
public import RequestProject.Euler.CircularMaterialPhysicalForcing

/-! The actual exterior remainder is a genuine C¹ Hölder contour
forcing, with the correct eighth-moment spatial derivative budget.
This upgrades pointwise field estimates to the original contour norm. -/

@[expose] public section

set_option maxHeartbeats 1000000

noncomputable section

open Complex ComplexConjugate Set Filter Topology Metric MeasureTheory
open scoped NNReal BoundedContinuousFunction

namespace Euler2D

def exteriorFourthDerivativeBound (M₈ d : ℝ) (m : ℕ) : ℝ :=
  (m.factorial : ℝ) * (8 / (15 * Real.pi) * M₈ / (d / 2) ^ 9) / (d / 2) ^ m

theorem exteriorFourthDerivativeBound_nonneg {M₈ d : ℝ} (hM : 0 ≤ M₈) (hd : 0 < d) (m : ℕ) :
    0 ≤ exteriorFourthDerivativeBound M₈ d m := by
  unfold exteriorFourthDerivativeBound
  positivity

theorem analyticOnNhd_exteriorFourthRemainderCauchy
    {w : ℂ → ℝ} {S : ℝ} (hS : 0 ≤ S) (hw : Integrable w)
    (hsupp : ∀ y, S < ‖y‖ → w y = 0) :
    AnalyticOnNhd ℂ (exteriorFourthRemainderCauchy w) {z | S < ‖z‖} := by
  apply DifferentiableOn.analyticOnNhd _ (isOpen_lt continuous_const continuous_norm)
  intro z hz
  exact (differentiableAt_exteriorFourthRemainderCauchy hw hsupp hz
    (norm_pos_iff.mp (hS.trans_lt hz))).differentiableWithinAt

theorem exteriorFourth_iteratedDeriv_bound_on_target
    {w : ℂ → ℝ} {S M₈ d : ℝ} (hS : 0 ≤ S) (hw : Integrable w)
    (hsupp : ∀ y, S < ‖y‖ → w y = 0) (hmass : ∫ y, w y = 0)
    (hsym : ∀ y, w (I * y) = w y)
    (hM : (∫ y : ℂ, ‖y‖ ^ 8 * |w y|) ≤ M₈) (hd : 0 < d) (hsep : 4 * S ≤ d)
    {x : ℂ} (hx : d ≤ ‖x‖) (m : ℕ) :
    ‖iteratedDeriv m (exteriorFourthRemainderCauchy w) x‖ ≤
      exteriorFourthDerivativeBound M₈ d m := by
  have hx0 : x ≠ 0 := norm_pos_iff.mp (hd.trans_le hx)
  have hMn : 0 ≤ M₈ := (integral_nonneg (fun y => by positivity)).trans hM
  have hb := norm_iteratedDeriv_exteriorFourthRemainderCauchy hS hw hsupp hmass hsym hx0
    (hsep.trans hx) m
  refine hb.trans ?_
  unfold exteriorFourthDerivativeBound
  gcongr

def contourC1Conjugate {γ : ℝ≥0} (Z : ContourC1Space γ) : ContourC1Space γ :=
  ContourC1Space.ofHasDerivAt
    ((Complex.conjCLE : ℂ →L[ℝ] ℂ).compLeftContinuousBounded ContourCircle
      (ContourC1Space.toBCF γ Z))
    (HolderFunctionSpace.conjugate (ContourC1Space.derivative γ Z))
    (fun θ => Complex.conjCLE.hasFDerivAt.comp_hasDerivAt θ (ContourC1Space.hasDerivAt_lift Z θ))

@[simp] theorem lift_contourC1Conjugate {γ : ℝ≥0} (Z : ContourC1Space γ) (θ : ℝ) :
    ContourC1Space.lift γ (contourC1Conjugate Z) θ = conj (ContourC1Space.lift γ Z θ) := rfl

theorem norm_contourC1Conjugate_le {γ : ℝ≥0} (Z : ContourC1Space γ) :
    ‖contourC1Conjugate Z‖ ≤ ‖Z‖ := by
  apply max_le
  · apply (BoundedContinuousFunction.norm_le (norm_nonneg Z)).mpr
    intro x
    change ‖conj (ContourC1Space.toBCF γ Z x)‖ ≤ ‖Z‖
    rw [norm_conj]
    exact ContourC1Space.norm_eval_le Z x
  · exact (HolderFunctionSpace.norm_conjugate_le _).trans (ContourC1Space.norm_derivative_le Z)

/-- The original real physical field, evaluated on the actual target
contour, is an actual member of the original C¹ Hölder space. -/
theorem exists_exteriorContourRemainderC1 {γ : ℝ≥0} (hγ1 : (γ : ℝ) ≤ 1)
    {w : ℂ → ℝ} {S M₈ d : ℝ} (hS : 0 ≤ S) (hw : Integrable w)
    (hsupp : ∀ y, S < ‖y‖ → w y = 0) (hmass : ∫ y, w y = 0)
    (hsym : ∀ y, w (I * y) = w y)
    (hM : (∫ y : ℂ, ‖y‖ ^ 8 * |w y|) ≤ M₈) (hd : 0 < d) (hsep : 4 * S ≤ d)
    (Z : ContourC1Space γ) (hZ : ∀ x, d ≤ ‖ContourC1Space.toBCF γ Z x‖) :
    ∃ Q : ContourC1Space γ,
      (∀ θ, ContourC1Space.lift γ Q θ = exteriorFourthRemainder w (ContourC1Space.lift γ Z θ)) ∧
      ‖Q‖ ≤ max (exteriorFourthDerivativeBound M₈ d 0)
        (2 * (exteriorFourthDerivativeBound M₈ d 1 + Real.pi ^ (1 - (γ : ℝ)) *
          exteriorFourthDerivativeBound M₈ d 2 * ‖Z‖) * ‖Z‖) := by
  have hMn : 0 ≤ M₈ := (integral_nonneg (fun y => by positivity)).trans hM
  have hB (m : ℕ) := exteriorFourthDerivativeBound_nonneg hMn hd m
  have hF := analyticOnNhd_exteriorFourthRemainderCauchy hS hw hsupp
  have hZu : ∀ x, ContourC1Space.toBCF γ Z x ∈ {z : ℂ | S < ‖z‖} := by
    intro x
    have hx := hZ x
    change S < ‖ContourC1Space.toBCF γ Z x‖
    rcases eq_or_lt_of_le hS with hS0 | hS0
    · rw [← hS0]
      exact hd.trans_le hx
    · linarith
  have hder (m : ℕ) (x : ContourCircle) :=
    exteriorFourth_iteratedDeriv_bound_on_target hS hw hsupp hmass hsym hM hd hsep (hZ x) m
  have h₀ : ∀ x, ‖exteriorFourthRemainderCauchy w (ContourC1Space.toBCF γ Z x)‖ ≤
      exteriorFourthDerivativeBound M₈ d 0 := by simpa only [iteratedDeriv_zero] using hder 0
  have h₁ : ∀ x, ‖deriv (exteriorFourthRemainderCauchy w) (ContourC1Space.toBCF γ Z x)‖ ≤
      exteriorFourthDerivativeBound M₈ d 1 := by simpa only [iteratedDeriv_one] using hder 1
  have h₂ : ∀ x, ‖deriv (deriv (exteriorFourthRemainderCauchy w)) (ContourC1Space.toBCF γ Z x)‖ ≤
      exteriorFourthDerivativeBound M₈ d 2 := by
    simpa only [iteratedDeriv_succ, iteratedDeriv_zero] using hder 2
  let Q := analyticContourComposition hγ1 hF Z hZu (hB 2) h₂
  refine ⟨contourC1Conjugate Q, ?_, ?_⟩
  · intro θ
    rw [lift_contourC1Conjugate, show ContourC1Space.lift γ Q θ =
      exteriorFourthRemainderCauchy w (ContourC1Space.lift γ Z θ) from rfl]
    exact conj_conj _
  · exact (norm_contourC1Conjugate_le Q).trans
      (norm_analyticContourComposition_le hγ1 hF Z hZu (hB 0) (hB 1) (hB 2) h₀ h₁ h₂)

end Euler2D

end
