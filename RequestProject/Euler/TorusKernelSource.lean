module

public import RequestProject.Euler.TorusPeriodization
public import RequestProject.Euler.TorusModel
public import RequestProject.Euler.CurlLimit

/-!
# The actual periodic source for the Green-kernel correction

A compact planar error is translated into the coordinate disk and
periodized as an actual smooth function. Its plane integral is retained
exactly. For mass minus one, subtracting the reciprocal torus area
produces the zero-mean Poisson source, with the physical normalization.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology Real
open scoped ContDiff

namespace Euler2D

attribute [local instance] instMeasureSpaceUnitAddCircle

local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

lemma torus_area_toReal : (μT univ).toReal = (2 * Real.pi) ^ 2 := by
  have h := integral_torusProj (fun _ : UnitAddTorus (Fin 2) => (1 : ℝ))
    (continuous_const.aestronglyMeasurable)
  simpa [Measure.real_def] using h

lemma norm_sub_center_lt_one_mem_box {x : R2} (hx : ‖x - torusCenter‖ < 1) : x ∈ torusBox := by
  intro i
  have hc : |x i - Real.pi| < 1 := by
    simpa only [PiLp.sub_apply, torusCenter_apply] using (abs_coord_le _ i).trans_lt hx
  have hcoord := abs_lt.mp hc
  constructor <;> linarith [Real.pi_gt_three]

def periodicCenteredSource (q : R2 → ℝ) : R2 → ℝ :=
  torusPeriodize (fun x => q (x - torusCenter))

lemma periodicCenteredSource_eq_on_box {q : R2 → ℝ}
    (hq : ∀ x, 1 ≤ ‖x‖ → q x = 0) {x : R2} (hx : x ∈ torusBox) :
    periodicCenteredSource q x = q (x - torusCenter) :=
  torusPeriodize_eq_on_box (fun _ hy => hq _ hy) hx

lemma isScalarTest_periodicCenteredSource {q : R2 → ℝ} (hq : ContDiff ℝ ∞ q)
    (hzero : ∀ x, 1 ≤ ‖x‖ → q x = 0) : IsScalarTest (periodicCenteredSource q) :=
  isScalarTest_torusPeriodize (hq.comp (contDiff_id.sub contDiff_const))
    (fun _ hx => hzero _ hx)

theorem integral_periodicCenteredSource {q : R2 → ℝ}
    (hzero : ∀ x, 1 ≤ ‖x‖ → q x = 0) :
    (∫ x in torusBox, periodicCenteredSource q x) = ∫ x, q x := by
  calc
    _ = ∫ x in torusBox, q (x - torusCenter) :=
      setIntegral_congr_fun measurableSet_torusBox (fun x hx => periodicCenteredSource_eq_on_box hzero hx)
    _ = ∫ x : R2, q (x - torusCenter) := by
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro x hx
      exact hzero _ (le_of_not_gt (fun hn => hx (norm_sub_center_lt_one_mem_box hn)))
    _ = ∫ x, q x := integral_sub_right_eq_self q torusCenter

def torusCorrectionSource (q : R2 → ℝ) (x : R2) : ℝ :=
  -periodicCenteredSource q x - ((2 * Real.pi) ^ 2)⁻¹

lemma isScalarTest_torusCorrectionSource {q : R2 → ℝ} (hq : ContDiff ℝ ∞ q)
    (hzero : ∀ x, 1 ≤ ‖x‖ → q x = 0) : IsScalarTest (torusCorrectionSource q) := by
  have hp := isScalarTest_periodicCenteredSource hq hzero
  exact ⟨hp.1.neg.sub contDiff_const, fun x i => by
    simp only [torusCorrectionSource, hp.2 x i]⟩

/-- The physical square has mass `(2π)²`, so the compensating constant
is exactly its reciprocal, rather than a normalized-Haar constant. -/
theorem integral_torusCorrectionSource {q : R2 → ℝ} (hq : ContDiff ℝ ∞ q)
    (hzero : ∀ x, 1 ≤ ‖x‖ → q x = 0) (hmass : (∫ x, q x) = -1) :
    (∫ x in torusBox, torusCorrectionSource q x) = 0 := by
  have hqInt : Integrable (periodicCenteredSource q) μT :=
    (continuous_memLp_torus (isScalarTest_periodicCenteredSource hq hzero).1.continuous 1).integrable le_rfl
  have hn : Integrable (fun x => -periodicCenteredSource q x) μT := hqInt.neg
  have hc : Integrable (fun _ : R2 => ((2 * Real.pi) ^ 2)⁻¹) μT := integrable_const _
  change (∫ x in torusBox, -periodicCenteredSource q x - ((2 * Real.pi) ^ 2)⁻¹) = 0
  rw [integral_sub hn hc, integral_neg,
    integral_periodicCenteredSource hzero, hmass, integral_const]
  simp only [smul_eq_mul, Measure.real, torus_area_toReal]
  field_simp [Real.pi_ne_zero]
  norm_num

end Euler2D

end
