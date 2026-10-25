module

public import RequestProject.Euler.TorusKernelSymmetry

/-!
# Actual torus-area preservation and convolution under a quarter-turn

The quotient rotation is a product-coordinate swap followed by one
circle negation.  Both preserve the actual normalized Haar measure;
the physical-area correspondence then retains `(2π)^2` exactly.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology Real
open scoped ContDiff ENNReal

namespace Euler2D

attribute [local instance] instMeasureSpaceUnitAddCircle

local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)

local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

local instance : Measure.IsNegInvariant (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsNegInvariant AddCircle.haarAddCircle)

def torusQuotientQuarterTurn (z : UnitAddTorus (Fin 2)) : UnitAddTorus (Fin 2) :=
  ![-z 1, z 0]

theorem measurePreserving_torusQuotientQuarterTurn :
    MeasurePreserving torusQuotientQuarterTurn volume volume := by
  let e : UnitAddTorus (Fin 2) ≃ᵐ (UnitAddCircle × UnitAddCircle) :=
    MeasurableEquiv.finTwoArrow
  have he : MeasurePreserving e volume volume := volume_preserving_finTwoArrow UnitAddCircle
  have hneg : MeasurePreserving (Neg.neg : UnitAddCircle → UnitAddCircle) volume volume :=
    Measure.measurePreserving_neg volume
  have hid : MeasurePreserving (id : UnitAddCircle → UnitAddCircle) volume volume :=
    MeasurePreserving.id volume
  have hp : MeasurePreserving (fun p : UnitAddCircle × UnitAddCircle => (-p.2, p.1))
      volume volume := (hneg.prod hid).comp Measure.measurePreserving_swap
  have hh := he.symm.comp (hp.comp he)
  have heq : torusQuotientQuarterTurn =
      (e.symm : UnitAddCircle × UnitAddCircle → UnitAddTorus (Fin 2)) ∘
        (fun p : UnitAddCircle × UnitAddCircle => (-p.2, p.1)) ∘ e := by
    funext z i
    fin_cases i <;> rfl
  rw [heq]
  exact hh

lemma torusQuarterTurn_zero (x : R2) : torusQuarterTurn x 0 = 2 * π - x 1 := by
  change π + -(x 1 - π) = 2 * π - x 1
  ring

lemma torusQuarterTurn_one (x : R2) : torusQuarterTurn x 1 = x 0 := by
  change π + (x 0 - π) = x 0
  ring

theorem torusProj_torusQuarterTurn (x : R2) :
    torusProj (torusQuarterTurn x) = torusQuotientQuarterTurn (torusProj x) := by
  funext i
  fin_cases i
  · change ((torusQuarterTurn x 0 / (2 * π) : ℝ) : UnitAddCircle) =
      -((x 1 / (2 * π) : ℝ) : UnitAddCircle)
    rw [torusQuarterTurn_zero]
    have he : (2 * π - x 1) / (2 * π) = -(x 1 / (2 * π)) + 1 := by
      rw [sub_div, div_self (by positivity : (2 * π : ℝ) ≠ 0)]
      ring
    rw [he, AddCircle.coe_add_period, AddCircle.coe_neg]
  · change ((torusQuarterTurn x 1 / (2 * π) : ℝ) : UnitAddCircle) =
      ((x 0 / (2 * π) : ℝ) : UnitAddCircle)
    rw [torusQuarterTurn_one]

theorem torusAreaPreserving_torusQuarterTurn : TorusAreaPreserving torusQuarterTurn :=
  torusAreaPreserving_of_quotient torusQuotientQuarterTurn
    measurePreserving_torusQuotientQuarterTurn torusProj_torusQuarterTurn

/-- Any actual periodic, bounded quarter-turn-invariant scalar source
has a quarter-turn-covariant velocity under the actual torus kernel. -/
theorem torusKernelVelocity_quarterTurn_of_invariant
    {w : R2 → ℝ} (hw : AEStronglyMeasurable w μT)
    {M : ℝ} (hM : ∀ᵐ y ∂μT, ‖w y‖ ≤ M)
    (hper : IsTorusPeriodic w) (hrot : ∀ y, w (torusQuarterTurn y) = w y) (x : R2) :
    torusKernelVelocity w (torusQuarterTurn x) = perpJ (torusKernelVelocity w x) := by
  let F : R2 → R2 := fun y => w y • torusBiotSavartKernel (torusQuarterTurn x - y + torusCenter)
  have hFi : Integrable F μT := integrable_torusKernelVelocity_integrand hw hM _
  have hFp : IsTorusPeriodic F := by
    intro y i
    dsimp only [F]
    rw [hper y i]
    congr 1
    have he : torusQuarterTurn x - (y + EuclideanSpace.single i (2 * π)) + torusCenter +
        EuclideanSpace.single i (2 * π) = torusQuarterTurn x - y + torusCenter := by abel
    have hp := isTorusPeriodic_torusBiotSavartKernel
      (torusQuarterTurn x - (y + EuclideanSpace.single i (2 * π)) + torusCenter) i
    rw [he] at hp
    exact hp.symm
  have hchange := torusAreaPreserving_torusQuarterTurn.integral_comp hFi.aestronglyMeasurable hFp
  calc
    _ = ∫ y in torusBox, F y := rfl
    _ = ∫ y in torusBox, F (torusQuarterTurn y) := hchange.symm
    _ = ∫ y in torusBox, perpJ (w y • torusBiotSavartKernel (x - y + torusCenter)) := by
      apply integral_congr_ae
      filter_upwards with y
      dsimp only [F]
      rw [hrot y, torusQuarterTurn_kernel_argument, torusBiotSavartKernel_quarterTurn, perpJ_smul]
    _ = _ := perpJL.integral_comp_comm (integrable_torusKernelVelocity_integrand hw hM x)

end Euler2D

end
