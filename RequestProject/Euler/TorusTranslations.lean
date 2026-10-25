module

public import RequestProject.Euler.TorusTransport

/-!
# Actual area preservation of periodic translations and reflections

The physical representative maps are obtained from normalized Haar
translations through the exact area-scaled quotient correspondence.
This provides the change of variables needed for periodic convolution.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace Euler2D

attribute [local instance] instMeasureSpaceUnitAddCircle

local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)

local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

local instance : Measure.IsNegInvariant (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsNegInvariant AddCircle.haarAddCircle)

lemma torusProj_add (x y : R2) : torusProj (x + y) = torusProj x + torusProj y := by
  ext i
  simp only [torusProj, PiLp.add_apply, add_div, AddCircle.coe_add, Pi.add_apply]

lemma torusProj_neg (x : R2) : torusProj (-x) = -torusProj x := by
  ext i
  simp only [torusProj, PiLp.neg_apply, neg_div, AddCircle.coe_neg, Pi.neg_apply]

lemma torusProj_sub (x y : R2) : torusProj (x - y) = torusProj x - torusProj y := by
  simp only [sub_eq_add_neg, torusProj_add, torusProj_neg]

/-- Any genuine Haar-preserving quotient map gives an area-preserving
fundamental-domain representative, with the physical area retained. -/
theorem torusAreaPreserving_of_quotient {X : R2 → R2}
    (F : UnitAddTorus (Fin 2) → UnitAddTorus (Fin 2))
    (hF : MeasurePreserving F volume volume)
    (hproj : ∀ x, torusProj (X x) = F (torusProj x)) : TorusAreaPreserving X := by
  let A : ENNReal := ENNReal.ofReal ((2 * Real.pi) ^ 2)
  have hA : A ≠ 0 := by dsimp only [A]; positivity
  have hAfin : A ≠ ∞ := ENNReal.ofReal_ne_top
  have hrep : MeasurePreserving torusRep
      (A • (volume : Measure (UnitAddTorus (Fin 2)))) μT := by
    have h := measurePreserving_torusRep.smul_measure A
    simpa only [A, smul_smul, ENNReal.mul_inv_cancel hA hAfin, one_smul] using h
  have hcomp := hrep.comp ((hF.smul_measure A).comp measurePreserving_torusProj)
  have heq : torusWrap ∘ X = torusRep ∘ F ∘ torusProj := by
    funext x
    change torusRep (torusProj (X x)) = torusRep (F (torusProj x))
    rw [hproj]
  change MeasurePreserving (torusWrap ∘ X) μT μT
  rw [heq]
  exact hcomp

theorem torusAreaPreserving_add_right (a : R2) :
    TorusAreaPreserving (fun x => x + a) := by
  exact torusAreaPreserving_of_quotient (fun t => t + torusProj a)
    (measurePreserving_add_right volume (torusProj a)) (fun x => torusProj_add x a)

theorem torusAreaPreserving_sub_right (a : R2) :
    TorusAreaPreserving (fun x => x - a) := by
  simpa only [sub_eq_add_neg] using torusAreaPreserving_add_right (-a)

theorem torusAreaPreserving_sub_left (a : R2) :
    TorusAreaPreserving (fun x => a - x) := by
  exact torusAreaPreserving_of_quotient (fun t => torusProj a - t)
    (Measure.measurePreserving_sub_left volume (torusProj a))
    (fun x => by simp only [sub_eq_add_neg, torusProj_add, torusProj_neg])

end Euler2D

end
