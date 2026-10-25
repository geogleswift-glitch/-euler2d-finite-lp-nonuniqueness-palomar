module

public import RequestProject.Euler.TorusTransport
public import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed

/-!
# Actual preservation of area in particle-map limits

Almost-everywhere pointwise limits of finite-measure-preserving maps
preserve their target measure. The physical torus statement is obtained
through the continuous quotient map, so wrapping across a face causes
no false continuity assumption.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace Euler2D

theorem measurePreserving_of_ae_tendsto {α β : Type*} [MeasurableSpace α]
    [MeasurableSpace β] [TopologicalSpace β] [BorelSpace β] [HasOuterApproxClosed β]
    {μ : Measure α} {ν : Measure β} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {F : ℕ → α → β} {G : α → β} (hF : ∀ n, MeasurePreserving (F n) μ ν)
    (hG : Measurable G) (hlim : ∀ᵐ a ∂μ, Tendsto (fun n => F n a) atTop (𝓝 (G a))) :
    MeasurePreserving G μ ν := by
  refine ⟨hG, ext_of_forall_integral_eq_of_IsFiniteMeasure fun φ => ?_⟩
  have hi : Tendsto (fun n => ∫ a, φ (F n a) ∂μ) atTop (𝓝 (∫ a, φ (G a) ∂μ)) := by
    apply tendsto_integral_of_dominated_convergence (fun _ => ‖φ‖)
      (fun n => (φ.continuous.measurable.comp (hF n).measurable).aestronglyMeasurable)
      (integrable_const _)
      (fun n => Eventually.of_forall fun a => φ.norm_coe_le_norm (F n a))
    filter_upwards [hlim] with a ha
    exact (φ.continuous.tendsto (G a)).comp ha
  have he (n : ℕ) : (∫ a, φ (F n a) ∂μ) = ∫ b, φ b ∂ν := by
    have hm := integral_map (hF n).aemeasurable φ.continuous.aestronglyMeasurable
    rw [(hF n).map_eq] at hm
    exact hm.symm
  have hc : Tendsto (fun n => ∫ a, φ (F n a) ∂μ) atTop (𝓝 (∫ b, φ b ∂ν)) :=
    tendsto_const_nhds.congr' (Eventually.of_forall fun n => (he n).symm)
  have hm := integral_map (μ := μ) hG.aemeasurable φ.continuous.aestronglyMeasurable
  rw [hm]
  exact tendsto_nhds_unique hi hc

lemma continuous_torusProj : Continuous torusProj := by
  apply continuous_pi
  intro i
  have hc : Continuous (fun r : ℝ => (r : UnitAddCircle)) := AddCircle.continuous_mk' (1 : ℝ)
  exact hc.comp ((EuclideanSpace.proj i : R2 →L[ℝ] ℝ).continuous.div_const (2 * Real.pi))

attribute [local instance] instMeasureSpaceUnitAddCircle

local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

theorem torusAreaPreserving_of_ae_tendsto {X : ℕ → R2 → R2} {Y : R2 → R2}
    (hX : ∀ n, TorusAreaPreserving (X n)) (hY : Measurable Y)
    (hlim : ∀ᵐ a ∂μT, Tendsto (fun n => X n a) atTop (𝓝 (Y a))) :
    TorusAreaPreserving Y := by
  let A : ENNReal := ENNReal.ofReal ((2 * Real.pi) ^ 2)
  have hA : A ≠ 0 := by dsimp only [A]; positivity
  have hAfin : A ≠ ∞ := ENNReal.ofReal_ne_top
  letI : IsFiniteMeasure (A • (volume : Measure (UnitAddTorus (Fin 2)))) := by
    constructor
    simp only [Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
    exact hAfin.lt_top
  have hproj (n : ℕ) : MeasurePreserving (torusProj ∘ X n) μT
      (A • (volume : Measure (UnitAddTorus (Fin 2)))) := by
    have hp := measurePreserving_torusProj.comp (hX n)
    have he : torusProj ∘ (torusWrap ∘ X n) = torusProj ∘ X n := by
      funext a
      exact torusProj_torusRep _
    change MeasurePreserving (torusProj ∘ (torusWrap ∘ X n)) μT _ at hp
    rw [he] at hp
    exact hp
  have hYproj : MeasurePreserving (torusProj ∘ Y) μT
      (A • (volume : Measure (UnitAddTorus (Fin 2)))) := by
    apply measurePreserving_of_ae_tendsto hproj (measurable_torusProj.comp hY)
    filter_upwards [hlim] with a ha
    exact (continuous_torusProj.tendsto (Y a)).comp ha
  have hrep : MeasurePreserving torusRep
      (A • (volume : Measure (UnitAddTorus (Fin 2)))) μT := by
    have hp := measurePreserving_torusRep.smul_measure A
    simpa only [A, smul_smul, ENNReal.mul_inv_cancel hA hAfin, one_smul] using hp
  exact hrep.comp hYproj

end Euler2D

end
