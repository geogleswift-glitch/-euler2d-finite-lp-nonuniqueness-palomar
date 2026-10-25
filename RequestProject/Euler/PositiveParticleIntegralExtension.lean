module

public import RequestProject.Euler.ParticleEquationLimit

/-! A genuine primitive for trajectories on all nonnegative times.
Continuous freezing of the derivative beyond time zero gives a true
two-sided derivative at zero as well. -/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal

namespace Euler2D

def positiveParticleVelocityExtension (v : ℝ≥0 → R2 → R2) (t : ℝ) (x : R2) : R2 :=
  v t.toNNReal x

def positiveParticleDerivative (v F : ℝ≥0 → R2 → R2) (t : ℝ) (a : R2) : R2 :=
  v t.toNNReal (F t.toNNReal a)

def positiveParticleIntegralExtension (v F : ℝ≥0 → R2 → R2) (t : ℝ) (a : R2) : R2 :=
  a + ∫ s in (0 : ℝ)..t, positiveParticleDerivative v F s a

theorem continuous_positiveParticleVelocityExtension {v : ℝ≥0 → R2 → R2}
    (hv : Continuous (Function.uncurry v)) :
    Continuous (Function.uncurry (positiveParticleVelocityExtension v)) :=
  hv.comp ((continuous_real_toNNReal.comp continuous_fst).prodMk continuous_snd)

theorem continuous_positiveParticleDerivative {v F : ℝ≥0 → R2 → R2}
    (hv : Continuous (Function.uncurry v)) (hF : Continuous (Function.uncurry F)) :
    Continuous (Function.uncurry (positiveParticleDerivative v F)) := by
  have hc : Continuous (fun p : ℝ × R2 => (p.1.toNNReal, p.2)) :=
    (continuous_real_toNNReal.comp continuous_fst).prodMk continuous_snd
  exact hv.comp ((continuous_real_toNNReal.comp continuous_fst).prodMk (hF.comp hc))

theorem continuous_positiveParticleIntegralExtension {v F : ℝ≥0 → R2 → R2}
    (hv : Continuous (Function.uncurry v)) (hF : Continuous (Function.uncurry F)) :
    Continuous (Function.uncurry (positiveParticleIntegralExtension v F)) := by
  have hc := continuous_positiveParticleDerivative hv hF
  have hp : Continuous (Function.uncurry
      (fun p : ℝ × R2 => fun s : ℝ => positiveParticleDerivative v F s p.2)) :=
    hc.comp (continuous_snd.prodMk (continuous_snd.comp continuous_fst))
  exact continuous_snd.add
    (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous (a₀ := 0) hp continuous_fst)

@[simp] theorem positiveParticleIntegralExtension_zero (v F : ℝ≥0 → R2 → R2) (a : R2) :
    positiveParticleIntegralExtension v F 0 a = a := by
  simp only [positiveParticleIntegralExtension, intervalIntegral.integral_same, add_zero]

theorem positiveParticleIntegralExtension_eq {v F : ℝ≥0 → R2 → R2}
    (hInt : ∀ (t : ℝ≥0) a,
      F t a = a + ∫ s in (0 : ℝ)..(t : ℝ), positiveParticleDerivative v F s a)
    (t : ℝ≥0) (a : R2) : positiveParticleIntegralExtension v F t a = F t a := (hInt t a).symm

theorem positiveParticleIntegralExtension_hasDerivAt {v F : ℝ≥0 → R2 → R2}
    (hv : Continuous (Function.uncurry v)) (hF : Continuous (Function.uncurry F))
    (t : ℝ) (a : R2) : HasDerivAt (fun s => positiveParticleIntegralExtension v F s a)
      (positiveParticleDerivative v F t a) t := by
  have hc : Continuous (fun s => positiveParticleDerivative v F s a) :=
    (continuous_positiveParticleDerivative hv hF).comp (continuous_id.prodMk continuous_const)
  exact (intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 t)
    hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt).const_add a

theorem positiveParticleIntegralExtension_hasDerivAt_nonneg {v F : ℝ≥0 → R2 → R2}
    (hv : Continuous (Function.uncurry v)) (hF : Continuous (Function.uncurry F))
    (hInt : ∀ (t : ℝ≥0) a,
      F t a = a + ∫ s in (0 : ℝ)..(t : ℝ), positiveParticleDerivative v F s a)
    {t : ℝ} (ht : 0 ≤ t) (a : R2) :
    HasDerivAt (fun s => positiveParticleIntegralExtension v F s a)
      (positiveParticleVelocityExtension v t (positiveParticleIntegralExtension v F t a)) t := by
  have he : positiveParticleIntegralExtension v F t a = F t.toNNReal a := by
    simpa only [Real.coe_toNNReal t ht] using positiveParticleIntegralExtension_eq hInt t.toNNReal a
  simpa only [positiveParticleDerivative, positiveParticleVelocityExtension, he] using
    positiveParticleIntegralExtension_hasDerivAt hv hF t a

end Euler2D

end
