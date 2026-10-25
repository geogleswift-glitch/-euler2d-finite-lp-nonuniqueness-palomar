module

public import RequestProject.Euler.BoundedEulerExistence
public import RequestProject.Euler.RegularizedParticleEquationLimit

/-!
# Constructed bounded-vorticity Euler particle systems

The witnesses are obtained from the actual smooth-kernel systems. Their
forward and inverse maps converge together, and the actual particle
equation survives the limit. No existence hypothesis for a limiting flow
or for an Euler solution is used.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

namespace Euler2D

theorem exists_boundedEulerParticleSystem (f : Lp ℝ 2 μT)
    {T B : ℝ} (hT : 0 ≤ T) (hB0 : 0 ≤ B) (hB : ∀ᵐ a ∂μT, ‖f a‖ ≤ B) :
    Nonempty (BoundedEulerParticleSystem f T) := by
  have hf : Integrable (f : R2 → ℝ) μT := (Lp.memLp f).integrable (by norm_num)
  obtain ⟨F, G, hFc, hGc, hFMP, hGMP, _hF0, _hG0, hFlat, hGlat,
    hFG, hGF, φ, hφ, hFlim, hGlim⟩ :=
    uniform_subseq_regularizedApproximation_pair (f : R2 → ℝ) hf hT hB0 hB
  let Y : ℝ → R2 → R2 := particleVelocityExtension hT (fun t a => G (t, a))
  have hYc : Continuous (Function.uncurry Y) :=
    continuous_particleVelocityExtension hT hGc
  have hY (t : ℝ) : TorusAreaPreserving (Y t) := hGMP (projIcc 0 T hT t)
  have hYeq (t : Icc (0 : ℝ) T) (a : R2) : Y t a = G (t, a) := by
    dsimp only [Y, particleVelocityExtension]
    rw [projIcc_of_mem hT t.property]
  have hYlat (t : ℝ) (a : R2) (k : Fin 2 → ℤ) :
      Y t (a + torusLatticeShift k) = Y t a + torusLatticeShift k :=
    hGlat (projIcc 0 T hT t) a k
  have hFY (t : Icc (0 : ℝ) T) (a : R2) : F (t, Y t a) = a := by
    rw [hYeq]
    exact hFG t a
  have hYF (t : Icc (0 : ℝ) T) (a : R2) : Y t (F (t, a)) = a :=
    (hYeq t (F (t, a))).trans (hGF t a)
  have hForward (t : Icc (0 : ℝ) T) (a : R2) :
      Tendsto (fun n => regularizedApproximationForward f hf hT (φ n) t a)
        atTop (𝓝 (F (t, a))) := TendstoUniformly.tendsto_at hFlim (t, a)
  have hBackward (t : Icc (0 : ℝ) T) : ∀ᵐ a ∂μT,
      Tendsto (fun n => regularizedApproximationBackward f hf hT (φ n) t a)
        atTop (𝓝 (Y t a)) := by
    exact Eventually.of_forall fun a => by
      simpa only [hYeq] using TendstoUniformly.tendsto_at hGlim (t, a)
  have hInt := regularizedApproximation_particle_integral_eq f hf hT hB0 hB
    φ hφ hY hForward hBackward
  exact boundedEulerParticleSystem_of_integral_flow f hT hB0 hB
    (fun t a => F (t, a)) hFc Y hYc hY hFMP hFlat hYlat hFY hYF hInt

/-- An actual bounded initial vorticity of zero mean gives an Euler
solution in the original strong-continuity and momentum formulation. -/
theorem exists_boundedVorticity_weakEuler (f : Lp ℝ 2 μT)
    {T B : ℝ} (hT : 0 ≤ T) (hmean : (∫ x in torusBox, f x) = 0)
    (hB0 : 0 ≤ B) (hB : ∀ᵐ a ∂μT, ‖f a‖ ≤ B) :
    ∃ S : BoundedEulerParticleSystem f T,
      IsWeakEulerSolution T (biotSavartL2 f)
        (particleVelocity f S.backward S.backward_area) := by
  obtain ⟨S⟩ := exists_boundedEulerParticleSystem f hT hB0 hB
  exact ⟨S, S.weakEuler hT hmean hB0 hB⟩

end Euler2D

end
