module

public import RequestProject.Euler.BoundedParticleVelocity
public import RequestProject.Euler.TorusKernelTimeContinuity

/-!
# The actual singular-integral particle equation implies weak Euler

Joint continuity, periodicity and agreement with the `L²` velocity are
derived for the constructed representative. The remaining particle
equation is genuinely self-consistent with the transported vorticity.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology

namespace Euler2D

theorem continuous_particleVelocityRepresentative (f : Lp ℝ 2 μT) {M : ℝ}
    (hM0 : 0 ≤ M) (hM : ∀ᵐ x ∂μT, ‖f x‖ ≤ M) {Y : ℝ → R2 → R2}
    (hY : ∀ t, TorusAreaPreserving (Y t)) (hYc : Continuous (Function.uncurry Y)) :
    Continuous (Function.uncurry (particleVelocityRepresentative f Y hY)) :=
  continuous_torusKernelVelocity_of_continuous_L2
    (continuous_particleCurlL2 f hY hYc) hM0 (norm_particleCurlL2_ae_le f hM Y hY)

theorem weakEuler_of_kernel_particle_flow {T : ℝ} (hT : 0 ≤ T)
    (f : Lp ℝ 2 μT) (hf : (∫ x in torusBox, f x) = 0)
    {M : ℝ} (hM0 : 0 ≤ M) (hM : ∀ᵐ x ∂μT, ‖f x‖ ≤ M)
    {X Y : ℝ → R2 → R2} (hY : ∀ t, TorusAreaPreserving (Y t))
    (hYc : Continuous (Function.uncurry Y)) (hXc : Continuous (Function.uncurry X))
    (hXmp : ∀ t ∈ Icc 0 T, TorusAreaPreserving (X t))
    (hinv : ∀ t ∈ Icc 0 T, ∀ᵐ a ∂μT, torusWrap (Y t (torusWrap (X t a))) = a)
    (hinit : ∀ a ∈ torusBox, X 0 a = a)
    (hflow : ∀ a ∈ torusBox, ∀ t ∈ Icc 0 T,
      HasDerivAt (fun s => X s a)
        (particleVelocityRepresentative f Y hY t (X t a)) t) :
    IsWeakEulerSolution T (biotSavartL2 f) (particleVelocity f Y hY) := by
  have hv := continuous_particleVelocityRepresentative f hM0 hM hY hYc
  have hraw := weakEuler_of_biotSavart_particle_flow hT f hf hY hYc hXc hv
    (isTorusPeriodic_particleVelocityRepresentative f Y hY) hXmp hinv hinit hflow
    (fun t _ => (particleVelocityRepresentative_ae f hM hf Y hY t).symm)
  have hi : particleCurlL2 f Y hY 0 = f :=
    particleCurlL2_initial f hY hinit (hinv 0 ⟨le_rfl, hT⟩)
  have hu0 : particleVelocity f Y hY 0 = biotSavartL2 f := by
    change biotSavartL2 (particleCurlL2 f Y hY 0) = biotSavartL2 f
    rw [hi]
  simpa only [hu0] using hraw

end Euler2D

end
