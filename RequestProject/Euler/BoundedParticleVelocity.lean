module

public import RequestProject.Euler.LagrangianEuler
public import RequestProject.Euler.TorusKernelVelocityRegularity
public import RequestProject.Euler.LogFlowGlobal

/-!
# Actual continuous spatial representatives for bounded transported curls

The representative is the physical kernel integral of the actual
transported `L²` class, and agrees almost everywhere with the existing
Biot–Savart velocity. Its logarithmic modulus is uniform in time.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology Metric Real

namespace Euler2D

lemma norm_particleCurlL2_ae_le (f : Lp ℝ 2 μT) {M : ℝ}
    (hM : ∀ᵐ x ∂μT, ‖f x‖ ≤ M) (Y : ℝ → R2 → R2)
    (hY : ∀ t, TorusAreaPreserving (Y t)) (t : ℝ) :
    ∀ᵐ x ∂μT, ‖particleCurlL2 f Y hY t x‖ ≤ M := by
  have hb := (hY t).quasiMeasurePreserving.ae hM
  filter_upwards [particleCurlL2_ae f Y hY t, hb] with x hx hb
  rw [hx]
  exact hb

def particleVelocityRepresentative (f : Lp ℝ 2 μT) (Y : ℝ → R2 → R2)
    (hY : ∀ t, TorusAreaPreserving (Y t)) (t : ℝ) : R2 → R2 :=
  torusKernelVelocity (particleCurlL2 f Y hY t)

theorem particleVelocityRepresentative_ae (f : Lp ℝ 2 μT) {M : ℝ}
    (hM : ∀ᵐ x ∂μT, ‖f x‖ ≤ M) (hf : (∫ x in torusBox, f x) = 0)
    (Y : ℝ → R2 → R2) (hY : ∀ t, TorusAreaPreserving (Y t)) (t : ℝ) :
    particleVelocityRepresentative f Y hY t =ᵐ[μT] particleVelocity f Y hY t :=
  torusKernelVelocity_eq_biotSavartL2_ae _ (norm_particleCurlL2_ae_le f hM Y hY t)
    ((integral_particleCurlL2 f Y hY t).trans hf)

theorem isTorusPeriodic_particleVelocityRepresentative (f : Lp ℝ 2 μT)
    (Y : ℝ → R2 → R2) (hY : ∀ t, TorusAreaPreserving (Y t)) (t : ℝ) :
    IsTorusPeriodic (particleVelocityRepresentative f Y hY t) :=
  isTorusPeriodic_torusKernelVelocity _

theorem continuous_particleVelocityRepresentative_space (f : Lp ℝ 2 μT) {M : ℝ}
    (hM : ∀ᵐ x ∂μT, ‖f x‖ ≤ M) (Y : ℝ → R2 → R2)
    (hY : ∀ t, TorusAreaPreserving (Y t)) (t : ℝ) :
    Continuous (particleVelocityRepresentative f Y hY t) :=
  continuous_torusKernelVelocity (Lp.aestronglyMeasurable _)
    (norm_particleCurlL2_ae_le f hM Y hY t)

theorem norm_particleVelocityRepresentative_le (f : Lp ℝ 2 μT) {M : ℝ}
    (hM : ∀ᵐ x ∂μT, ‖f x‖ ≤ M) (Y : ℝ → R2 → R2)
    (hY : ∀ t, TorusAreaPreserving (Y t)) (t : ℝ) (x : R2) :
    ‖particleVelocityRepresentative f Y hY t x‖ ≤
      M * ∫ y in torusBox, ‖torusBiotSavartKernel y‖ :=
  norm_torusKernelVelocity_le (norm_particleCurlL2_ae_le f hM Y hY t) x

theorem exists_uniform_logLip_particleVelocityRepresentative (f : Lp ℝ 2 μT) {M : ℝ}
    (hM0 : 0 ≤ M) (hM : ∀ᵐ x ∂μT, ‖f x‖ ≤ M) (Y : ℝ → R2 → R2)
    (hY : ∀ t, TorusAreaPreserving (Y t)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t x z, ‖x - z‖ ≤ 1 / 2 →
      ‖particleVelocityRepresentative f Y hY t x - particleVelocityRepresentative f Y hY t z‖ ≤
        C * logFlowModulus ‖x - z‖ :=
  exists_uniform_logLip_torusKernelVelocity (fun _ => Lp.aestronglyMeasurable _) hM0
    (norm_particleCurlL2_ae_le f hM Y hY)

theorem particleVelocityRepresentative_trajectory_unique (f : Lp ℝ 2 μT) {M : ℝ}
    (hM0 : 0 ≤ M) (hM : ∀ᵐ x ∂μT, ‖f x‖ ≤ M) (Y : ℝ → R2 → R2)
    (hY : ∀ t, TorusAreaPreserving (Y t)) {T : ℝ} {a b : ℝ → R2}
    (ha : Continuous a) (hb : Continuous b)
    (haD : ∀ t ∈ Icc 0 T, HasDerivAt a (particleVelocityRepresentative f Y hY t (a t)) t)
    (hbD : ∀ t ∈ Icc 0 T, HasDerivAt b (particleVelocityRepresentative f Y hY t (b t)) t)
    (hinit : a 0 = b 0) : ∀ t ∈ Icc 0 T, a t = b t := by
  obtain ⟨C, hC, hbound⟩ := exists_uniform_logLip_particleVelocityRepresentative f hM0 hM Y hY
  exact logFlow_unique hC ha hb haD hbD hinit (fun t _ => hbound t)

end Euler2D

end
