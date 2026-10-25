module

public import RequestProject.Euler.RegularizedApproximation
public import RequestProject.Euler.PeriodicParticleLimit

/-!
# A simultaneous limit of the actual regularized forward and inverse flows

All hypotheses of particle compactness are supplied by the genuinely
constructed smooth-kernel systems and their common vorticity bounds.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology Metric

namespace Euler2D

theorem uniform_subseq_regularizedApproximation_pair
    (w : R2 → ℝ) (hw : Integrable w μT) {T B : ℝ} (hT : 0 ≤ T)
    (hB0 : 0 ≤ B) (hB : ∀ᵐ y ∂μT, ‖w y‖ ≤ B) :
    ∃ F G : Icc (0 : ℝ) T × R2 → R2, Continuous F ∧ Continuous G ∧
      (∀ t : Icc (0 : ℝ) T, TorusAreaPreserving (fun a => F (t, a))) ∧
      (∀ t : Icc (0 : ℝ) T, TorusAreaPreserving (fun a => G (t, a))) ∧
      (∀ a, F (⟨0, le_rfl, hT⟩, a) = a) ∧
      (∀ a, G (⟨0, le_rfl, hT⟩, a) = a) ∧
      (∀ (t : Icc (0 : ℝ) T) a k,
        F (t, a + torusLatticeShift k) = F (t, a) + torusLatticeShift k) ∧
      (∀ (t : Icc (0 : ℝ) T) a k,
        G (t, a + torusLatticeShift k) = G (t, a) + torusLatticeShift k) ∧
      (∀ (t : Icc (0 : ℝ) T) a, F (t, G (t, a)) = a) ∧
      (∀ (t : Icc (0 : ℝ) T) a, G (t, F (t, a)) = a) ∧
      ∃ φ : ℕ → ℕ, StrictMono φ ∧
        TendstoUniformly
          (fun n (p : Icc (0 : ℝ) T × R2) =>
            regularizedApproximationForward w hw hT (φ n) p.1 p.2) F atTop ∧
        TendstoUniformly
          (fun n (p : Icc (0 : ℝ) T × R2) =>
            regularizedApproximationBackward w hw hT (φ n) p.1 p.2) G atTop := by
  obtain ⟨C, M, hC, hM0, hM, hlip⟩ :=
    exists_uniform_bounds_regularizedApproximation w hw hT hB0 hB
  exact uniform_subseq_periodic_particle_pair hT hC hM0
    (regularizedApproximationVelocity w hw hT)
    (regularizedApproximationForward w hw hT)
    (regularizedApproximationBackward w hw hT)
    (fun n => (regularizedApproximationSystem w hw hT n).forward_continuous)
    (fun n => (regularizedApproximationSystem w hw hT n).backward_continuous)
    (fun n => (regularizedApproximationSystem w hw hT n).derivative)
    (fun n => (regularizedApproximationSystem w hw hT n).initial)
    (fun n => (regularizedApproximationSystem w hw hT n).forward_backward)
    (fun n => (regularizedApproximationSystem w hw hT n).backward_forward)
    hM hlip
    (fun n => (regularizedApproximationSystem w hw hT n).forward_lattice)
    (fun n => (regularizedApproximationSystem w hw hT n).backward_lattice)
    (fun n => (regularizedApproximationSystem w hw hT n).forward_area)
    (fun n t _ => (regularizedApproximationSystem w hw hT n).backward_area t)

end Euler2D

end
