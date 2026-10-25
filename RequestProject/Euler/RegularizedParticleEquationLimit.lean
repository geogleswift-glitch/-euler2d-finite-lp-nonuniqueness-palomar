module

public import RequestProject.Euler.RegularizedApproximation
public import RequestProject.Euler.RegularizedVelocityLimit
public import RequestProject.Euler.ParticleEquationLimit
public import RequestProject.Euler.BoundedParticleVelocity

/-!
# The actual regularized particle equations pass to their limiting flow

The approximations are the constructed self-consistent systems for the
actual smooth torus kernels.  Their common speed bound supplies dominated
convergence; the inverse-map limit supplies strong transport and the
genuine limiting velocity along every converging particle position.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

namespace Euler2D

/-- Every subsequential forward and inverse limit of the actual systems
satisfies the genuine self-consistent particle integral equation. -/
theorem regularizedApproximation_particle_integral_eq
    (f : Lp ℝ 2 μT) (hf : Integrable (f : R2 → ℝ) μT)
    {T B : ℝ} (hT : 0 ≤ T) (hB0 : 0 ≤ B) (hB : ∀ᵐ a ∂μT, ‖f a‖ ≤ B)
    (φ : ℕ → ℕ) (hφ : StrictMono φ)
    {F : Icc (0 : ℝ) T × R2 → R2} {Y : ℝ → R2 → R2}
    (hY : ∀ t, TorusAreaPreserving (Y t))
    (hForward : ∀ (t : Icc (0 : ℝ) T) a,
      Tendsto (fun n => regularizedApproximationForward f hf hT (φ n) t a)
        atTop (𝓝 (F (t, a))))
    (hBackward : ∀ (t : Icc (0 : ℝ) T), ∀ᵐ a ∂μT,
      Tendsto (fun n => regularizedApproximationBackward f hf hT (φ n) t a)
        atTop (𝓝 (Y t a)))
    (t : Icc (0 : ℝ) T) (a : R2) :
    F (t, a) = a + ∫ s in (0 : ℝ)..(t : ℝ),
      clampedParticleDerivative hT
        (fun r x => particleVelocityRepresentative f Y hY r x)
        (fun r x => F (r, x)) s a := by
  let S (n : ℕ) := regularizedApproximationSystem f hf hT (φ n)
  let gn (n : ℕ) (s : ℝ) := (S n).velocity s ((S n).forward s a)
  let g (s : ℝ) := clampedParticleDerivative hT
    (fun r x => particleVelocityRepresentative f Y hY r x) (fun r x => F (r, x)) s a
  obtain ⟨_C, M, _hC, _hM0, hM, _hlip⟩ :=
    exists_uniform_bounds_regularizedApproximation f hf hT hB0 hB
  have hεlim : Tendsto (fun n => radialApproxScale (φ n)) atTop (𝓝 (0 : ℝ)) :=
    (tendsto_nhdsWithin_iff.mp tendsto_radialApproxScale).1.comp hφ.tendsto_atTop
  have hgnc (n : ℕ) : Continuous (gn n) :=
    (S n).bounded.continuous.comp
      (continuous_id.prodMk ((S n).forward_continuous.comp
        (continuous_id.prodMk continuous_const)))
  have hgnbound (n : ℕ) :
      ∀ᵐ s ∂volume.restrict (Icc (0 : ℝ) T), ‖gn n s‖ ≤ M := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
    exact hM (φ n) s hs _
  have hgnpoint (s : ℝ) (hs : s ∈ Icc (0 : ℝ) T) :
      Tendsto (fun n => gn n s) atTop (𝓝 (g s)) := by
    have hp := tendsto_regularizedParticleVelocity_along_positions f
      (fun n => radialApproxScale (φ n)) (fun n => radialApproxScale_pos (φ n)) hεlim S
      hB0 hB hs (hY s) (hBackward ⟨s, hs⟩) (hForward ⟨s, hs⟩ a)
    have hg : g s = torusKernelVelocity (torusTransportL2 f (Y s) (hY s)) (F (⟨s, hs⟩, a)) := by
      dsimp only [g, clampedParticleDerivative]
      rw [projIcc_of_mem hT hs]
      rfl
    rw [hg]
    exact hp
  have hgnlim : ∀ᵐ s ∂volume.restrict (Icc (0 : ℝ) T),
      Tendsto (fun n => gn n s) atTop (𝓝 (g s)) := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
    exact hgnpoint s hs
  have hXlim (s : ℝ) (hs : s ∈ Icc (0 : ℝ) T) :
      Tendsto (fun n => (S n).forward s a) atTop (𝓝 (F (projIcc 0 T hT s, a))) := by
    simpa only [projIcc_of_mem hT hs] using hForward ⟨s, hs⟩ a
  have heq := particle_integral_eq_of_tendsto
    (Xn := fun n s => (S n).forward s a)
    (X := fun s => F (projIcc 0 T hT s, a)) (gn := gn) (g := g)
    (fun n => (S n).initial a) (fun n s hs => (S n).derivative s hs a)
    (fun n => (hgnc n).aestronglyMeasurable) hgnbound hgnlim hXlim t.property
  simpa only [projIcc_of_mem hT t.property] using heq

end Euler2D

end
