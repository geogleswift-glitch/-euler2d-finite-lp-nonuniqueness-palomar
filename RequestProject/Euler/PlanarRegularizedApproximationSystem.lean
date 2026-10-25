module

public import RequestProject.Euler.PlanarSmoothKernel
public import RequestProject.Euler.PlanarRegularizedTransport

/-! The actual compact smoothings of the original singular planar
kernel produce an entire sequence of genuine self-consistent planar
particle systems, on every prescribed finite time interval. -/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal ContDiff

namespace Euler2D

theorem exists_planarBiotSavart_regularized_system_sequence
    {w : R2 → ℝ} (hw : Integrable w μT) {T : ℝ} (hT : 0 ≤ T) :
    ∃ L M : ℕ → ℝ≥0,
    ∃ S : ∀ n, SmoothPlanarRegularizedParticleSystem (planarSmoothedBiotSavartKernel n) w T (L n) (M n),
      ∀ n, ContDiff ℝ ∞ (planarSmoothedBiotSavartKernel n) ∧
        LipschitzWith (L n) (planarSmoothedBiotSavartKernel n) ∧
        (∀ x, ‖planarSmoothedBiotSavartKernel n x‖ ≤ M n) ∧
        ∀ x, pd 0 (planarSmoothedBiotSavartKernel n) x 0 + pd 1 (planarSmoothedBiotSavartKernel n) x 1 = 0 := by
  classical
  obtain ⟨L, M, hK⟩ := exists_planarSmoothedBiotSavartKernel_bounds
  have hS (n : ℕ) : Nonempty
      (SmoothPlanarRegularizedParticleSystem (planarSmoothedBiotSavartKernel n) w T (L n) (M n)) :=
    exists_smoothPlanarRegularizedParticleSystem ((hK n).1.of_le (by
      change ((1 : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞)
      exact WithTop.coe_le_coe.mpr le_top)) (hK n).2.1 (hK n).2.2.1 (hK n).2.2.2 hw hT
  exact ⟨L, M, fun n => Classical.choice (hS n), hK⟩

end Euler2D

end
