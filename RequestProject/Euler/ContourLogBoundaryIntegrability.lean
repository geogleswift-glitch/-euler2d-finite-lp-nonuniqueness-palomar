module

public import RequestProject.Euler.ContourLogBoundaryLimit

/-! Genuine integrability of the unregularized boundary logarithm at
every target, including targets on the parametrized curve. -/

@[expose] public section

noncomputable section

open Complex Set Filter Topology MeasureTheory intervalIntegral

namespace Euler2D

theorem intervalIntegrable_contourLogBoundaryIntegrand
    {z dz : ℝ → ℂ} {c M D : ℝ}
    (hzc : Continuous z) (hdzc : Continuous dz) (hc : 0 < c)
    (hM : ∀ t, ‖z t‖ ≤ M) (hD : ∀ t, ‖dz t‖ ≤ D)
    (hca : ∀ θ τ : ℝ, |τ| ≤ Real.pi → c * |τ| ≤ ‖z θ - z (θ + τ)‖)
    (hz : Function.Periodic z (2 * Real.pi))
    (hdz : Function.Periodic dz (2 * Real.pi)) (x : ℂ) :
    IntervalIntegrable (fun φ => Real.log ‖x - z φ‖ • dz φ)
      volume (0 : ℝ) (2 * Real.pi) := by
  by_cases hx : x ∈ Set.range z
  · obtain ⟨θ, rfl⟩ := hx
    let f : ℝ → ℂ := fun φ => Real.log ‖z θ - z φ‖ • dz φ
    have hp : Function.Periodic f (2 * Real.pi) := by
      intro φ
      dsimp only [f]
      rw [hz φ, hdz φ]
    have hrel := intervalIntegrable_contourSelfIntegrand hzc hdzc hc hM hD hca θ
    change IntervalIntegrable (fun τ => f (θ + τ)) volume (-Real.pi) Real.pi at hrel
    have hshift := hrel.comp_add_left (-θ)
    have hi : IntervalIntegrable f volume (θ - Real.pi) (θ + Real.pi) := by
      have hf : (fun x => f (θ + (-θ + x))) = f := by
        funext x
        congr 1
        ring
      rw [hf] at hshift
      rwa [show -Real.pi - -θ = θ - Real.pi by ring,
        show Real.pi - -θ = θ + Real.pi by ring] at hshift
    have hi' : IntervalIntegrable f volume (θ - Real.pi) ((θ - Real.pi) + 2 * Real.pi) := by
      rw [show (θ - Real.pi) + 2 * Real.pi = θ + Real.pi by ring]
      exact hi
    exact hp.intervalIntegrable (by positivity) (by finiteness) hi' 0 (2 * Real.pi)
  · have hn : Continuous (fun φ : ℝ => ‖x - z φ‖) := by fun_prop
    have hlog : Continuous (fun φ : ℝ => Real.log ‖x - z φ‖) :=
      hn.log (fun φ => norm_ne_zero_iff.mpr (sub_ne_zero.mpr (by
        intro he
        exact hx ⟨φ, he.symm⟩)))
    exact (hlog.smul hdzc).intervalIntegrable 0 (2 * Real.pi)

end Euler2D
