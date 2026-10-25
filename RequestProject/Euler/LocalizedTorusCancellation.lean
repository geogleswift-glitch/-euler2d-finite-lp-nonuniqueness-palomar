module

public import RequestProject.Euler.LocalizedTorusComparison

/-!
# Cubic comparison for the genuine velocity of a localized torus density

Both singular integrals are genuinely integrable. The physical torus
velocity is the planar velocity plus the actual smooth correction, and
the established fourth-moment cancellation bounds their difference.
-/

@[expose] public section

noncomputable section

open MeasureTheory Complex Set Filter Topology

namespace Euler2D

theorem torusKernelVelocity_localized_eq_planar_add_remainder {a M : ℝ}
    (ha : a ≤ 1 / 16) {ζ : ℂ → ℝ} (hζ : Integrable ζ)
    (hM : ∀ y, ‖ζ y‖ ≤ M) (hsupp : ∀ z, a < ‖z‖ → ζ z = 0)
    {x : ℂ} (hx : ‖x‖ ≤ a) :
    planeComplexEquiv (torusKernelVelocity (localizedComplexVorticity ζ) (complexTorusPoint x)) =
      velocityC ζ x + ∫ y, ζ y • actualComplexRemainderKernel (x - y) := by
  have ha1 : a < 1 := by linarith
  have hT := integrable_localized_torusComplexVelocity ha1 hζ hM hsupp x
  have hR := integrable_actualComplexRemainderVelocity hζ x
  have hpoint (y : ℂ) : ζ y • planeComplexEquiv
      (torusBiotSavartKernel (complexTorusPoint (x - y))) =
      ζ y • (I * (x - y) / (2 * Real.pi * ‖x - y‖ ^ 2)) +
        ζ y • actualComplexRemainderKernel (x - y) := by
    by_cases hy : ζ y = 0
    · simp only [hy, zero_smul, add_zero]
    have hya : ‖y‖ ≤ a := le_of_not_gt (fun h => hy (hsupp y h))
    have hgap : ‖x - y‖ ≤ 1 / 2 := by
      have hn := norm_sub_le x y
      linarith
    rw [complexTorusKernel_eq_planar_add_remainder hgap, smul_add]
  have hP : Integrable (fun y =>
      ζ y • (I * (x - y) / (2 * Real.pi * ‖x - y‖ ^ 2))) := by
    apply (hT.sub hR).congr
    filter_upwards [] with y
    change ζ y • planeComplexEquiv
      (torusBiotSavartKernel (complexTorusPoint (x - y))) -
      ζ y • actualComplexRemainderKernel (x - y) = _
    rw [hpoint y]
    abel
  have hplanar : (∫ y, ζ y • (I * (x - y) / (2 * Real.pi * ‖x - y‖ ^ 2))) =
      velocityC ζ x := by
    simp only [velocityC, Complex.real_smul]
  rw [torusKernelVelocity_localized_complex ha1 hsupp x, ← hplanar,
    ← integral_add hP hR]
  apply integral_congr_ae
  exact Eventually.of_forall hpoint

theorem localized_torusVelocity_cubic_comparison {a : ℝ}
    (ha : 0 < a) (ha16 : a ≤ 1 / 16) :
    ∃ K : ℝ, 0 < K ∧ ∀ ζ : ℂ → ℝ, Integrable ζ →
      (∃ M : ℝ, ∀ y, ‖ζ y‖ ≤ M) →
      (∀ y, a < ‖y‖ → ζ y = 0) → (∀ y, ζ (I * y) = ζ y) →
      (∫ y, ζ y) = 0 → ∀ x : ℂ, ‖x‖ ≤ a →
        ‖planeComplexEquiv (torusKernelVelocity (localizedComplexVorticity ζ) (complexTorusPoint x)) -
          velocityC ζ x‖ ≤ K * ‖x‖ ^ 3 * ∫ y, ‖y‖ ^ 4 * |ζ y| := by
  obtain ⟨K, hK0, hK⟩ := actual_torusRemainderVelocity_cancellation ha ha16
  refine ⟨K, hK0, fun ζ hζ hbounded hsupp hsym hmass x hx => ?_⟩
  obtain ⟨M, hM⟩ := hbounded
  rw [torusKernelVelocity_localized_eq_planar_add_remainder ha16 hζ hM hsupp hx,
    add_sub_cancel_left]
  exact hK ζ hζ hsupp hsym hmass x hx

end Euler2D

end
