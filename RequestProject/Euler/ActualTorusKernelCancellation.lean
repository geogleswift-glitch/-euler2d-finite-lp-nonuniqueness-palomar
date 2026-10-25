module

public import RequestProject.Euler.ActualTorusRemainderVelocity
public import RequestProject.Euler.TorusBiotSavartKernel

/-!
# Cubic cancellation of the actual torus kernel minus the planar kernel

The constructed local kernel equals the true planar Biot--Savart kernel
on the half-radius disk.  Hence the actual kernel difference is exactly
the perpendicular gradient of the constructed correction there.  The
previously proved actual velocity cancellation therefore applies directly
to the actual periodic and planar kernels.
-/

@[expose] public section

noncomputable section

open MeasureTheory Complex Metric Set Filter Topology
open scoped ContDiff ComplexConjugate

namespace Euler2D

theorem torusBiotSavartKernel_sub_kernelK_near_pole {x : R2}
    (hx : ‖x - torusCenter‖ ≤ 1 / 2) :
    torusBiotSavartKernel x - kernelK (x - torusCenter) =
      perpGradient torusGreenCorrection x := by
  have hbox : x ∈ torusBox := norm_sub_center_lt_one_mem_box (by linarith)
  rw [torusBiotSavartKernel, periodicLocalKernel_eq_on_box hbox,
    localPlanarKernel_eq_kernelK_of_norm_le_half hx]
  abel

theorem torusBiotSavartKernel_complexTorusPoint_sub_kernelK {z : ℂ}
    (hz : ‖z‖ ≤ 1 / 2) :
    torusBiotSavartKernel (complexTorusPoint z) - kernelK (complexPhysicalPlane z) =
      perpGradient torusGreenCorrection (complexTorusPoint z) := by
  have hn : ‖complexTorusPoint z - torusCenter‖ ≤ 1 / 2 := by
    rw [norm_complexTorusPoint_sub_center]
    exact hz
  simpa only [complexTorusPoint, add_sub_cancel_right] using
    torusBiotSavartKernel_sub_kernelK_near_pole hn

lemma planeComplexEquiv_kernelK_complexPhysicalPlane (z : ℂ) :
    planeComplexEquiv (kernelK (complexPhysicalPlane z)) =
      I * z / (2 * Real.pi * ‖z‖ ^ 2) := by
  rw [← complexPhysicalPlane_symm_eq_planeComplexEquiv]
  simp only [kernelK, LinearIsometryEquiv.norm_map, map_smul,
    ← complexPhysicalPlane_mul_I, LinearIsometryEquiv.symm_apply_apply]
  simp only [Complex.real_smul, Complex.ofReal_inv, Complex.ofReal_mul,
    Complex.ofReal_ofNat, Complex.ofReal_pow, div_eq_mul_inv]
  ring

/-- The weighted actual kernel difference is the weighted actual smooth
correction throughout the small support; outside it the density is zero. -/
theorem integral_torusKernel_sub_planar_eq_correction {a : ℝ} (ha16 : a ≤ 1 / 16)
    {ζ : ℂ → ℝ} (hsupp : ∀ y, a < ‖y‖ → ζ y = 0)
    {x : ℂ} (hx : ‖x‖ ≤ a) :
    (∫ y, ζ y • (torusBiotSavartKernel (complexTorusPoint (x - y)) -
      kernelK (complexPhysicalPlane (x - y)))) =
      ∫ y, ζ y • perpGradient torusGreenCorrection (complexTorusPoint (x - y)) := by
  apply integral_congr_ae
  exact Eventually.of_forall fun y => by
    dsimp only
    by_cases hy : ζ y = 0
    · simp only [hy, zero_smul]
    have hya : ‖y‖ ≤ a := le_of_not_gt (fun h => hy (hsupp y h))
    have hgap : ‖x - y‖ ≤ 1 / 2 := by
      have hn := norm_sub_le x y
      linarith
    rw [torusBiotSavartKernel_complexTorusPoint_sub_kernelK hgap]

/-- The cubic bound for the genuine periodic Biot--Savart kernel minus
the genuine planar Biot--Savart kernel, in physical vector coordinates. -/
theorem actual_torusKernelRemainder_cancellation {a : ℝ}
    (ha : 0 < a) (ha16 : a ≤ 1 / 16) :
    ∃ K : ℝ, 0 < K ∧ ∀ ζ : ℂ → ℝ, Integrable ζ →
      (∀ y, a < ‖y‖ → ζ y = 0) → (∀ y, ζ (I * y) = ζ y) →
      (∫ y, ζ y) = 0 → ∀ x : ℂ, ‖x‖ ≤ a →
        ‖∫ y, ζ y • (torusBiotSavartKernel (complexTorusPoint (x - y)) -
          kernelK (complexPhysicalPlane (x - y)))‖ ≤
          K * ‖x‖ ^ 3 * ∫ y, ‖y‖ ^ 4 * |ζ y| := by
  obtain ⟨K, hK0, hK⟩ := actual_physicalTorusRemainderVelocity_cancellation ha ha16
  refine ⟨K, hK0, fun ζ hζ hsupp hsym hmass x hx => ?_⟩
  rw [integral_torusKernel_sub_planar_eq_correction ha16 hsupp hx]
  exact hK ζ hζ hsupp hsym hmass x hx

/-- The same genuine kernel bound in the complex physical coordinates used
by the already proved planar multipole and fourth-moment estimates. -/
theorem actual_complexTorusKernelRemainder_cancellation {a : ℝ}
    (ha : 0 < a) (ha16 : a ≤ 1 / 16) :
    ∃ K : ℝ, 0 < K ∧ ∀ ζ : ℂ → ℝ, Integrable ζ →
      (∀ y, a < ‖y‖ → ζ y = 0) → (∀ y, ζ (I * y) = ζ y) →
      (∫ y, ζ y) = 0 → ∀ x : ℂ, ‖x‖ ≤ a →
        ‖∫ y, ζ y • planeComplexEquiv
          (torusBiotSavartKernel (complexTorusPoint (x - y)) -
            kernelK (complexPhysicalPlane (x - y)))‖ ≤
          K * ‖x‖ ^ 3 * ∫ y, ‖y‖ ^ 4 * |ζ y| := by
  obtain ⟨K, hK0, hK⟩ := actual_torusRemainderVelocity_cancellation ha ha16
  refine ⟨K, hK0, fun ζ hζ hsupp hsym hmass x hx => ?_⟩
  have he : (∫ y, ζ y • planeComplexEquiv
      (torusBiotSavartKernel (complexTorusPoint (x - y)) -
        kernelK (complexPhysicalPlane (x - y)))) =
      ∫ y, ζ y • actualComplexRemainderKernel (x - y) := by
    apply integral_congr_ae
    exact Eventually.of_forall fun y => by
      dsimp only
      by_cases hy : ζ y = 0
      · simp only [hy, zero_smul]
      have hya : ‖y‖ ≤ a := le_of_not_gt (fun h => hy (hsupp y h))
      have hgap : ‖x - y‖ ≤ 1 / 2 := by
        have hn := norm_sub_le x y
        linarith
      rw [torusBiotSavartKernel_complexTorusPoint_sub_kernelK hgap]
      rfl
  rw [he]
  exact hK ζ hζ hsupp hsym hmass x hx

end Euler2D

end
