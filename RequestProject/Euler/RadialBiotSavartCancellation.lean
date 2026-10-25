module

public import RequestProject.Euler.ContourAnnularPerturbation
public import RequestProject.Euler.InteriorContourForcing

/-! Circular reference velocities have exactly zero radial component.
This is proved for the original singular Biot--Savart integral by a
measure-preserving reflection fixing the target; no reference velocity
formula or assumed cancellation is used. -/

@[expose] public section

set_option maxHeartbeats 2100000

noncomputable section

open Complex ComplexConjugate Set MeasureTheory Metric
open scoped NNReal

namespace Euler2D

theorem integral_comp_circle_reflection (e : Circle) (f : ℂ → ℂ) :
    (∫ y : ℂ, f ((e : ℂ) * conj y)) = ∫ y : ℂ, f y := by
  let E : ℂ ≃ₗᵢ[ℝ] ℂ := conjLIE.trans (rotation e)
  have h := E.measurePreserving.integral_comp E.toHomeomorph.measurableEmbedding f
  simpa only [E, LinearIsometryEquiv.trans_apply, rotation_apply, conjLIE_apply] using h

theorem radial_component_velocityC_eq_zero {w : ℂ → ℝ}
    (hradial : ∀ x y, ‖x‖ = ‖y‖ → w x = w y) (z : ℂ) :
    (velocityC w z * conj z).re = 0 := by
  by_cases hz : z = 0
  · simp [hz]
  have hcz : conj z ≠ 0 := (map_ne_zero _).mpr hz
  let e : Circle := ⟨z / conj z, mem_sphere_zero_iff_norm.mpr (by
    simp only [norm_div, norm_conj, div_self (norm_ne_zero_iff.mpr hz)])⟩
  have hfix : (e : ℂ) * conj z = z := by
    change z / conj z * conj z = z
    exact div_mul_cancel₀ z hcz
  have hfixconj : conj z = conj (e : ℂ) * z := by
    have hh := congrArg conj hfix
    simpa only [map_mul, conj_conj] using hh.symm
  have heinv : (conj (e : ℂ))⁻¹ = (e : ℂ) := by
    rw [← Circle.coe_inv_eq_conj, Circle.coe_inv, inv_inv]
  let c : ℂ := I / (2 * Real.pi)
  have hc : conj c = -c := by
    simp only [c, map_div₀, map_mul, conj_I, map_ofNat, conj_ofReal]
    ring
  let G : ℂ → ℂ := fun y => (w y : ℂ) * c * (conj (z - y))⁻¹ * conj z
  have hpoint : ∀ y, G ((e : ℂ) * conj y) = -conj (G y) := by
    intro y
    have hwy : w ((e : ℂ) * conj y) = w y :=
      hradial _ _ (by simp only [norm_mul, Circle.norm_coe, norm_conj, one_mul])
    have hden : conj (z - (e : ℂ) * conj y) = conj (e : ℂ) * (z - y) := by
      rw [map_sub, map_mul, conj_conj, hfixconj]
      ring
    have hneg : -conj (G y) = (w y : ℂ) * c * (z - y)⁻¹ * z := by
      simp only [G, map_mul, map_inv₀, conj_conj, conj_ofReal, hc]
      ring
    rw [hneg]
    simp only [G, hwy, hden, mul_inv_rev, heinv]
    calc
      _ = (w y : ℂ) * c * (z - y)⁻¹ * ((e : ℂ) * conj z) := by ring
      _ = _ := by rw [hfix]
  have he : (∫ y, G y) = -conj (∫ y, G y) := by
    calc
      _ = ∫ y, G ((e : ℂ) * conj y) := (integral_comp_circle_reflection e G).symm
      _ = ∫ y, -conj (G y) := integral_congr_ae (ae_of_all _ hpoint)
      _ = _ := by rw [integral_neg, integral_conj]
  have hGeq : (∫ y, G y) = velocityC w z * conj z := by
    have hv : velocityC w z = c * (∫ y, (w y : ℂ) * (conj (z - y))⁻¹) := by
      have hh := congrArg conj (conj_velocityC w z)
      change conj (conj (velocityC w z)) = conj (-c * (∫ y, (w y : ℂ) * (z - y)⁻¹)) at hh
      simpa only [conj_conj, map_mul, map_neg, hc, neg_neg, ← integral_conj,
        map_inv₀, conj_ofReal] using hh
    calc
      _ = (∫ y, (w y : ℂ) * c * (conj (z - y))⁻¹) * conj z := integral_mul_const _ _
      _ = (c * (∫ y, (w y : ℂ) * (conj (z - y))⁻¹)) * conj z := by
        rw [← integral_const_mul]
        congr 1
        apply integral_congr_ae
        exact ae_of_all _ (fun y => by ring)
      _ = _ := by rw [hv]
  rw [hGeq] at he
  have hre := congrArg Complex.re he
  simp only [neg_re, conj_re] at hre
  linarith

theorem radial_component_circlePatchVelocity_eq_zero (r : ℝ) (z : ℂ) :
    (velocityC (circlePatchVorticity r) z * conj z).re = 0 := by
  apply radial_component_velocityC_eq_zero
  intro x y hnorm
  simp [circlePatchVorticity, Set.indicator, mem_ball_zero_iff, hnorm]

theorem radial_component_finiteCirclePatchVelocity_eq_zero {ι : Type*} [Fintype ι]
    (g : ι → ℝ) (r : ι → ℝ) (z : ℂ) :
    (velocityC (fun y => ∑ i, g i * circlePatchVorticity (r i) y) z * conj z).re = 0 := by
  apply radial_component_velocityC_eq_zero
  intro x y hnorm
  apply Finset.sum_congr rfl
  intro i _
  simp [circlePatchVorticity, Set.indicator, mem_ball_zero_iff, hnorm]

end Euler2D

end
