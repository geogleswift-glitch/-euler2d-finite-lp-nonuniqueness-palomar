module

public import RequestProject.Euler.RotatingNormalizedFiniteParticleTransport
public import RequestProject.Euler.CircularFinitePlanarClusterVelocity

/-! The actual descendant part of the rotating normalized velocity is
uniformly small everywhere. This is independent of contour smoothness,
the observation time, the current label, and the cutoff. -/

@[expose] public section

set_option maxHeartbeats 5000000
set_option maxRecDepth 5500

noncomputable section

open Complex Set Filter Topology MeasureTheory
open scoped NNReal ENNReal

namespace Euler2D
namespace CircularMaterialTransferProfile

variable {γ : ℝ≥0} {hγ : 0 < γ} {hγ1 : (γ : ℝ) < 1}
    (P : CircularMaterialTransferProfile hγ hγ1)

def normalizedFiniteInnerVelocity (s A₀ b R ρ : ℝ) (N k : ℕ)
    {f : Lp ℝ 2 μT} {T : ℝ} (S : BoundedEulerParticleSystem f T) (t θ : ℝ) (z : R2) : R2 :=
  planarRigidRotation (-θ)
    ((ampScale A₀ b k * radScale R ρ k)⁻¹ •
      complexPhysicalPlane (velocityC (P.finiteInnerClusterComplexSource s A₀ b R ρ N k S t)
        (complexPhysicalPlane.symm (radScale R ρ k • planarRigidRotation θ z))))

theorem exists_uniform_normalizedFiniteInnerVelocity_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ {s A₀ b R ρ : ℝ},
      s ≤ 0 → 0 < A₀ → 0 < b → 0 < R → R ≤ 1 / 2 → 0 < ρ → ρ ≤ 1 → ρ < b →
      ∀ N k : ℕ, ∀ {f : Lp ℝ 2 μT} {T : ℝ} (S : BoundedEulerParticleSystem f T),
      ∀ t θ z, ‖P.normalizedFiniteInnerVelocity s A₀ b R ρ N k S t θ z‖ ≤
        C * (ρ / b) / (1 - ρ / b) := by
  obtain ⟨C, hC, hbound⟩ := P.exists_uniform_finiteInnerCluster_planarVelocity_bound
  refine ⟨C, hC, ?_⟩
  intro s A₀ b R ρ hs hA hb hR hRmax hρ hρ1 hρb N k f T S t θ z
  have hAr : 0 < ampScale A₀ b k * radScale R ρ k :=
    mul_pos (div_pos hA (pow_pos hb k)) (radScale_pos hR hρ k)
  have hh := hbound hs hA.le hb hR hRmax hρ hρ1 hρb N k S t
    (complexPhysicalPlane.symm (radScale R ρ k • planarRigidRotation θ z))
  rw [normalizedFiniteInnerVelocity, LinearIsometryEquiv.norm_map, norm_smul,
    Real.norm_eq_abs, abs_inv, abs_of_pos hAr, LinearIsometryEquiv.norm_map]
  refine (mul_le_mul_of_nonneg_left hh (inv_nonneg.mpr hAr.le)).trans_eq ?_
  calc
    _ = ((ampScale A₀ b k * radScale R ρ k)⁻¹ *
        (ampScale A₀ b k * radScale R ρ k)) * (C * (ρ / b) / (1 - ρ / b)) := by ring
    _ = _ := by rw [inv_mul_cancel₀ hAr.ne', one_mul]

theorem eventually_normalizedFiniteInnerVelocity_le {b ε : ℝ} (hb : 0 < b) (hε : 0 < ε) :
    ∀ᶠ ξ : ℝ in atTop,
      ∀ {s A₀ R : ℝ}, s ≤ 0 → 0 < A₀ → 0 < R → R ≤ 1 / 2 →
      ∀ N k : ℕ, ∀ {f : Lp ℝ 2 μT} {T : ℝ} (S : BoundedEulerParticleSystem f T),
      ∀ t θ z, ‖P.normalizedFiniteInnerVelocity s A₀ b R (Real.exp (-ξ)) N k S t θ z‖ ≤ ε := by
  obtain ⟨C, hC, hbound⟩ := P.exists_uniform_normalizedFiniteInnerVelocity_bound
  have he : Tendsto (fun ξ : ℝ => Real.exp (-ξ)) atTop (𝓝 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero
  have hratio := he.div_const b
  have hden : Tendsto (fun ξ : ℝ => 1 - Real.exp (-ξ) / b) atTop (𝓝 1) := by
    simpa only [zero_div, sub_zero] using
      (tendsto_const_nhds : Tendsto (fun _ξ : ℝ => (1 : ℝ)) atTop (𝓝 1)).sub hratio
  have hsmall : Tendsto (fun ξ : ℝ => C * (Real.exp (-ξ) / b) /
      (1 - Real.exp (-ξ) / b)) atTop (𝓝 0) := by
    simpa only [zero_div, mul_zero, div_one] using
      (hratio.const_mul C).div hden (by norm_num : (1 : ℝ) ≠ 0)
  filter_upwards [he.eventually (eventually_lt_nhds hb),
    he.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)),
    hsmall.eventually (eventually_lt_nhds hε)] with ξ hρb hρ1 hh
  intro s A₀ R hs hA hR hRmax N k f T S t θ z
  exact (hbound hs hA hb hR hRmax (Real.exp_pos (-ξ)) hρ1.le hρb N k S t θ z).trans hh.le

end CircularMaterialTransferProfile
end Euler2D

end
