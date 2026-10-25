module

public import RequestProject.Euler.CircularFiniteLabelTransport
public import RequestProject.Euler.EulerVelocitySupportWindow

/-! A velocity bound uniform in the finite cutoff for the same actual
Euler systems. It is the geometric sum of the transported label bounds. -/

@[expose] public section

set_option maxHeartbeats 2600000

noncomputable section

open MeasureTheory Set Filter Topology Metric Real
open scoped NNReal ENNReal

namespace Euler2D
namespace CircularMaterialTransferProfile

variable {γ : ℝ≥0} {hγ : 0 < γ} {hγ1 : (γ : ℝ) < 1}
    (P : CircularMaterialTransferProfile hγ hγ1)

theorem exists_uniform_finiteEuler_velocity_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ {s A₀ b R ρ q T : ℝ},
      ∀ [Fact (1 ≤ ENNReal.ofReal q)] (hs : s ≤ 0) (_hA : 0 ≤ A₀) (_hb : 0 < b)
        (hR : 0 < R) (_hRmax : R ≤ 1 / 2) (hρ : 0 < ρ) (_hρ1 : ρ ≤ 1)
        (_hρb : ρ < b) (hq : 0 < q) (hqE : 2 ≤ ENNReal.ofReal q),
      ∀ N : ℕ, ∀ S : BoundedEulerParticleSystem
        (finiteBaseCurlL2 (A₀ := A₀) (b := b) hR hρ hq hqE
          (P.finiteBaseLp (A₀ := A₀) (b := b) (q := q) hs hR hρ) N) T,
      ∀ t x,
        ‖particleVelocityRepresentative
          (finiteBaseCurlL2 (A₀ := A₀) (b := b) hR hρ hq hqE
            (P.finiteBaseLp (A₀ := A₀) (b := b) (q := q) hs hR hρ) N)
          S.backward S.backward_area t x‖ ≤ C * A₀ * R / (1 - ρ / b) := by
  obtain ⟨C, hC, hlabel⟩ := P.exists_finitePeriodicLabel_velocity_bound
  refine ⟨C, hC, ?_⟩
  intro s A₀ b R ρ q T _ hs hA hb hR hRmax hρ hρ1 hρb hq hqE N S t x
  have hwf : P.finiteInitialPeriodicDensity s A₀ b R ρ N =ᵐ[μT]
      (finiteBaseCurlL2 (A₀ := A₀) (b := b) hR hρ hq hqE
        (P.finiteBaseLp (A₀ := A₀) (b := b) (q := q) hs hR hρ) N : R2 → ℝ) := by
    filter_upwards [P.finiteBaseCurlL2_ae_density (A₀ := A₀) (b := b) hs hR hρ hq hqE N,
      ae_restrict_mem measurableSet_torusBox] with y hy hybox
    exact (P.finiteInitialPeriodicDensity_eq_on_box hs hR hRmax hρ hρ1 N hybox).trans hy.symm
  rw [S.particleVelocityRepresentative_eq_raw (P.finiteInitialPeriodicDensity s A₀ b R ρ N) hwf,
    P.torusKernelVelocity_finiteInitialDensity_eq_sum_labels hs hA hb hR hRmax hρ hρ1 N S t x]
  have hκ0 : 0 ≤ ρ / b := div_nonneg hρ.le hb.le
  have hκ1 : ρ / b < 1 := (div_lt_one hb).mpr hρb
  have hsum : ∑ j ∈ Finset.range (N + 1), (ρ / b) ^ j ≤ (1 - ρ / b)⁻¹ := by
    rw [← tsum_geometric_of_lt_one hκ0 hκ1]
    exact (summable_geometric_of_lt_one hκ0 hκ1).sum_le_tsum _ (fun j _ => pow_nonneg hκ0 j)
  have hscale (j : ℕ) : ampScale A₀ b j * radScale R ρ j = (A₀ * R) * (ρ / b) ^ j := by
    simp only [ampScale, radScale, div_pow, div_eq_mul_inv]
    ring
  calc
    _ ≤ ∑ j ∈ Finset.range (N + 1),
        ‖torusKernelVelocity (S.transportedScalar (P.finitePeriodicLabel s A₀ b R ρ N j) t) x‖ :=
      norm_sum_le _ _
    _ ≤ ∑ j ∈ Finset.range (N + 1), (C * (A₀ * R)) * (ρ / b) ^ j := by
      apply Finset.sum_le_sum
      intro j _
      exact (hlabel hs hA hb hR hRmax hρ hρ1 N j S t x).trans_eq (by rw [mul_assoc, hscale]; ring)
    _ = (C * (A₀ * R)) * ∑ j ∈ Finset.range (N + 1), (ρ / b) ^ j := (Finset.mul_sum _ _ _).symm
    _ ≤ (C * (A₀ * R)) * (1 - ρ / b)⁻¹ :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = _ := by ring

end CircularMaterialTransferProfile
end Euler2D

end
