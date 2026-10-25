module

public import RequestProject.Euler.CircularFiniteUniformSupport

/-! The actual inner cluster consists of the same transported finite
labels. Its global periodic velocity has the original child/parent
geometric scale, uniformly in the finite cutoff. -/

@[expose] public section

set_option maxHeartbeats 2300000

noncomputable section

open MeasureTheory Set Filter Topology Metric Real
open scoped NNReal ENNReal

namespace Euler2D
namespace CircularMaterialTransferProfile

variable {γ : ℝ≥0} {hγ : 0 < γ} {hγ1 : (γ : ℝ) < 1}
    (P : CircularMaterialTransferProfile hγ hγ1)

def finiteInnerClusterSource (s A₀ b R ρ : ℝ) (N k : ℕ)
    {f : Lp ℝ 2 μT} {T : ℝ} (S : BoundedEulerParticleSystem f T) (t : ℝ) (x : R2) : ℝ :=
  ∑ j ∈ Finset.Ico (k + 1) (N + 1),
    S.transportedScalar (P.finitePeriodicLabel s A₀ b R ρ N j) t x

theorem torusKernelVelocity_finiteInnerCluster_eq_sum {s A₀ b R ρ : ℝ} (hs : s ≤ 0)
    (hA : 0 ≤ A₀) (hb : 0 < b) (hR : 0 < R) (hRmax : R ≤ 1 / 2) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (N k : ℕ) {f : Lp ℝ 2 μT} {T : ℝ} (S : BoundedEulerParticleSystem f T) (t : ℝ) (x : R2) :
    torusKernelVelocity (P.finiteInnerClusterSource s A₀ b R ρ N k S t) x =
      ∑ j ∈ Finset.Ico (k + 1) (N + 1),
        torusKernelVelocity (S.transportedScalar (P.finitePeriodicLabel s A₀ b R ρ N j) t) x := by
  have hi (j : ℕ) : Integrable (fun y =>
      S.transportedScalar (P.finitePeriodicLabel s A₀ b R ρ N j) t y •
        torusBiotSavartKernel (x - y + torusCenter)) μT := by
    obtain ⟨hij, _, hsup, _⟩ := P.finitePeriodicLabel_bounds hs hA hb hR hRmax hρ hρ1 N j
    exact integrable_torusKernelVelocity_integrand
      (S.integrable_transportedScalar_of_integrable hij t).aestronglyMeasurable
      (S.norm_transportedScalar_ae_le (ae_of_all _ hsup) t) x
  unfold torusKernelVelocity finiteInnerClusterSource
  simp_rw [Finset.sum_smul]
  exact integral_finset_sum _ (fun j _ => hi j)

theorem exists_uniform_finiteInnerCluster_velocity_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ {s A₀ b R ρ : ℝ}, s ≤ 0 → 0 ≤ A₀ → 0 < b →
      0 < R → R ≤ 1 / 2 → 0 < ρ → ρ ≤ 1 → ρ < b →
      ∀ N k : ℕ, ∀ {f : Lp ℝ 2 μT} {T : ℝ} (S : BoundedEulerParticleSystem f T), ∀ t x,
        ‖torusKernelVelocity (P.finiteInnerClusterSource s A₀ b R ρ N k S t) x‖ ≤
          C * ampScale A₀ b k * radScale R ρ k * (ρ / b) / (1 - ρ / b) := by
  obtain ⟨C, hC, hlabel⟩ := P.exists_finitePeriodicLabel_velocity_bound
  refine ⟨C, hC, ?_⟩
  intro s A₀ b R ρ hs hA hb hR hRmax hρ hρ1 hρb N k f T S t x
  rw [P.torusKernelVelocity_finiteInnerCluster_eq_sum hs hA hb hR hRmax hρ hρ1 N k S t x]
  have hκ0 : 0 ≤ ρ / b := div_nonneg hρ.le hb.le
  have hκ1 : ρ / b < 1 := (div_lt_one hb).mpr hρb
  have hsum : ∑ j ∈ Finset.Ico (k + 1) (N + 1), (ρ / b) ^ j ≤
      (ρ / b) ^ (k + 1) / (1 - ρ / b) := geom_sum_Ico_le_of_lt_one hκ0 hκ1
  have hscale (j : ℕ) : ampScale A₀ b j * radScale R ρ j = (A₀ * R) * (ρ / b) ^ j := by
    simp only [ampScale, radScale, div_pow, div_eq_mul_inv]
    ring
  calc
    _ ≤ ∑ j ∈ Finset.Ico (k + 1) (N + 1),
        ‖torusKernelVelocity (S.transportedScalar (P.finitePeriodicLabel s A₀ b R ρ N j) t) x‖ :=
      norm_sum_le _ _
    _ ≤ ∑ j ∈ Finset.Ico (k + 1) (N + 1), (C * (A₀ * R)) * (ρ / b) ^ j := by
      apply Finset.sum_le_sum
      intro j _
      exact (hlabel hs hA hb hR hRmax hρ hρ1 N j S t x).trans_eq (by rw [mul_assoc, hscale]; ring)
    _ = (C * (A₀ * R)) * ∑ j ∈ Finset.Ico (k + 1) (N + 1), (ρ / b) ^ j :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ (C * (A₀ * R)) * ((ρ / b) ^ (k + 1) / (1 - ρ / b)) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = _ := by
      conv_rhs => rw [mul_assoc C, hscale]
      rw [pow_succ]
      ring

end CircularMaterialTransferProfile
end Euler2D

end
