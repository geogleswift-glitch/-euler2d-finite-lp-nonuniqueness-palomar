module

public import RequestProject.Euler.CircularFinitePlanarClusterVelocity

/-! Exact decomposition of the full same-S physical planar velocity
into actual outer labels and the entire remaining transported cluster. -/

@[expose] public section

set_option maxHeartbeats 2100000

noncomputable section

open Complex ComplexConjugate Set MeasureTheory Metric
open scoped NNReal ENNReal

namespace Euler2D
namespace CircularMaterialTransferProfile

variable {γ : ℝ≥0} {hγ : 0 < γ} {hγ1 : (γ : ℝ) < 1}
    (P : CircularMaterialTransferProfile hγ hγ1)

theorem physicalComplexSource_finiteDensity_eq_sum_labels {s A₀ b R ρ : ℝ} (hs : s ≤ 0)
    (hR : 0 < R) (hRmax : R ≤ 1 / 2) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (N : ℕ) {f : Lp ℝ 2 μT} {T : ℝ} (S : BoundedEulerParticleSystem f T) (t : ℝ) :
    S.physicalComplexSource (P.finiteInitialPeriodicDensity s A₀ b R ρ N) t =
      fun x => ∑ j ∈ Finset.range (N + 1), boxedComplexDensity
        (S.transportedScalar (P.finitePeriodicLabel s A₀ b R ρ N j) t) x := by
  funext x
  by_cases hx : complexTorusPoint x ∈ torusBox
  · simp only [BoundedEulerParticleSystem.physicalComplexSource, boxedComplexDensity, indicator_of_mem hx]
    exact P.transported_finiteInitialDensity_eq_sum_labels hs hR hRmax hρ hρ1 N S t _
  · simp [BoundedEulerParticleSystem.physicalComplexSource, boxedComplexDensity, hx]

theorem velocityC_physicalFiniteDensity_eq_sum_labels {s A₀ b R ρ : ℝ} (hs : s ≤ 0)
    (hA : 0 ≤ A₀) (hb : 0 < b) (hR : 0 < R) (hRmax : R ≤ 1 / 2) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (N : ℕ) {f : Lp ℝ 2 μT} {T : ℝ} (S : BoundedEulerParticleSystem f T) (t : ℝ) (x : ℂ) :
    velocityC (S.physicalComplexSource (P.finiteInitialPeriodicDensity s A₀ b R ρ N) t) x =
      ∑ j ∈ Finset.range (N + 1), velocityC (boxedComplexDensity
        (S.transportedScalar (P.finitePeriodicLabel s A₀ b R ρ N j) t)) x := by
  rw [P.physicalComplexSource_finiteDensity_eq_sum_labels hs hR hRmax hρ hρ1 N S t]
  unfold velocityC
  simp_rw [Complex.ofReal_sum, Finset.sum_mul]
  apply integral_finset_sum
  intro j _
  obtain ⟨hi, hsup, _⟩ := P.boxed_finitePeriodicLabel_bounds hs hA hb hR hRmax hρ hρ1 N j S t
  exact integrable_velocity_integrand hi hsup x

theorem velocityC_physicalFiniteDensity_eq_outer_add_cluster {s A₀ b R ρ : ℝ} (hs : s ≤ 0)
    (hA : 0 ≤ A₀) (hb : 0 < b) (hR : 0 < R) (hRmax : R ≤ 1 / 2) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (N k : ℕ) (hk : k ≤ N) {f : Lp ℝ 2 μT} {T : ℝ} (S : BoundedEulerParticleSystem f T)
    (t : ℝ) (x : ℂ) :
    velocityC (S.physicalComplexSource (P.finiteInitialPeriodicDensity s A₀ b R ρ N) t) x =
      (∑ j ∈ Finset.range (k + 1), velocityC (boxedComplexDensity
        (S.transportedScalar (P.finitePeriodicLabel s A₀ b R ρ N j) t)) x) +
      velocityC (P.finiteInnerClusterComplexSource s A₀ b R ρ N k S t) x := by
  rw [P.velocityC_physicalFiniteDensity_eq_sum_labels hs hA hb hR hRmax hρ hρ1 N S t x,
    P.velocityC_finiteInnerClusterComplexSource_eq_sum hs hA hb hR hRmax hρ hρ1 N k S t x]
  exact (Finset.sum_range_add_sum_Ico _ (Nat.add_le_add_right hk 1)).symm

/-- No velocity or radial-budget hypothesis is used in this split:
all terms are those of the actual same-S transported labels. -/
theorem radial_component_physicalFiniteDensity_le_outer_add_cluster
    {s A₀ b R ρ : ℝ} (hs : s ≤ 0)
    (hA : 0 ≤ A₀) (hb : 0 < b) (hR : 0 < R) (hRmax : R ≤ 1 / 2) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (N k : ℕ) (hk : k ≤ N) {f : Lp ℝ 2 μT} {T : ℝ} (S : BoundedEulerParticleSystem f T)
    (t : ℝ) (x : ℂ) :
    (velocityC (S.physicalComplexSource (P.finiteInitialPeriodicDensity s A₀ b R ρ N) t) x * conj x).re ≤
      (∑ j ∈ Finset.range (k + 1), |(velocityC (boxedComplexDensity
        (S.transportedScalar (P.finitePeriodicLabel s A₀ b R ρ N j) t)) x * conj x).re|) +
      ‖velocityC (P.finiteInnerClusterComplexSource s A₀ b R ρ N k S t) x‖ * ‖x‖ := by
  rw [P.velocityC_physicalFiniteDensity_eq_outer_add_cluster hs hA hb hR hRmax hρ hρ1 N k hk S t x,
    add_mul, add_re, Finset.sum_mul, Complex.re_sum]
  apply add_le_add
  · exact Finset.sum_le_sum (fun j _ => le_abs_self _)
  · calc
      _ ≤ ‖velocityC (P.finiteInnerClusterComplexSource s A₀ b R ρ N k S t) x * conj x‖ :=
        (le_abs_self _).trans (abs_re_le_norm _)
      _ = _ := by rw [norm_mul, norm_conj]

end CircularMaterialTransferProfile
end Euler2D

end
