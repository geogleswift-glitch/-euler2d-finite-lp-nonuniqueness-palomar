module

public import RequestProject.Euler.BanachNonlinearKernelOrbit
public import RequestProject.Euler.BanachObservableDeparture

/-! An actual backward-orbit construction with arbitrarily small
graph error produces an orbit detected by a genuine observable. -/

@[expose] public section

set_option maxHeartbeats 1500000

noncomputable section

open Set Filter Topology Metric

namespace Euler2D

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup H] [NormedSpace ℝ H]

def HasFlatBackwardOrbits (F : E → E) (P : E →L[ℝ] E) (ρ : ℝ) : Prop :=
  ∀ ε > 0, ∀ rmax > 0, ∃ r > 0, r ≤ rmax ∧ ∀ ξ : E, P ξ = ξ → ‖ξ‖ ≤ r / 2 →
    ∃ x : ℕ → E,
      (∀ n, F (x (n + 1)) = x n) ∧
      (∀ n, x n ∈ closedBall 0 r) ∧
      (∀ n, ‖x n‖ ≤ 2 * (ρ⁻¹) ^ n * ‖ξ‖) ∧
      P (x 0) = ξ ∧ ‖x 0 - ξ‖ ≤ ε * ‖ξ‖ ∧ Tendsto x atTop (𝓝 (0 : E))

theorem exists_backwardOrbit_with_observable_departure
    {F : E → E} {P : E →L[ℝ] E} {ρ : ℝ} (horbit : HasFlatBackwardOrbits F P ρ)
    {φ : E → H} {D : E →L[ℝ] H} (hφ : HasFDerivAt φ D 0)
    (g : E) (hPg : P g = g) (hg : D g ≠ 0) {rmax : ℝ} (hrmax : 0 < rmax) :
    ∃ t > 0, ∃ x : ℕ → E,
      (∀ n, F (x (n + 1)) = x n) ∧
      (∀ n, x n ∈ closedBall 0 rmax) ∧
      (∀ n, ‖x n‖ ≤ 2 * (ρ⁻¹) ^ n * ‖t • g‖) ∧
      P (x 0) = t • g ∧ (‖D g‖ / 2) * t ≤ ‖φ (x 0) - φ 0‖ ∧
      φ (x 0) ≠ φ 0 ∧ Tendsto x atTop (𝓝 (0 : E)) := by
  obtain ⟨ε, hε, r₁, hr₁, hcone⟩ := exists_observable_departure_cone hφ g hg
  let cap := min rmax (r₁ / 2)
  have hcap : 0 < cap := lt_min hrmax (half_pos hr₁)
  obtain ⟨r, hr, hrcap, horb⟩ := horbit ε hε cap hcap
  let t : ℝ := r / (4 * (‖g‖ + 1))
  have hden : 0 < 4 * (‖g‖ + 1) := by positivity
  have ht : 0 < t := div_pos hr hden
  have hteq : t * (4 * (‖g‖ + 1)) = r := div_mul_cancel₀ r hden.ne'
  have htnorm : ‖t • g‖ = t * ‖g‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht]
  have htr : ‖t • g‖ ≤ r / 2 := by rw [htnorm]; nlinarith [norm_nonneg g]
  have hPt : P (t • g) = t • g := by rw [P.map_smul, hPg]
  obtain ⟨x, hback, hball, hnorm, hproj, hgraph, hlim⟩ := horb (t • g) hPt htr
  have hrmax' : r ≤ rmax := hrcap.trans (min_le_left _ _)
  have hrcone : r < r₁ := lt_of_le_of_lt (hrcap.trans (min_le_right _ _)) (half_lt_self hr₁)
  have hxball : x 0 ∈ ball 0 r₁ := closedBall_subset_ball hrcone (hball 0)
  have hxnorm : ‖x 0‖ ≤ 2 * |t| * ‖g‖ := by
    have h := hnorm 0
    simpa only [pow_zero, mul_one, htnorm, abs_of_pos ht, mul_assoc] using h
  have hxgraph : ‖x 0 - t • g‖ ≤ ε * |t| * ‖g‖ := by
    simpa only [htnorm, abs_of_pos ht, mul_assoc] using hgraph
  have hdep := hcone t (x 0) hxball hxnorm hxgraph
  rw [abs_of_pos ht] at hdep
  have hne : φ (x 0) ≠ φ 0 := by
    intro hz
    rw [hz, sub_self, norm_zero] at hdep
    have hp : 0 < (‖D g‖ / 2) * t := mul_pos (half_pos (norm_pos_iff.mpr hg)) ht
    linarith
  exact ⟨t, ht, x, hback, fun n => closedBall_subset_closedBall hrmax' (hball n),
    hnorm, hproj, hdep, hne, hlim⟩

end Euler2D

end
