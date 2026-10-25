module

public import RequestProject.Euler.CircularFiniteLabelBounds

/-! The actual labelled finite sum is transported by the same Euler map.
Each genuine label retains its own mass and amplitude bounds. -/

@[expose] public section

set_option maxHeartbeats 2400000

noncomputable section

open MeasureTheory Set Filter Topology Metric Real
open scoped NNReal ENNReal

namespace Euler2D
namespace CircularMaterialTransferProfile

variable {γ : ℝ≥0} {hγ : 0 < γ} {hγ1 : (γ : ℝ) < 1}
    (P : CircularMaterialTransferProfile hγ hγ1)

theorem finitePeriodicLabel_bounds {s A₀ b R ρ : ℝ} (hs : s ≤ 0)
    (hA : 0 ≤ A₀) (hb : 0 < b) (hR : 0 < R) (hRmax : R ≤ 1 / 2)
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (N j : ℕ) :
    Integrable (P.finitePeriodicLabel s A₀ b R ρ N j) μT ∧
      IsTorusPeriodic (P.finitePeriodicLabel s A₀ b R ρ N j) ∧
      (∀ x, ‖P.finitePeriodicLabel s A₀ b R ρ N j x‖ ≤
        finiteLabelAmplitudeBound * ampScale A₀ b j) ∧
      (∫ x in torusBox, |P.finitePeriodicLabel s A₀ b R ρ N j x|) ≤
        finiteLabelMassBound * ampScale A₀ b j * radScale R ρ j ^ 2 := by
  have hz := P.finitePlanarLabel_zero_of_one_le_norm (A₀ := A₀) (b := b) hs hR hRmax hρ hρ1 N j
  refine ⟨integrable_periodicCenteredSource (P.integrable_finitePlanarLabel hs hR hρ N j) hz,
    isTorusPeriodic_periodicCenteredSource _, ?_, ?_⟩
  · exact norm_periodicCenteredSource_le hz (P.norm_finitePlanarLabel_le hs hA hb N j)
  · rw [finitePeriodicLabel, integral_abs_periodicCenteredSource hz]
    exact P.integral_abs_finitePlanarLabel_le hs hA hb hR hρ N j

theorem exists_finitePeriodicLabel_velocity_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ {s A₀ b R ρ : ℝ}, s ≤ 0 → 0 ≤ A₀ → 0 < b →
      0 < R → R ≤ 1 / 2 → 0 < ρ → ρ ≤ 1 → ∀ N j : ℕ,
      ∀ {f : Lp ℝ 2 μT} {T : ℝ} (S : BoundedEulerParticleSystem f T), ∀ t x,
        ‖torusKernelVelocity (S.transportedScalar (P.finitePeriodicLabel s A₀ b R ρ N j) t) x‖ ≤
          C * ampScale A₀ b j * radScale R ρ j := by
  obtain ⟨C, hC, hbound⟩ := exists_torusKernelVelocity_scaled_mass_amplitude_bound
  let B := finiteLabelAmplitudeBound + finiteLabelMassBound + C * finiteLabelMassBound
  have hB : 0 < B := by
    have hi : (4 : ℝ) ≤ finiteLabelAmplitudeBound := le_max_left _ _
    dsimp only [B]
    nlinarith [finiteLabelMassBound_nonneg, mul_nonneg hC finiteLabelMassBound_nonneg]
  refine ⟨B, hB, ?_⟩
  intro s A₀ b R ρ hs hA hb hR hRmax hρ hρ1 N j f T S t x
  obtain ⟨hi, hp, hsup, hm⟩ := P.finitePeriodicLabel_bounds hs hA hb hR hRmax hρ hρ1 N j
  have hrj : 0 < radScale R ρ j := mul_pos hR (pow_pos hρ j)
  have hrj1 : radScale R ρ j ≤ 1 :=
    (mul_le_of_le_one_right hR.le (pow_le_one₀ hρ.le hρ1)).trans (by linarith)
  exact hbound (S.integrable_transportedScalar_of_integrable hi t)
    (div_nonneg hA (pow_pos hb j).le) hrj hrj1 finiteLabelMassBound_nonneg finiteLabelAmplitudeBound_nonneg
    (S.norm_transportedScalar_ae_le (ae_of_all _ hsup) t)
    (by rwa [S.integral_abs_transportedScalar hi hp t]) x

theorem finiteInitialPlanarDensity_eq_sum_labels (s A₀ b R ρ : ℝ) (N : ℕ) (x : R2) :
    P.finiteInitialPlanarDensity s A₀ b R ρ N x =
      ∑ j ∈ Finset.range (N + 1), P.finitePlanarLabel s A₀ b R ρ N j x := by
  rw [Finset.sum_range_succ]
  have he : (∑ j ∈ Finset.range N, P.finitePlanarLabel s A₀ b R ρ N j x) =
      ∑ j ∈ Finset.range N, datumTerm A₀ b R ρ j x := by
    apply Finset.sum_congr rfl
    intro j hj
    simp only [finitePlanarLabel, if_neg (Nat.ne_of_lt (Finset.mem_range.mp hj))]
  rw [he]
  simp only [finitePlanarLabel, if_pos rfl, ite_true, finiteInitialPlanarDensity]

theorem finiteInitialPeriodicDensity_eq_sum_labels {s A₀ b R ρ : ℝ} (hs : s ≤ 0)
    (hR : 0 < R) (hRmax : R ≤ 1 / 2) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (N : ℕ) (x : R2) :
    P.finiteInitialPeriodicDensity s A₀ b R ρ N x =
      ∑ j ∈ Finset.range (N + 1), P.finitePeriodicLabel s A₀ b R ρ N j x := by
  have hz : ∀ y : R2, 1 ≤ ‖y‖ → P.finiteInitialPlanarDensity s A₀ b R ρ N y = 0 :=
    fun y hy => P.finiteInitialPlanarDensity_eq_zero hs hR hRmax hρ hρ1 N hy
  change periodicCenteredSource (P.finiteInitialPlanarDensity s A₀ b R ρ N) x = _
  rw [periodicCenteredSource_eq_wrapped hz x,
    P.finiteInitialPlanarDensity_eq_sum_labels]
  apply Finset.sum_congr rfl
  intro j _
  exact (periodicCenteredSource_eq_wrapped
    (P.finitePlanarLabel_zero_of_one_le_norm hs hR hRmax hρ hρ1 N j) x).symm

theorem transported_finiteInitialDensity_eq_sum_labels {s A₀ b R ρ : ℝ} (hs : s ≤ 0)
    (hR : 0 < R) (hRmax : R ≤ 1 / 2) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (N : ℕ)
    {f : Lp ℝ 2 μT} {T : ℝ} (S : BoundedEulerParticleSystem f T) (t : ℝ) (x : R2) :
    S.transportedScalar (P.finiteInitialPeriodicDensity s A₀ b R ρ N) t x =
      ∑ j ∈ Finset.range (N + 1),
        S.transportedScalar (P.finitePeriodicLabel s A₀ b R ρ N j) t x :=
  P.finiteInitialPeriodicDensity_eq_sum_labels hs hR hRmax hρ hρ1 N _

theorem torusKernelVelocity_finiteInitialDensity_eq_sum_labels {s A₀ b R ρ : ℝ} (hs : s ≤ 0)
    (hA : 0 ≤ A₀) (hb : 0 < b) (hR : 0 < R) (hRmax : R ≤ 1 / 2) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (N : ℕ) {f : Lp ℝ 2 μT} {T : ℝ} (S : BoundedEulerParticleSystem f T) (t : ℝ) (x : R2) :
    torusKernelVelocity (S.transportedScalar (P.finiteInitialPeriodicDensity s A₀ b R ρ N) t) x =
      ∑ j ∈ Finset.range (N + 1),
        torusKernelVelocity (S.transportedScalar (P.finitePeriodicLabel s A₀ b R ρ N j) t) x := by
  have hi (j : ℕ) : Integrable (fun y =>
      S.transportedScalar (P.finitePeriodicLabel s A₀ b R ρ N j) t y •
        torusBiotSavartKernel (x - y + torusCenter)) μT := by
    obtain ⟨hij, hpj, hsup, _⟩ := P.finitePeriodicLabel_bounds hs hA hb hR hRmax hρ hρ1 N j
    exact integrable_torusKernelVelocity_integrand
      (S.integrable_transportedScalar_of_integrable hij t).aestronglyMeasurable
      (S.norm_transportedScalar_ae_le (ae_of_all _ hsup) t) x
  unfold torusKernelVelocity
  simp_rw [P.transported_finiteInitialDensity_eq_sum_labels hs hR hRmax hρ hρ1 N S t,
    Finset.sum_smul]
  exact integral_finset_sum _ (fun j _ => hi j)

end CircularMaterialTransferProfile
end Euler2D

end
