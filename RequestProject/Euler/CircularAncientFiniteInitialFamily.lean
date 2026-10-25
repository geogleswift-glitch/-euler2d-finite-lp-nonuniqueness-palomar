module

public import RequestProject.Euler.CircularFiniteContourInitialData

/-! A common actual ancient entrance for every finite cutoff. The
entrance is selected from the already constructed same ancient curve;
the complete original finite contour domain is then genuinely inhabited. -/

@[expose] public section

set_option maxHeartbeats 2500000

noncomputable section

open Set Filter Topology Metric
open scoped NNReal

namespace Euler2D

theorem finiteCircularInterfaceRadius_pos {R ρ : ℝ} (hR : 0 < R) (hρ : 0 < ρ)
    {N : ℕ} (p : FiniteCircularIndex N) : 0 < finiteCircularInterfaceRadius R ρ p :=
  mul_pos (mul_pos hR (pow_pos hρ p.1)) (circularContourRadii_bounds p.2).1

theorem lift_finiteCircularReferenceC1 {γ : ℝ≥0} (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1)
    (R ρ : ℝ) {N : ℕ} (p : FiniteCircularIndex N) :
    ContourC1Space.lift γ (finiteCircularReferenceC1 hγ hγ1 R ρ p) =
      refCircle (finiteCircularInterfaceRadius R ρ p) := by
  funext θ
  change radScale R ρ p.1 • refCircle (circularContourRadii p.2) θ = _
  simp only [finiteCircularInterfaceRadius, refCircle, Complex.real_smul, Complex.ofReal_mul]
  ring

namespace CircularMaterialTransferProfile

variable {γ : ℝ≥0} {hγ : 0 < γ} {hγ1 : (γ : ℝ) < 1}
    (P : CircularMaterialTransferProfile hγ hγ1)

theorem exists_common_finiteContour_sample (M : ℕ) :
    ∃ n : ℕ, M ≤ n ∧ ∀ {R ρ : ℝ}, 0 < R → 0 < ρ → ρ ≤ cellA / 4 →
      ∀ N : ℕ, IsAdmissibleLittleContourFamily
        (finiteCircularReferenceC1 hγ hγ1 R ρ : FiniteCircularIndex N → ContourC1Space γ)
        (finiteCircularInterfaceRadius R ρ)
        (finiteCircularInitialContours hγ hγ1 R ρ (P.ancient (-(n : ℝ) * (period + period))) N) := by
  let η : ℝ := min (cellA / 16) ((1 - cellA) / 16)
  have hη : 0 < η := lt_min (div_pos cellA_pos (by norm_num))
    (div_pos (sub_pos.mpr cellA_lt_one) (by norm_num))
  obtain ⟨n, hn, hMn⟩ :=
    ((P.ancient_samples_tendsto.eventually
      (ball_mem_nhds (littleCircularReference hγ hγ1) hη)).and (eventually_ge_atTop M)).exists
  let s := -(n : ℝ) * (period + period)
  have hn' : ‖P.ancient s - littleCircularReference hγ hγ1‖ < η := by
    simpa only [mem_ball, dist_eq_norm] using hn
  have hclose (i : Fin 2) : ‖(P.ancient s i).val - circularReferenceC1 hγ hγ1 i‖ ≤ η :=
    (norm_le_pi_norm (P.ancient s - littleCircularReference hγ hγ1) i).trans hn'.le
  refine ⟨n, hMn, ?_⟩
  intro R ρ hR hρ hρa N
  have hρ1 : ρ ≤ 1 := by linarith [cellA_lt_one]
  exact admissible_scaledCircular_family_of_close hγ hγ1 hR hρ hρ1 hρa hη.le
    (min_le_left _ _) (min_le_right _ _)
    (finiteCircularInitialContours hγ hγ1 R ρ (P.ancient s) N)
    (finiteCircular_initial_close hγ hγ1 hR hρ hη.le (P.ancient s) hclose N)

theorem exists_common_finiteContour_entrance :
    ∃ s : ℝ, s ≤ 0 ∧ ∀ {R ρ : ℝ}, 0 < R → 0 < ρ → ρ ≤ cellA / 4 →
      ∀ N : ℕ, IsAdmissibleLittleContourFamily
        (finiteCircularReferenceC1 hγ hγ1 R ρ : FiniteCircularIndex N → ContourC1Space γ)
        (finiteCircularInterfaceRadius R ρ)
        (finiteCircularInitialContours hγ hγ1 R ρ (P.ancient s) N) := by
  obtain ⟨n, _, hn⟩ := P.exists_common_finiteContour_sample 0
  exact ⟨-(n : ℝ) * (period + period),
    mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (Nat.cast_nonneg n))
      (by dsimp only [period]; positivity), hn⟩

end CircularMaterialTransferProfile

end Euler2D

end
