module

public import RequestProject.Euler.CircularFiniteContourPhysicalBounds

/-! One sufficiently old sample of the same material ancient orbit is
strictly within every finite quarter-radius chart, at every cutoff and
physical scale. Admissibility is proved at the same sample. -/

@[expose] public section

set_option maxHeartbeats 2500000

noncomputable section

open Set Filter Topology Metric
open scoped NNReal

namespace Euler2D
namespace CircularMaterialTransferProfile

variable {γ : ℝ≥0} {hγ : 0 < γ} {hγ1 : (γ : ℝ) < 1}
    (P : CircularMaterialTransferProfile hγ hγ1)

theorem exists_common_finiteContour_quarter_sample (M : ℕ) :
    ∃ n : ℕ, M ≤ n ∧ ∀ {R ρ : ℝ}, 0 < R → 0 < ρ → ρ ≤ cellA / 4 →
      ∀ N : ℕ,
        IsAdmissibleLittleContourFamily
          (finiteCircularReferenceC1 hγ hγ1 R ρ : FiniteCircularIndex N → ContourC1Space γ)
          (finiteCircularInterfaceRadius R ρ)
          (finiteCircularInitialContours hγ hγ1 R ρ (P.ancient (-(n : ℝ) * (period + period))) N) ∧
        ∀ p : FiniteCircularIndex N,
          ‖(finiteCircularInitialContours hγ hγ1 R ρ
              (P.ancient (-(n : ℝ) * (period + period))) N p).val -
            finiteCircularReferenceC1 hγ hγ1 R ρ p‖ < finiteCircularInterfaceRadius R ρ p / 4 := by
  let η : ℝ := min (cellA / 32) ((1 - cellA) / 32)
  have hη : 0 < η := lt_min (div_pos cellA_pos (by norm_num))
    (div_pos (sub_pos.mpr cellA_lt_one) (by norm_num))
  have hηa : η ≤ cellA / 16 := by
    have hh := min_le_left (cellA / 32) ((1 - cellA) / 32)
    dsimp only [η]
    linarith [cellA_pos]
  have hηgap : η ≤ (1 - cellA) / 16 := by
    have hh := min_le_right (cellA / 32) ((1 - cellA) / 32)
    dsimp only [η]
    linarith [cellA_lt_one]
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
  have hfinite := finiteCircular_initial_close hγ hγ1 hR hρ hη.le (P.ancient s) hclose N
  refine ⟨admissible_scaledCircular_family_of_close hγ hγ1 hR hρ hρ1 hρa hη.le
    hηa hηgap _ hfinite, ?_⟩
  intro p
  apply (hfinite p).trans_lt
  have hquarter : η < circularContourRadii p.2 / 4 := by
    have hh : η ≤ cellA / 32 := min_le_left _ _
    have hr := (circularContourRadii_bounds p.2).2.1
    linarith [cellA_pos]
  have hm := mul_lt_mul_of_pos_right hquarter (mul_pos hR (pow_pos hρ p.1))
  dsimp only [finiteCircularInterfaceRadius, radScale]
  nlinarith only [hm]

end CircularMaterialTransferProfile
end Euler2D

end
