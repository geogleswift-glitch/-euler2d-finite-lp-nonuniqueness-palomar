module

public import RequestProject.Euler.WeightedTrajectoryStageBounds

/-! Uniform closure of the actual weighted scalar budget on a full
logarithmic capture horizon. All constants and the original sigma
are fixed before rho=exp(-x) and before the finite cutoff. -/

@[expose] public section

set_option maxHeartbeats 4000000

noncomputable section

open Set Filter Topology MeasureTheory

namespace Euler2D

theorem weighted_stage_transient_le {σ ν νbar A C₀ D D₀ x : ℝ}
    (hσ : 0 < σ) (hν0 : 0 ≤ ν) (hν : ν ≤ νbar) (hA : 0 ≤ A) (hC₀ : 0 ≤ C₀)
    (hD : 0 ≤ D) (hclock : D ≤ (6 / σ) * x + D₀) :
    A * (C₀ * (Real.exp (-x)) ^ 6) * Real.exp (ν * D) ≤
      (A * C₀) * Real.exp (νbar * D₀) * Real.exp (-(6 - νbar * (6 / σ)) * x) := by
  have hνbar : 0 ≤ νbar := hν0.trans hν
  have htime : ν * D ≤ νbar * ((6 / σ) * x + D₀) :=
    (mul_le_mul_of_nonneg_right hν hD).trans (mul_le_mul_of_nonneg_left hclock hνbar)
  have heq : (Real.exp (-x)) ^ 6 * Real.exp (ν * D) = Real.exp (-6 * x + ν * D) := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    ring
  have he : Real.exp (-6 * x + ν * D) ≤
      Real.exp (νbar * D₀) * Real.exp (-(6 - νbar * (6 / σ)) * x) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith only [htime]
  calc
    _ = (A * C₀) * Real.exp (-6 * x + ν * D) := by rw [← heq]; ring
    _ ≤ _ := by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left he (mul_nonneg hA hC₀)

theorem eventually_uniform_weighted_stage_transient_small {σ νbar A C₀ D₀ ε : ℝ}
    (hσ : 0 < σ) (hgap : νbar < σ) (hA : 0 ≤ A) (hC₀ : 0 ≤ C₀) (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop, ∀ ν D : ℝ, 0 ≤ ν → ν ≤ νbar → 0 ≤ D →
      D ≤ (6 / σ) * x + D₀ →
      A * (C₀ * (Real.exp (-x)) ^ 6) * Real.exp (ν * D) ≤ ε := by
  filter_upwards [eventually_weighted_stage_transient_small (A := A * C₀) (D₀ := D₀) hσ hgap hε] with x hx
  intro ν D hν0 hν hD hclock
  exact (weighted_stage_transient_le hσ hν0 hν hA hC₀ hD hclock).trans hx

theorem exists_uniform_weighted_stage_closure {σ ν₀ νbar : ℝ}
    (hσ : 0 < σ) (hν₀ : 0 < ν₀) (hgap : νbar < σ) :
    ∃ Ctail : ℝ, 0 ≤ Ctail ∧ ∀ {C₀ L Ccur Cpoly δ D₀ K : ℝ},
      0 < C₀ → 0 ≤ L → 0 ≤ Ccur → 0 ≤ Cpoly → 0 < K →
      Ccur * δ / (C₀ * (σ - νbar)) ≤ K / 2 →
      ∀ᶠ x : ℝ in atTop, ∀ {ν E₀ D t Z₀ Zt : ℝ},
        ν₀ ≤ ν → ν ≤ νbar → 0 ≤ E₀ → 0 ≤ t → t ≤ D →
        D ≤ (6 / σ) * x + D₀ → E₀ * Real.exp (σ * D) ≤ δ →
        Z₀ ≤ L * (C₀ * (Real.exp (-x)) ^ 6) →
        ∀ R : ℝ → ℝ, ContinuousOn R (Icc 0 t) →
        (∀ s ∈ Icc 0 t, R s ≤ Cpoly * (Real.exp (-x)) ^ 6 * (1 + s) ^ 4) →
        Zt ≤ Z₀ * Real.exp (ν * t) +
          (Ccur / C₀) * (∫ s in (0)..t, Real.exp (ν * (t - s)) * (E₀ * Real.exp (σ * s))) +
          (∫ s in (0)..t, Real.exp (ν * (t - s)) * R s) →
        Zt ≤ K := by
  obtain ⟨Ctail, hCt, hbound⟩ := exists_weighted_stage_envelope_bound hν₀
  refine ⟨Ctail, hCt, ?_⟩
  intro C₀ L Ccur Cpoly δ D₀ K hC₀ hL hcur hpoly hK hcurrent
  have hA : 0 ≤ L + Cpoly * Ctail / C₀ := by positivity
  filter_upwards [eventually_uniform_weighted_stage_transient_small (D₀ := D₀)
    hσ hgap hA hC₀.le (half_pos hK)] with x hx
  intro ν E₀ D t Z₀ Zt hν₀ν hν hE₀ ht htD hclock hEmax hZ₀ R hRc hR hZ
  have hstage := hbound hν₀ν hν hgap hC₀ (Real.exp_pos (-x)) hL hcur hpoly hE₀
    ht htD hEmax hZ₀ R hRc hR hZ
  have hsmall := hx ν D (hν₀.le.trans hν₀ν) hν (ht.trans htD) hclock
  linarith only [hstage, hsmall, hcurrent]

end Euler2D

end
