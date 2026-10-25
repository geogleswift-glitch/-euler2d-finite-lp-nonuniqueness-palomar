module

public import RequestProject.Euler.WeightedInteractionRowBudget
public import RequestProject.Euler.Reset

/-! Quantitative whole-stage bounds for the weighted norm integral
inequality. The original current growth sigma is retained; only the
ancestor propagation exponent is replaced by the true b*K bound. -/

@[expose] public section

set_option maxHeartbeats 4000000

noncomputable section

open Set Filter Topology MeasureTheory

namespace Euler2D

theorem exists_weighted_stage_envelope_bound {ν₀ : ℝ} (hν₀ : 0 < ν₀) :
    ∃ Ctail : ℝ, 0 ≤ Ctail ∧ ∀ {σ ν νbar C₀ ρ L Ccur Cpoly E₀ δ D t Z₀ Zt : ℝ},
      ν₀ ≤ ν → ν ≤ νbar → νbar < σ → 0 < C₀ → 0 < ρ →
      0 ≤ L → 0 ≤ Ccur → 0 ≤ Cpoly → 0 ≤ E₀ →
      0 ≤ t → t ≤ D → E₀ * Real.exp (σ * D) ≤ δ →
      Z₀ ≤ L * (C₀ * ρ ^ 6) →
      ∀ R : ℝ → ℝ, ContinuousOn R (Icc 0 t) →
      (∀ s ∈ Icc 0 t, R s ≤ Cpoly * ρ ^ 6 * (1 + s) ^ 4) →
      Zt ≤ Z₀ * Real.exp (ν * t) +
        (Ccur / C₀) * (∫ s in (0)..t, Real.exp (ν * (t - s)) * (E₀ * Real.exp (σ * s))) +
        (∫ s in (0)..t, Real.exp (ν * (t - s)) * R s) →
      Zt ≤ (L + Cpoly * Ctail / C₀) * (C₀ * ρ ^ 6) * Real.exp (ν * D) +
        Ccur * δ / (C₀ * (σ - νbar)) := by
  obtain ⟨Ctail, hCt, htail⟩ := integral_exp_poly_le hν₀
  refine ⟨Ctail, hCt, ?_⟩
  intro σ ν νbar C₀ ρ L Ccur Cpoly E₀ δ D t Z₀ Zt hν₀ν hν hgap hC₀ hρ hL hcur hpoly hE₀
    ht htD hEmax hZ₀ R hRc hR hZ
  have hν0 : 0 ≤ ν := hν₀.le.trans hν₀ν
  have hσ0 : 0 < σ := hν₀.trans_le (hν₀ν.trans (hν.trans hgap.le))
  have hexp : Real.exp (ν * t) ≤ Real.exp (ν * D) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left htD hν0)
  have hEtime : E₀ * Real.exp (σ * t) ≤ δ :=
    (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_left htD hσ0.le)) hE₀).trans hEmax
  have hI := (integral_exp_envelope_le hν hgap hE₀).trans
    (div_le_div_of_nonneg_right hEtime (sub_pos.mpr hgap).le)
  have hIcur := mul_le_mul_of_nonneg_left hI (div_nonneg hcur hC₀.le)
  have hIR : (∫ s in (0)..t, Real.exp (ν * (t - s)) * R s) ≤
      Cpoly * ρ ^ 6 * Ctail * Real.exp (ν * D) := by
    calc
      _ ≤ ∫ s in (0)..t, (Cpoly * ρ ^ 6) *
          (Real.exp (ν * (t - s)) * (1 + s) ^ 4) := by
        apply intervalIntegral.integral_mono_on ht
        · apply ContinuousOn.intervalIntegrable
          rw [uIcc_of_le ht]
          exact (by fun_prop : ContinuousOn (fun s : ℝ => Real.exp (ν * (t - s))) (Icc 0 t)).mul hRc
        · exact (by fun_prop : Continuous (fun s : ℝ => (Cpoly * ρ ^ 6) *
            (Real.exp (ν * (t - s)) * (1 + s) ^ 4))).intervalIntegrable 0 t
        · intro s hs
          have hh := mul_le_mul_of_nonneg_left (hR s hs) (Real.exp_pos (ν * (t - s))).le
          convert hh using 1 <;> ring
      _ = (Cpoly * ρ ^ 6) * ∫ s in (0)..t, Real.exp (ν * (t - s)) * (1 + s) ^ 4 :=
        intervalIntegral.integral_const_mul _ _
      _ ≤ (Cpoly * ρ ^ 6) * (Ctail * Real.exp (ν * t)) :=
        mul_le_mul_of_nonneg_left (htail ν t hν₀ν ht) (by positivity)
      _ ≤ Cpoly * ρ ^ 6 * Ctail * Real.exp (ν * D) := by
        have hh := mul_le_mul_of_nonneg_left hexp (by positivity : 0 ≤ Cpoly * ρ ^ 6 * Ctail)
        convert hh using 1 <;> ring
  have hIinitial : Z₀ * Real.exp (ν * t) ≤ L * (C₀ * ρ ^ 6) * Real.exp (ν * D) :=
    (mul_le_mul_of_nonneg_right hZ₀ (Real.exp_pos _).le).trans
      (mul_le_mul_of_nonneg_left hexp (by positivity))
  calc
    Zt ≤ _ := hZ
    _ ≤ L * (C₀ * ρ ^ 6) * Real.exp (ν * D) +
        (Ccur / C₀) * (δ / (σ - νbar)) + Cpoly * ρ ^ 6 * Ctail * Real.exp (ν * D) :=
      add_le_add (add_le_add hIinitial hIcur) hIR
    _ = _ := by field_simp [hC₀.ne']; ring

theorem weighted_stage_decay_exponent_pos {σ νbar : ℝ} (hσ : 0 < σ) (hgap : νbar < σ) :
    0 < 6 - νbar * (6 / σ) := by
  have heq : 6 - νbar * (6 / σ) = 6 * (σ - νbar) / σ := by field_simp
  rw [heq]
  exact div_pos (mul_pos (by norm_num) (sub_pos.mpr hgap)) hσ

theorem eventually_weighted_stage_transient_small {σ νbar A D₀ ε : ℝ}
    (hσ : 0 < σ) (hgap : νbar < σ) (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop,
      A * Real.exp (νbar * D₀) * Real.exp (-(6 - νbar * (6 / σ)) * x) ≤ ε := by
  have hc := weighted_stage_decay_exponent_pos hσ hgap
  have hlin : Tendsto (fun x : ℝ => (6 - νbar * (6 / σ)) * x) atTop atTop :=
    tendsto_id.const_mul_atTop hc
  have hh := (Real.tendsto_exp_neg_atTop_nhds_zero.comp hlin).const_mul (A * Real.exp (νbar * D₀))
  have hlim : Tendsto (fun x : ℝ => A * Real.exp (νbar * D₀) *
      Real.exp (-(6 - νbar * (6 / σ)) * x)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, mul_zero, neg_mul] using hh
  exact (hlim.eventually (gt_mem_nhds hε)).mono (fun _ hx => hx.le)

end Euler2D

end
