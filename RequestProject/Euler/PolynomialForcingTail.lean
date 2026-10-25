module

public import RequestProject.Euler.Laplace

/-! A fixed late entrance makes the polynomial forcing tail small
in the original exponential capture weight, uniformly in every later
finite endpoint. -/

@[expose] public section

set_option maxHeartbeats 4000000

noncomputable section

open Filter Topology Set MeasureTheory Asymptotics

namespace Euler2D

def polynomialForcingTail (σ S : ℝ) : ℝ :=
  ∫ u in Ici S, Real.exp (-σ * u) * (1 + u) ^ 4

theorem integrableOn_exponential_polynomial_four {σ : ℝ} (hσ : 0 < σ) :
    IntegrableOn (fun u : ℝ => Real.exp (-σ * u) * (1 + u) ^ 4) (Ici (0 : ℝ)) := by
  have hpoly : (fun u : ℝ => (1 + u) ^ 4) =O[atTop] (fun u => Real.exp ((σ / 2) * u)) := by
    exact (onePlus_rpow_isBigO (d := (4 : ℝ)) (half_pos hσ)).congr_left
      (fun u => Real.rpow_natCast (1 + u) 4)
  have hprod := (isBigO_refl (fun u : ℝ => Real.exp (-σ * u)) atTop).mul hpoly
  have hbig : (fun u : ℝ => Real.exp (-σ * u) * (1 + u) ^ 4) =O[atTop]
      (fun u => Real.exp (-(σ / 2) * u)) := by
    apply hprod.congr_right
    intro u
    rw [← Real.exp_add]
    congr 1
    ring
  have hc : Continuous (fun u : ℝ => Real.exp (-σ * u) * (1 + u) ^ 4) := by fun_prop
  exact (hc.locallyIntegrable.locallyIntegrableOn (Ici (0 : ℝ))).integrableOn_of_isBigO_atTop hbig
    (integrableAtFilter_exp_atTop (half_pos hσ))

theorem tendsto_polynomialForcingTail {σ : ℝ} (hσ : 0 < σ) :
    Tendsto (polynomialForcingTail σ) atTop (𝓝 0) := by
  let g : ℝ → ℝ := (Ici (0 : ℝ)).indicator (fun u => Real.exp (-σ * u) * (1 + u) ^ 4)
  have hg : Integrable g := (integrable_indicator_iff measurableSet_Ici).mpr
    (integrableOn_exponential_polynomial_four hσ)
  have ht : Tendsto (fun S : ℝ => ∫ u in Ici S, g u) atTop (𝓝 0) := by
    simp_rw [← integral_indicator measurableSet_Ici]
    rw [show (0 : ℝ) = ∫ _u : ℝ, (0 : ℝ) by simp]
    apply tendsto_integral_filter_of_dominated_convergence (fun u => ‖g u‖)
    · exact Eventually.of_forall (fun S => hg.aestronglyMeasurable.indicator measurableSet_Ici)
    · exact Eventually.of_forall (fun S => Eventually.of_forall (fun u => norm_indicator_le_norm_self _ _))
    · exact hg.norm
    · refine Eventually.of_forall (fun u => tendsto_const_nhds.congr' ?_)
      filter_upwards [eventually_gt_atTop u] with S hS
      rw [indicator_of_notMem (show u ∉ Ici S from not_le.mpr hS)]
  apply ht.congr'
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with S hS
  unfold polynomialForcingTail
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ici] with u hu
  exact indicator_of_mem (show u ∈ Ici (0 : ℝ) from hS.trans hu) _

theorem polynomialForcingTail_nonneg (σ S : ℝ) : 0 ≤ polynomialForcingTail σ S :=
  integral_nonneg (fun u => by positivity)

theorem eventually_polynomialForcingTail_lt {σ ε : ℝ} (hσ : 0 < σ) (hε : 0 < ε) :
    ∀ᶠ S : ℝ in atTop, polynomialForcingTail σ S < ε :=
  (tendsto_polynomialForcingTail hσ).eventually (gt_mem_nhds hε)

end Euler2D

end
