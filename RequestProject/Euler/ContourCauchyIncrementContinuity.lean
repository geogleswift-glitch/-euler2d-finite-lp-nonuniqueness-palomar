module

public import RequestProject.Euler.ContourCauchyIncrement

/-! Joint continuity of the actual absolutely convergent Cauchy increment
under genuine common chord and Hölder bounds. This continuity will allow
smooth approximations to pass to the actual derivative formula. -/

@[expose] public section

noncomputable section

open Complex Set Filter Topology MeasureTheory

namespace Euler2D

variable {A : Type*} [TopologicalSpace A] [FirstCountableTopology A]

theorem continuous_contourCauchyIncrement_of_bounds
    (z dz f : A → ℝ → ℂ) {γ c L H : ℝ}
    (hz : Continuous (Function.uncurry z)) (hdz : Continuous (Function.uncurry dz))
    (hf : Continuous (Function.uncurry f)) (hγ : 0 < γ) (hc : 0 < c)
    (hL : 0 ≤ L) (hH : 0 ≤ H)
    (hD : ∀ a θ, ‖dz a θ‖ ≤ L)
    (hchord : ∀ a θ τ, |τ| ≤ Real.pi → c * |τ| ≤ ‖z a θ - z a (θ + τ)‖)
    (hholder : ∀ a θ τ, ‖f a (θ + τ) - f a θ‖ ≤ H * |τ| ^ γ) :
    Continuous (fun q : A × ℝ => ∫ τ in Icc (-Real.pi) Real.pi,
      contourCauchyIncrementIntegrand (z q.1) (dz q.1) (f q.1) q.2 τ) := by
  have hmeas (q : A × ℝ) : AEStronglyMeasurable
      (contourCauchyIncrementIntegrand (z q.1) (dz q.1) (f q.1) q.2)
      (volume.restrict (Icc (-Real.pi) Real.pi)) := by
    have hzτ : Continuous (fun τ : ℝ => z q.1 (q.2 + τ)) :=
      hz.comp (continuous_const.prodMk (continuous_const.add continuous_id))
    have hdτ : Continuous (fun τ : ℝ => dz q.1 (q.2 + τ)) :=
      hdz.comp (continuous_const.prodMk (continuous_const.add continuous_id))
    have hfτ : Continuous (fun τ : ℝ => f q.1 (q.2 + τ)) :=
      hf.comp (continuous_const.prodMk (continuous_const.add continuous_id))
    exact ((hdτ.measurable.div (measurable_const.sub hzτ.measurable)).mul
      (hfτ.measurable.sub measurable_const)).aestronglyMeasurable
  apply continuous_of_dominated (bound := fun τ => (L * H / c) * |τ| ^ (γ - 1)) hmeas
  · intro q
    filter_upwards [ae_restrict_mem measurableSet_Icc] with τ hτ
    exact norm_contourCauchyIncrementIntegrand_le hc hL hH
      (hchord q.1 q.2 τ (abs_le.mpr hτ)) (hD q.1 (q.2 + τ)) (hholder q.1 q.2 τ)
  · exact (integrableOn_abs_rpow_sub_one hγ Real.pi_pos.le).const_mul _
  · filter_upwards [ae_restrict_mem measurableSet_Icc,
      ae_restrict_of_ae (volume.ae_ne (0 : ℝ))] with τ hτ hτ0
    have hzshift : Continuous (fun q : A × ℝ => z q.1 (q.2 + τ)) :=
      hz.comp (continuous_fst.prodMk (continuous_snd.add continuous_const))
    have hdshift : Continuous (fun q : A × ℝ => dz q.1 (q.2 + τ)) :=
      hdz.comp (continuous_fst.prodMk (continuous_snd.add continuous_const))
    have hfshift : Continuous (fun q : A × ℝ => f q.1 (q.2 + τ)) :=
      hf.comp (continuous_fst.prodMk (continuous_snd.add continuous_const))
    have hn (q : A × ℝ) : z q.1 q.2 - z q.1 (q.2 + τ) ≠ 0 :=
      norm_pos_iff.mp ((mul_pos hc (abs_pos.mpr hτ0)).trans_le
        (hchord q.1 q.2 τ (abs_le.mpr hτ)))
    exact (hdshift.div (hz.sub hzshift) hn).mul (hfshift.sub hf)

end Euler2D

end
