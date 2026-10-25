module

public import Mathlib

/-!
# The logarithmic Osgood comparison

The modulus `r (1-log r)` vanishes at zero but is not Lipschitz there.
Regularizing the distance by a positive epsilon and differentiating an
explicit barrier gives the zero-initial-distance uniqueness criterion.
This is a scalar estimate for the bounded-vorticity particle flow.
-/

@[expose] public section

noncomputable section

open Set Filter Topology Real

namespace Euler2D

def logFlowModulus (r : ℝ) : ℝ := r - r * Real.log r

lemma continuous_logFlowModulus : Continuous logFlowModulus :=
  continuous_id.sub Real.continuous_mul_log

lemma hasDerivAt_logFlowModulus {r : ℝ} (hr : r ≠ 0) :
    HasDerivAt logFlowModulus (-Real.log r) r := by
  convert (hasDerivAt_id r).sub (Real.hasDerivAt_mul_log hr) using 1 <;>
    (try funext x) <;>
    (try dsimp only [logFlowModulus, Pi.sub_def, id_eq]) <;> ring

lemma monotoneOn_logFlowModulus : MonotoneOn logFlowModulus (Icc 0 1) := by
  apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 1) continuous_logFlowModulus.continuousOn
  · intro r hr
    rw [interior_Icc] at hr
    exact (hasDerivAt_logFlowModulus hr.1.ne').hasDerivWithinAt
  · intro r hr
    rw [interior_Icc] at hr
    exact neg_nonneg.mpr (Real.log_nonpos hr.1.le hr.2.le)

/-- An epsilon barrier for the logarithmic distance inequality. -/
theorem logFlow_epsilon_bound {T C ε : ℝ} {f f' : ℝ → ℝ}
    (hT : 0 ≤ T) (hC : 0 ≤ C) (hε : 0 < ε) (hεhalf : ε ≤ 1 / 2)
    (hf : ∀ t ∈ Icc 0 T, HasDerivAt f (f' t) t)
    (hsmall : ∀ t ∈ Icc 0 T, f t ∈ Icc 0 (1 / 2))
    (hzero : f 0 = 0)
    (hbound : ∀ t ∈ Ioo 0 T, f' t ≤ C * logFlowModulus (f t)) :
    ∀ t ∈ Icc 0 T, f t ≤ Real.exp 1 * ε ^ Real.exp (-(C * t)) := by
  let B := fun t => (1 - Real.log (f t + ε)) * Real.exp (C * t)
  have hpos (t : ℝ) (ht : t ∈ Icc 0 T) : 0 < f t + ε := by
    linarith [(hsmall t ht).1]
  have hB (t : ℝ) (ht : t ∈ Icc 0 T) : HasDerivAt B
      (Real.exp (C * t) * (C * (1 - Real.log (f t + ε)) - f' t / (f t + ε))) t := by
    have he := ((hasDerivAt_id t).const_mul C).exp
    have hl := ((hf t ht).add_const ε).log (hpos t ht).ne'
    convert ((hasDerivAt_const t (1 : ℝ)).sub hl).mul he using 1 <;>
      (try funext s) <;>
      (try dsimp only [B, Pi.sub_def, Pi.mul_def, id_eq]) <;> ring
  have hBc : ContinuousOn B (Icc 0 T) := fun t ht => (hB t ht).continuousAt.continuousWithinAt
  have hmono : MonotoneOn B (Icc 0 T) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 T) hBc
    · intro t ht
      exact (hB t (interior_subset ht)).hasDerivWithinAt
    · intro t ht
      have hti : t ∈ Ioo 0 T := by simpa only [interior_Icc] using ht
      have htc : t ∈ Icc 0 T := ⟨hti.1.le, hti.2.le⟩
      have hmod : logFlowModulus (f t) ≤ logFlowModulus (f t + ε) :=
        monotoneOn_logFlowModulus ⟨(hsmall t htc).1, by linarith [(hsmall t htc).2]⟩
          ⟨(hpos t htc).le, by linarith [(hsmall t htc).2]⟩ (by linarith)
      have hd : f' t ≤ C * ((f t + ε) * (1 - Real.log (f t + ε))) := by
        have hb := (hbound t hti).trans (mul_le_mul_of_nonneg_left hmod hC)
        convert hb using 1
        simp only [logFlowModulus]
        ring
      have hdiv : f' t / (f t + ε) ≤ C * (1 - Real.log (f t + ε)) := by
        apply (div_le_iff₀ (hpos t htc)).mpr
        nlinarith [hd]
      exact mul_nonneg (Real.exp_pos _).le (sub_nonneg.mpr hdiv)
  intro t ht
  have hb := hmono ⟨le_rfl, hT⟩ ht ht.1
  change (1 - Real.log (f 0 + ε)) * Real.exp (C * 0) ≤
    (1 - Real.log (f t + ε)) * Real.exp (C * t) at hb
  simp only [hzero, zero_add, mul_zero, Real.exp_zero, mul_one] at hb
  have hb' := mul_le_mul_of_nonneg_right hb (Real.exp_pos (-(C * t))).le
  rw [mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one] at hb'
  have hl : Real.log (f t + ε) ≤ 1 + Real.log ε * Real.exp (-(C * t)) := by
    nlinarith [Real.exp_pos (-(C * t))]
  have he := Real.exp_le_exp.mpr hl
  rw [Real.exp_log (hpos t ht), Real.exp_add, ← Real.rpow_def_of_pos hε] at he
  exact (le_add_of_nonneg_right hε.le).trans he

/-- Osgood uniqueness for a scalar logarithmic distance inequality. -/
theorem eq_zero_of_logFlow_bound {T C : ℝ} {f f' : ℝ → ℝ}
    (hT : 0 ≤ T) (hC : 0 ≤ C)
    (hf : ∀ t ∈ Icc 0 T, HasDerivAt f (f' t) t)
    (hsmall : ∀ t ∈ Icc 0 T, f t ∈ Icc 0 (1 / 2))
    (hzero : f 0 = 0)
    (hbound : ∀ t ∈ Ioo 0 T, f' t ≤ C * logFlowModulus (f t)) :
    ∀ t ∈ Icc 0 T, f t = 0 := by
  intro t ht
  have hα : 0 < Real.exp (-(C * t)) := Real.exp_pos _
  have hlim : Tendsto (fun ε : ℝ => Real.exp 1 * ε ^ Real.exp (-(C * t)))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hc := (Real.continuousAt_rpow_const (0 : ℝ) _ (Or.inr hα.le)).tendsto
    have h := hc.const_mul (Real.exp 1)
    simpa only [Real.zero_rpow hα.ne', mul_zero] using h.mono_left nhdsWithin_le_nhds
  have hs : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ), ε < 1 / 2 :=
    (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 2)).filter_mono nhdsWithin_le_nhds
  have hle : f t ≤ 0 := ge_of_tendsto hlim (by
    filter_upwards [self_mem_nhdsWithin, hs] with ε hε he
    exact logFlow_epsilon_bound hT hC hε he.le hf hsmall hzero hbound t ht)
  exact le_antisymm hle (hsmall t ht).1

end Euler2D

end
