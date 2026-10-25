module

public import RequestProject.Euler.VelocityCurlBound
public import RequestProject.Euler.DatumCurlSeries

/-!
# Stability of the actual velocity from its curl

The mean-zero inverse curl is Lipschitz in the physical torus L² norms.
This identifies a velocity limit directly from vorticity convergence,
without a separate assumption on convergence of the velocities.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ContDiff

namespace Euler2D

lemma DivFree.sub_L2 {u v : L2T} (hu : DivFree u) (hv : DivFree v) :
    DivFree (u - v : L2T) := by
  intro ψ hψ
  have hpd (i : Fin 2) : Continuous (pd i ψ) :=
    (hψ.1.continuous_fderiv (by simp)).clm_apply continuous_const
  have hint (a : L2T) : Integrable (fun x => ∑ i, a x i * pd i ψ x) μT := by
    apply integrable_finset_sum
    intro i _
    obtain ⟨C, hC⟩ := bound_on_box (hpd i)
    exact integrable_lin a i (hpd i).aestronglyMeasurable hC
  calc
    _ = ∫ x in torusBox, (∑ i, u x i * pd i ψ x) - ∑ i, v x i * pd i ψ x := by
      apply integral_congr_ae
      filter_upwards [Lp.coeFn_sub u v] with x hx
      simp only [hx, Pi.sub_apply, PiLp.sub_apply, sub_mul, Finset.sum_sub_distrib]
    _ = 0 := by rw [integral_sub (hint u) (hint v), hu ψ hψ, hv ψ hψ, sub_self]

lemma IsCurl.sub_L2 {u v : L2T} {w z : Lp ℝ 2 μT}
    (hu : IsCurl u w) (hv : IsCurl v z) :
    IsCurl (u - v : L2T) (w - z : Lp ℝ 2 μT) := by
  intro ψ hψ
  have hψmem := continuous_memLp_torus hψ.1.continuous 2
  have hpd (i : Fin 2) : Continuous (pd i ψ) :=
    (hψ.1.continuous_fderiv (by simp)).clm_apply continuous_const
  have hint (a : L2T) (i j : Fin 2) : Integrable (fun x => a x i * pd j ψ x) μT := by
    obtain ⟨C, hC⟩ := bound_on_box (hpd j)
    exact integrable_lin a i (hpd j).aestronglyMeasurable hC
  have hleft : (∫ x in torusBox, (w - z) x * ψ x) =
      (∫ x in torusBox, w x * ψ x) - ∫ x in torusBox, z x * ψ x := by
    calc
      _ = ∫ x in torusBox, w x * ψ x - z x * ψ x := by
        apply integral_congr_ae
        filter_upwards [Lp.coeFn_sub w z] with x hx
        simp only [hx, Pi.sub_apply, sub_mul]
      _ = _ := integral_sub ((Lp.memLp w).integrable_mul hψmem)
        ((Lp.memLp z).integrable_mul hψmem)
  have hright : (∫ x in torusBox,
      (u - v) x 0 * pd 1 ψ x - (u - v) x 1 * pd 0 ψ x) =
      (∫ x in torusBox, u x 0 * pd 1 ψ x - u x 1 * pd 0 ψ x) -
        ∫ x in torusBox, v x 0 * pd 1 ψ x - v x 1 * pd 0 ψ x := by
    calc
      _ = ∫ x in torusBox, (u x 0 * pd 1 ψ x - u x 1 * pd 0 ψ x) -
          (v x 0 * pd 1 ψ x - v x 1 * pd 0 ψ x) := by
        apply integral_congr_ae
        filter_upwards [Lp.coeFn_sub u v] with x hx
        simp only [hx, Pi.sub_apply, PiLp.sub_apply]
        ring
      _ = _ := integral_sub ((hint u 0 1).sub (hint u 1 0))
        ((hint v 0 1).sub (hint v 1 0))
  rw [hleft, hu ψ hψ, hv ψ hψ, hright]

lemma integral_sub_L2 (u v : L2T) :
    (∫ x in torusBox, (u - v) x) = (∫ x in torusBox, u x) - ∫ x in torusBox, v x := by
  calc
    _ = ∫ x in torusBox, u x - v x := integral_congr_ae (Lp.coeFn_sub u v)
    _ = _ := integral_sub ((Lp.memLp u).integrable (by norm_num))
      ((Lp.memLp v).integrable (by norm_num))

/-- Equal means and nearby actual L² curls force nearby velocities. -/
theorem norm_velocity_sub_le_of_curl_sub {u v : L2T} {w z : Lp ℝ 2 μT}
    (hu : DivFree u) (hv : DivFree v) (hc : IsCurl u w) (hd : IsCurl v z)
    (hmean : (∫ x in torusBox, u x) = ∫ x in torusBox, v x) :
    ‖u - v‖ ≤ 2 * ‖w - z‖ := by
  have hm : (∫ x in torusBox, (u - v) x) = ∫ x in torusBox, (0 : L2T) x := by
    rw [integral_sub_L2, hmean, sub_self]
    symm
    calc
      _ = ∫ _ in torusBox, (0 : R2) := integral_congr_ae (Lp.coeFn_zero R2 2 μT)
      _ = 0 := by simp
  have h := norm_velocity_le_of_curl_and_mean (u - v) 0 (hu.sub_L2 hv)
    (w - z : Lp ℝ 2 μT) (Lp.memLp _) (hc.sub_L2 hd) hm
  simpa only [norm_zero, add_zero, Lp.norm_def] using h

/-- In particular the mean-zero velocity with a specified L² curl is unique. -/
theorem velocity_eq_of_curl_eq {u v : L2T} {w : Lp ℝ 2 μT}
    (hu : DivFree u) (hv : DivFree v) (hc : IsCurl u w) (hd : IsCurl v w)
    (hmean : (∫ x in torusBox, u x) = ∫ x in torusBox, v x) : u = v := by
  have h := norm_velocity_sub_le_of_curl_sub hu hv hc hd hmean
  rw [sub_self, norm_zero, mul_zero] at h
  exact sub_eq_zero.mp (norm_le_zero_iff.mp h)

/-- Strong L² vorticity convergence gives strong velocity convergence,
provided the divergence and spatial means agree. -/
theorem tendsto_velocity_of_curl {ι : Type*} {l : Filter ι}
    {u : ι → L2T} {v : L2T} {w : ι → Lp ℝ 2 μT} {z : Lp ℝ 2 μT}
    (hu : ∀ i, DivFree (u i)) (hv : DivFree v)
    (hc : ∀ i, IsCurl (u i) (w i)) (hd : IsCurl v z)
    (hmean : ∀ i, (∫ x in torusBox, u i x) = ∫ x in torusBox, v x)
    (hw : Tendsto w l (𝓝 z)) : Tendsto u l (𝓝 v) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hn := tendsto_iff_norm_sub_tendsto_zero.mp hw
  have hlim : Tendsto (fun i => 2 * ‖w i - z‖) l (𝓝 0) := by
    simpa only [mul_zero] using hn.const_mul 2
  exact squeeze_zero (fun i => norm_nonneg _) (fun i =>
    norm_velocity_sub_le_of_curl_sub (hu i) hv (hc i) hd (hmean i)) hlim

end Euler2D

end
