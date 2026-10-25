module

public import RequestProject.Euler.Delay

/-!
# Strong closure of stationary data

The quadratic pairing in the stationary Euler equation is continuous in the
strong `L²` topology. Consequently stationarity, and the mean-zero condition,
pass to strong limits of data.
-/

@[expose] public section

open MeasureTheory Real Filter Topology Set
open scoped ContDiff

namespace Euler2D

/-- A fixed bounded continuous coefficient defines a continuous bilinear pairing
on two copies of `L²` (stated for arbitrary convergent filters). -/
lemma tendsto_fixed_bilin {α : Type*} {l : Filter α} {v w : α → L2T} {v₀ w₀ : L2T}
    (hv : Tendsto v l (𝓝 v₀)) (hw : Tendsto w l (𝓝 w₀))
    {k : R2 → ℝ} (hk : Continuous k) (i j : Fin 2) :
    Tendsto (fun a => ∫ x in torusBox, v a x i * w a x j * k x) l
      (𝓝 (∫ x in torusBox, v₀ x i * w₀ x j * k x)) := by
  obtain ⟨C, hC⟩ := bound_on_box hk
  have hI : ∀ f g : L2T,
      Integrable (fun x => f x i * g x j * k x) μT :=
    fun f g => integrable_bilin f g i j hk.aestronglyMeasurable hC
  have hdecomp (a : α) :
      (∫ x in torusBox, v a x i * w a x j * k x) -
        (∫ x in torusBox, v₀ x i * w₀ x j * k x) =
      (∫ x in torusBox, (v a - v₀) x i * w a x j * k x) +
        (∫ x in torusBox, v₀ x i * (w a - w₀) x j * k x) := by
    rw [← integral_sub (hI (v a) (w a)) (hI v₀ w₀),
      ← integral_add (hI (v a - v₀) (w a)) (hI v₀ (w a - w₀))]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub (v a) v₀, Lp.coeFn_sub (w a) w₀] with x hx hy
    rw [hx, hy]
    simp only [Pi.sub_apply, PiLp.sub_apply]
    ring
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hbound (a : α) :
      ‖(∫ x in torusBox, v a x i * w a x j * k x) -
        (∫ x in torusBox, v₀ x i * w₀ x j * k x)‖ ≤
      C * (‖v a - v₀‖ * ‖w a‖) + C * (‖v₀‖ * ‖w a - w₀‖) := by
    rw [hdecomp, Real.norm_eq_abs]
    exact (abs_add_le _ _).trans
      (add_le_add (abs_integral_bilin_le (v a - v₀) (w a) i j hC)
        (abs_integral_bilin_le v₀ (w a - w₀) i j hC))
  have hzero : Tendsto
      (fun a => C * (‖v a - v₀‖ * ‖w a‖) + C * (‖v₀‖ * ‖w a - w₀‖)) l (𝓝 0) := by
    convert (tendsto_const_nhds.mul
      (((hv.sub tendsto_const_nhds).norm).mul hw.norm)).add
      (tendsto_const_nhds.mul
        (tendsto_const_nhds.mul ((hw.sub tendsto_const_nhds).norm))) using 1
    simp
  exact squeeze_zero (fun _ => norm_nonneg _) hbound hzero

/-- The stationary quadratic pairing with a fixed smooth field is continuous. -/
lemma continuous_stationary_pairing {ψ : R2 → R2} (hψ : ContDiff ℝ ∞ ψ) :
    Continuous (fun v : L2T =>
      ∫ x in torusBox, ∑ i, ∑ j, v x i * v x j * pd j ψ x i) := by
  have hk (i j : Fin 2) : Continuous (fun x => pd j ψ x i) := by
    exact (EuclideanSpace.proj i : R2 →L[ℝ] ℝ).continuous.comp
      ((hψ.continuous_fderiv (by simp)).clm_apply continuous_const)
  have heq (v : L2T) :
      (∫ x in torusBox, ∑ i, ∑ j, v x i * v x j * pd j ψ x i) =
        ∑ i, ∑ j, ∫ x in torusBox, v x i * v x j * pd j ψ x i := by
    have hI (i j : Fin 2) :
        Integrable (fun x => v x i * v x j * pd j ψ x i) μT := by
      obtain ⟨C, hC⟩ := bound_on_box (hk i j)
      exact integrable_bilin v v i j (hk i j).aestronglyMeasurable hC
    rw [integral_finset_sum _ (fun i _ => integrable_finset_sum _ (fun j _ => hI i j))]
    exact Finset.sum_congr rfl fun i _ => integral_finset_sum _ (fun j _ => hI i j)
  simp_rw [heq]
  exact continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun j _ =>
    continuous_iff_continuousAt.mpr fun v =>
      tendsto_fixed_bilin tendsto_id tendsto_id (hk i j) i j

/-- Strong limits of stationary data are stationary. -/
lemma IsStationary.of_tendsto {α : Type*} {l : Filter α} [NeBot l]
    {v : α → L2T} {u₀ : L2T} (hstat : ∀ᶠ a in l, IsStationary (v a))
    (hv : Tendsto v l (𝓝 u₀)) : IsStationary u₀ := by
  intro ψ hψ hper hdiv
  have hlim := (continuous_stationary_pairing hψ).tendsto u₀ |>.comp hv
  have hz : Tendsto (fun a =>
      ∫ x in torusBox, ∑ i, ∑ j, v a x i * v a x j * pd j ψ x i) l (𝓝 0) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [hstat] with a ha
    exact (ha ψ hψ hper hdiv).symm
  exact tendsto_nhds_unique hlim hz

/-- Stationary data form a strongly closed subset of `L²`. -/
lemma isClosed_setOf_isStationary : IsClosed {u₀ : L2T | IsStationary u₀} := by
  simp only [IsStationary, setOf_forall]
  refine isClosed_iInter fun ψ => isClosed_iInter fun hψ =>
    isClosed_iInter fun _ => isClosed_iInter fun _ => ?_
  exact isClosed_eq (continuous_stationary_pairing hψ) continuous_const

/-- Fixed linear test pairings pass to strong `L²` limits. -/
lemma tendsto_fixed_lin {α : Type*} {l : Filter α} {v : α → L2T} {v₀ : L2T}
    (hv : Tendsto v l (𝓝 v₀)) {k : R2 → ℝ} (hk : Continuous k) (i : Fin 2) :
    Tendsto (fun a => ∫ x in torusBox, v a x i * k x) l
      (𝓝 (∫ x in torusBox, v₀ x i * k x)) := by
  have heq (f : L2T) :
      (∫ x in torusBox, f x i * constE0 x 0 * k x) =
        ∫ x in torusBox, f x i * k x := by
    apply integral_congr_ae
    filter_upwards [constE0_ae] with x hx
    rw [hx, mul_one]
  simpa only [heq] using
    tendsto_fixed_bilin hv (tendsto_const_nhds (x := constE0)) hk i 0

/-- The mean-zero condition on torus data passes to strong `L²` limits. -/
lemma mean_zero_of_tendsto {α : Type*} {l : Filter α} [NeBot l]
    {v : α → L2T} {v₀ : L2T} (hmean : ∀ᶠ a in l, ∫ x in torusBox, v a x = 0)
    (hv : Tendsto v l (𝓝 v₀)) : ∫ x in torusBox, v₀ x = 0 := by
  have hcoord (f : L2T) (i : Fin 2) :
      (∫ x in torusBox, f x) i = ∫ x in torusBox, f x i := by
    exact ((EuclideanSpace.proj i : R2 →L[ℝ] ℝ).integral_comp_comm
      ((Lp.memLp f).integrable (by norm_num))).symm
  ext i
  rw [hcoord]
  have hlim : Tendsto (fun a => ∫ x in torusBox, v a x i) l
      (𝓝 (∫ x in torusBox, v₀ x i)) := by
    simpa only [mul_one] using tendsto_fixed_lin hv (continuous_const (y := (1 : ℝ))) i
  have hz : Tendsto (fun a => ∫ x in torusBox, v a x i) l (𝓝 0) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [hmean] with a ha
    rw [← hcoord, ha]
    rfl
  exact tendsto_nhds_unique hlim hz

end Euler2D

end
