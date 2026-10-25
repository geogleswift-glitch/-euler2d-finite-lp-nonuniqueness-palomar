module

public import RequestProject.Euler.TorusTransport
public import RequestProject.Euler.RadialStationary

/-!
# Pointwise uniqueness of continuous periodic representatives

Almost-everywhere equality on the physical fundamental square determines
continuous periodic fields everywhere on the covering plane.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Metric

namespace Euler2D

lemma convex_torusBox : Convex ℝ torusBox := by
  intro x hx y hy a b ha hb hab i
  simpa only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul] using
    (convex_Ico (𝕜 := ℝ) (0 : ℝ) (2 * Real.pi)) (hx i) (hy i) ha hb hab

lemma torusCenter_mem_interior_torusBox : torusCenter ∈ interior torusBox := by
  have hball : ball torusCenter 1 ⊆ torusBox := by
    intro x hx i
    have hn : ‖x - torusCenter‖ < 1 := by simpa only [mem_ball, dist_eq_norm] using hx
    have hc : |x i - Real.pi| < 1 := by
      simpa only [PiLp.sub_apply, torusCenter_apply] using (abs_coord_le _ i).trans_lt hn
    have hcc := abs_lt.mp hc
    constructor <;> linarith [Real.pi_gt_three]
  apply mem_interior_iff_mem_nhds.mpr
  exact Filter.mem_of_superset (ball_mem_nhds torusCenter (by norm_num : (0 : ℝ) < 1)) hball

lemma torusBox_subset_closure_interior : torusBox ⊆ closure (interior torusBox) := by
  rw [convex_torusBox.closure_interior_eq_closure_of_nonempty_interior
    ⟨torusCenter, torusCenter_mem_interior_torusBox⟩]
  exact subset_closure

/-- Continuous periodic representatives of the same physical torus class
coincide globally. The codomain only needs a Hausdorff topology. -/
theorem _root_.Continuous.eq_of_periodic_ae_eq {F : Type*} [TopologicalSpace F] [T2Space F]
    {f g : R2 → F} (hf : Continuous f) (hg : Continuous g)
    (hfp : IsTorusPeriodic f) (hgp : IsTorusPeriodic g) (hfg : f =ᵐ[μT] g) : f = g := by
  have heq : EqOn f g torusBox := Measure.eqOn_of_ae_eq (μ := volume) hfg
    hf.continuousOn hg.continuousOn torusBox_subset_closure_interior
  funext x
  calc
    f x = f (torusWrap x) := (hfp.eq_torusWrap x).symm
    _ = g (torusWrap x) := heq (torusRep_mem (torusProj x))
    _ = g x := hgp.eq_torusWrap x

end Euler2D

end
