module

public import RequestProject.Euler.LogFlowUniqueness

/-!
# Uniqueness on an entire finite interval for logarithmic particle flows

Continuous induction extends the local Osgood comparison. No global
closeness of the two trajectories is assumed.
-/

@[expose] public section

noncomputable section

open Set Filter Topology Real Metric

namespace Euler2D

theorem logFlow_unique {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {T C : ℝ} (hC : 0 ≤ C) {v : ℝ → E → E} {X Y : ℝ → E}
    (hXc : Continuous X) (hYc : Continuous Y)
    (hX : ∀ t ∈ Icc 0 T, HasDerivAt X (v t (X t)) t)
    (hY : ∀ t ∈ Icc 0 T, HasDerivAt Y (v t (Y t)) t)
    (hinit : X 0 = Y 0)
    (hlip : ∀ t ∈ Icc 0 T, ∀ x y : E, ‖x - y‖ ≤ 1 / 2 →
      ‖v t x - v t y‖ ≤ C * logFlowModulus ‖x - y‖) :
    ∀ t ∈ Icc 0 T, X t = Y t := by
  intro t ht
  have hclosed : IsClosed ({s : ℝ | X s = Y s} ∩ Icc 0 t) :=
    (isClosed_eq hXc hYc).inter isClosed_Icc
  apply hclosed.mem_of_ge_of_forall_exists_gt hinit ht.1
  intro a ha
  have ha0 : 0 ≤ a := ha.2.1
  have hat : a < t := ha.2.2
  have hXa : X a = Y a := ha.1
  have hnear : ∀ᶠ s in 𝓝 a, ‖X s - Y s‖ < 1 / 2 := by
    have hc := ((hXc.sub hYc).norm).continuousAt (x := a)
    have hval : ‖X a - Y a‖ < (1 / 2 : ℝ) := by simp [hXa]
    exact hc.eventually (Iio_mem_nhds hval)
  obtain ⟨ε, hε, hεbound⟩ := Metric.eventually_nhds_iff.mp hnear
  let b := min t (a + ε / 2)
  have hab : a < b := lt_min hat (by linarith)
  have hbt : b ≤ t := min_le_left _ _
  have hba : b ≤ a + ε / 2 := min_le_right _ _
  have hsub (r : ℝ) (hr : r ∈ Icc 0 (b - a)) : r + a ∈ Icc 0 T := by
    exact ⟨by linarith [hr.1], by linarith [hr.2, ht.2]⟩
  have hXshift (r : ℝ) (hr : r ∈ Icc 0 (b - a)) :
      HasDerivAt (fun s => X (s + a)) (v (r + a) (X (r + a))) r := by
    simpa only [Function.comp_def, id_eq, one_smul] using
      (hX (r + a) (hsub r hr)).scomp r ((hasDerivAt_id r).add_const a)
  have hYshift (r : ℝ) (hr : r ∈ Icc 0 (b - a)) :
      HasDerivAt (fun s => Y (s + a)) (v (r + a) (Y (r + a))) r := by
    simpa only [Function.comp_def, id_eq, one_smul] using
      (hY (r + a) (hsub r hr)).scomp r ((hasDerivAt_id r).add_const a)
  have hclose (r : ℝ) (hr : r ∈ Icc 0 (b - a)) : ‖X (r + a) - Y (r + a)‖ ≤ 1 / 2 := by
    apply le_of_lt (hεbound (y := r + a) ?_)
    rw [Real.dist_eq, add_sub_cancel_right, abs_of_nonneg hr.1]
    linarith [hr.2]
  have hlocal := logFlow_unique_of_nearby (sub_nonneg.mpr hab.le) hC
    (v := fun r x => v (r + a) x) hXshift hYshift
    (by simpa only [zero_add] using hXa) hclose
    (fun r hr x y hxy => hlip (r + a) (hsub r hr) x y hxy)
  have hEq : X b = Y b := by
    simpa only [sub_add_cancel] using hlocal (b - a) ⟨sub_nonneg.mpr hab.le, le_rfl⟩
  exact ⟨b, hEq, hab, hbt⟩

end Euler2D

end
