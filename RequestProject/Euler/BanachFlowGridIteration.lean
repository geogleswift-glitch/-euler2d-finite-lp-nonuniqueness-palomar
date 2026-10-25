module

public import RequestProject.Euler.BanachReferenceContinuation

/-! A genuinely existing longer autonomous flow agrees at every grid
time with iterates of the same shorter flow. The proof uses the original
open-domain ODE uniqueness on each translated interval. -/

@[expose] public section

set_option maxHeartbeats 2000000

noncomputable section

open Set Filter Topology Metric
open scoped ContDiff

namespace Euler2D

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem banachFlow_grid_eq_iterate {f : E → E} {D V W : Set E}
    (hD : IsOpen D) (hf : ContDiffOn ℝ 1 f D) {T : ℝ} (hT : 0 < T) (m : ℕ)
    {X Y : E → ℝ → E} (hX : IsBanachFlowOn f D V T X)
    (hY : IsBanachFlowOn f D W ((m : ℝ) * T) Y)
    {b : E} (hb : b ∈ W)
    (hgrid : ∀ j < m, (fun z => X z T)^[j] b ∈ V) :
    ∀ n ≤ m, Y b ((n : ℝ) * T) = (fun z => X z T)^[n] b := by
  intro n
  induction n with
  | zero => intro _; simpa only [Nat.cast_zero, zero_mul, Function.iterate_zero_apply] using hY.initial b hb
  | succ n ih =>
    intro hn
    have hnm : n < m := Nat.lt_of_succ_le hn
    have he₀ := ih hnm.le
    let a := (fun z => X z T)^[n] b
    have ha : a ∈ V := hgrid n hnm
    have htime (s : ℝ) (hs : s ∈ Icc (0 : ℝ) T) :
        (n : ℝ) * T + s ∈ Icc (0 : ℝ) ((m : ℝ) * T) := by
      have hncast : (n : ℝ) + 1 ≤ m := by exact_mod_cast hn
      have hh := mul_le_mul_of_nonneg_right hncast hT.le
      constructor
      · exact add_nonneg (mul_nonneg (Nat.cast_nonneg n) hT.le) hs.1
      · nlinarith only [hh, hs.2]
    have heq : EqOn (fun s => Y b ((n : ℝ) * T + s)) (X a) (Icc (0 : ℝ) T) := by
      apply eqOn_of_banachODE_open hD hf
      · exact (hY.continuous b hb).comp
          (continuousOn_const.add continuousOn_id) (fun s hs => htime s hs)
      · exact hX.continuous a ha
      · intro s hs
        exact hY.mem b hb _ (htime s hs)
      · exact hX.mem a ha
      · intro s hs
        exact HasDerivAt.comp_const_add ((n : ℝ) * T) s
          (hY.hasDerivAt b hb _ (htime s ⟨hs.1, hs.2.le⟩))
      · intro s hs
        exact hX.hasDerivAt a ha s ⟨hs.1, hs.2.le⟩
      · rw [add_zero, hX.initial a ha]
        exact he₀
    have he := heq ⟨hT.le, le_rfl⟩
    simpa only [Nat.cast_succ, add_mul, one_mul, Function.iterate_succ_apply'] using he

theorem eventually_fixedPoint_iterates_mem_ball {F : E → E} {x : E}
    (hF : ContinuousAt F x) (hfix : F x = x) {r : ℝ} (hr : 0 < r) (m : ℕ) :
    ∀ᶠ b : E in 𝓝 x, ∀ j ≤ m, F^[j] b ∈ ball x r := by
  have he (j : ℕ) : F^[j] x = x := by
    induction j with
    | zero => rfl
    | succ j ih => rw [Function.iterate_succ_apply', ih, hfix]
  have hc (j : ℕ) : ContinuousAt F^[j] x := by
    induction j with
    | zero => exact continuousAt_id
    | succ j ih =>
      have ho : ContinuousAt F (F^[j] x) := by rw [he]; exact hF
      simpa only [Function.iterate_succ', Function.comp_def] using ho.comp ih
  have hfinite : ∀ j : Fin (m + 1), ∀ᶠ b : E in 𝓝 x, F^[j.val] b ∈ ball x r := by
    intro j
    apply (hc j.val).eventually
    rw [he]
    exact ball_mem_nhds x hr
  filter_upwards [Filter.eventually_all.mpr hfinite] with b hb
  intro j hj
  exact hb ⟨j, Nat.lt_succ_of_le hj⟩

end Euler2D

end
