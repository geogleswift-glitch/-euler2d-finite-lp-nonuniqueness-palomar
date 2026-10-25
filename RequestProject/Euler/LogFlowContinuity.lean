module

public import RequestProject.Euler.LogFlowCompactness

/-! Joint continuity follows from the actual ODE and its logarithmic
modulus; it is not an assumption on a selected particle family. -/

@[expose] public section

noncomputable section

open Set Filter Topology Real Metric

namespace Euler2D

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem uniformContinuous_logParticleFamily {T C M : ℝ}
    (hT : 0 ≤ T) (hC : 0 ≤ C) (hM0 : 0 ≤ M)
    (v X : ℝ → E → E) (hXc : ∀ a, Continuous (fun t => X t a))
    (hX : ∀ t ∈ Icc (0 : ℝ) T, ∀ a, HasDerivAt (fun s => X s a) (v t (X t a)) t)
    (hinit : ∀ a, X 0 a = a)
    (hM : ∀ t ∈ Icc (0 : ℝ) T, ∀ x, ‖v t x‖ ≤ M)
    (hlip : ∀ t ∈ Icc (0 : ℝ) T, ∀ x y, ‖x - y‖ ≤ 1 / 2 →
      ‖v t x - v t y‖ ≤ C * logFlowModulus ‖x - y‖) :
    UniformContinuous (fun p : Icc (0 : ℝ) T × E => X p.1 p.2) := by
  apply Metric.uniformContinuous_iff.mpr
  intro ε hε
  obtain ⟨d, hd, hspace⟩ := logFlow_uniform_stability (E := E) hT hC
    (div_pos hε (by norm_num : (0 : ℝ) < 2))
  let r := ε / (2 * (M + 1))
  have hr : 0 < r := by dsimp only [r]; positivity
  refine ⟨min d r, lt_min hd hr, fun p q hpq => ?_⟩
  have ha : ‖p.2 - q.2‖ < d := by
    have hb : dist p.2 q.2 ≤ dist p q := by rw [Prod.dist_eq]; exact le_max_right _ _
    have hb' : ‖p.2 - q.2‖ ≤ dist p q := by simpa only [dist_eq_norm] using hb
    exact hb'.trans_lt (hpq.trans_le (min_le_left _ _))
  have ht : |(p.1 : ℝ) - q.1| < r := by
    have hb : dist p.1 q.1 ≤ dist p q := by rw [Prod.dist_eq]; exact le_max_left _ _
    have hb' : |(p.1 : ℝ) - q.1| ≤ dist p q := by
      simpa only [Subtype.dist_eq, Real.dist_eq] using hb
    exact hb'.trans_lt (hpq.trans_le (min_le_right _ _))
  have hs : ‖X p.1 p.2 - X p.1 q.2‖ < ε / 2 :=
    hspace v (fun t => X t p.2) (fun t => X t q.2) (hXc _) (hXc _)
      (fun t ht => hX t ht _) (fun t ht => hX t ht _) hlip
      (by simpa only [hinit] using ha.le) p.1 p.1.property
  have htime := norm_trajectory_sub_time_le (fun t ht => hX t ht q.2) hM
    q.1.property p.1.property
  have ht' : ‖X p.1 q.2 - X q.1 q.2‖ < ε / 2 := by
    have hpos : 0 < M + 1 := by linarith
    have hb := mul_lt_mul_of_pos_left ht hpos
    have he : (M + 1) * r = ε / 2 := by dsimp only [r]; field_simp
    rw [he] at hb
    exact (htime.trans (mul_le_mul_of_nonneg_right (by linarith : M ≤ M + 1)
      (abs_nonneg _))).trans_lt hb
  rw [dist_eq_norm]
  exact (norm_sub_le_norm_sub_add_norm_sub _ (X p.1 q.2) _).trans_lt
    ((add_lt_add hs ht').trans_eq (by ring))

theorem logParticleCurve_unique {T C : ℝ}
    (hT : 0 ≤ T) (hC : 0 ≤ C) {v : ℝ → E → E} {X Y : ℝ → E}
    (hXc : Continuous X) (hYc : Continuous Y)
    (hX : ∀ t ∈ Icc (0 : ℝ) T, HasDerivAt X (v t (X t)) t)
    (hY : ∀ t ∈ Icc (0 : ℝ) T, HasDerivAt Y (v t (Y t)) t)
    (hlip : ∀ t ∈ Icc (0 : ℝ) T, ∀ x y, ‖x - y‖ ≤ 1 / 2 →
      ‖v t x - v t y‖ ≤ C * logFlowModulus ‖x - y‖)
    (hinit : X 0 = Y 0) : Set.EqOn X Y (Icc (0 : ℝ) T) := by
  intro t ht
  apply sub_eq_zero.mp
  apply norm_eq_zero.mp
  apply le_antisymm ?_ (norm_nonneg _)
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨δ, hδ, hstable⟩ := logFlow_uniform_stability (E := E) hT hC hε
  have hs := hstable v X Y hXc hYc hX hY hlip
    (by simpa only [hinit, sub_self, norm_zero] using hδ.le) t ht
  simpa only [zero_add] using hs.le

end Euler2D

end
