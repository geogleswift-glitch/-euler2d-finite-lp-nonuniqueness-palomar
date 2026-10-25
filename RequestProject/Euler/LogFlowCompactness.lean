module

public import RequestProject.Euler.LogFlowStability
public import RequestProject.Euler.CompactTestTopology

/-!
# Compactness of actual particle trajectories with a common logarithmic modulus

The spatial equicontinuity comes from the proved Osgood stability.
The time equicontinuity and range bound come from the actual particle ODE.
-/

@[expose] public section

noncomputable section

open Set Filter Topology Real Metric
open scoped UniformConvergence

namespace Euler2D

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma norm_trajectory_sub_time_le {T M : ℝ} {v : ℝ → E → E} {X : ℝ → E}
    (hX : ∀ t ∈ Icc 0 T, HasDerivAt X (v t (X t)) t)
    (hM : ∀ t ∈ Icc 0 T, ∀ x, ‖v t x‖ ≤ M)
    {s t : ℝ} (hs : s ∈ Icc 0 T) (ht : t ∈ Icc 0 T) :
    ‖X t - X s‖ ≤ M * |t - s| := by
  have haux {a b : ℝ} (ha : a ∈ Icc 0 T) (hb : b ∈ Icc 0 T) (hab : a ≤ b) :
      ‖X b - X a‖ ≤ M * (b - a) := by
    apply norm_image_sub_le_of_norm_deriv_le_segment'
      (fun r hr => (hX r ⟨ha.1.trans hr.1, hr.2.trans hb.2⟩).hasDerivWithinAt)
      (fun r hr => hM r ⟨ha.1.trans hr.1, hr.2.le.trans hb.2⟩ _) b ⟨hab, le_rfl⟩
  rcases le_total s t with hst | hts
  · simpa only [abs_of_nonneg (sub_nonneg.mpr hst)] using haux hs ht hst
  · rw [norm_sub_rev, abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hts)]
    exact haux ht hs hts

theorem uniformEquicontinuous_logFlow_family {ι : Type*} {T C M : ℝ}
    (hT : 0 ≤ T) (hC : 0 ≤ C) (hM0 : 0 ≤ M)
    (v X : ι → ℝ → E → E)
    (hXc : ∀ n, Continuous (Function.uncurry (X n)))
    (hX : ∀ n t, t ∈ Icc 0 T → ∀ a,
      HasDerivAt (fun s => X n s a) (v n t (X n t a)) t)
    (hinit : ∀ n a, X n 0 a = a)
    (hM : ∀ n t, t ∈ Icc 0 T → ∀ x, ‖v n t x‖ ≤ M)
    (hlip : ∀ n t, t ∈ Icc 0 T → ∀ x y, ‖x - y‖ ≤ 1 / 2 →
      ‖v n t x - v n t y‖ ≤ C * logFlowModulus ‖x - y‖) :
    UniformEquicontinuous (fun n (p : Icc (0 : ℝ) T × E) => X n p.1 p.2) := by
  apply Metric.uniformEquicontinuous_iff.mpr
  intro ε hε
  obtain ⟨d, hd, hspace⟩ := logFlow_uniform_stability (E := E) hT hC
    (div_pos hε (by norm_num : (0 : ℝ) < 2))
  let r := ε / (2 * (M + 1))
  have hr : 0 < r := by dsimp only [r]; positivity
  refine ⟨min d r, lt_min hd hr, fun p q hpq n => ?_⟩
  have ha : ‖p.2 - q.2‖ < d := by
    have hb : dist p.2 q.2 ≤ dist p q := by rw [Prod.dist_eq]; exact le_max_right _ _
    have hb' : ‖p.2 - q.2‖ ≤ dist p q := by simpa only [dist_eq_norm] using hb
    exact hb'.trans_lt (hpq.trans_le (min_le_left _ _))
  have ht : |(p.1 : ℝ) - q.1| < r := by
    have hb : dist p.1 q.1 ≤ dist p q := by rw [Prod.dist_eq]; exact le_max_left _ _
    have hb' : |(p.1 : ℝ) - q.1| ≤ dist p q := by
      simpa only [Subtype.dist_eq, Real.dist_eq] using hb
    exact hb'.trans_lt (hpq.trans_le (min_le_right _ _))
  have hspace' : ‖X n p.1 p.2 - X n p.1 q.2‖ < ε / 2 := by
    apply hspace (v n) (fun t => X n t p.2) (fun t => X n t q.2)
      ((hXc n).comp (continuous_id.prodMk continuous_const))
      ((hXc n).comp (continuous_id.prodMk continuous_const))
      (fun t ht => hX n t ht _) (fun t ht => hX n t ht _) (hlip n)
      (by simpa only [hinit] using ha.le) p.1 p.1.property
  have htime := norm_trajectory_sub_time_le (fun t ht => hX n t ht q.2) (hM n)
    q.1.property p.1.property
  have htime' : ‖X n p.1 q.2 - X n q.1 q.2‖ < ε / 2 := by
    have hpos : 0 < M + 1 := by linarith
    have hb : (M + 1) * |(p.1 : ℝ) - q.1| < ε / 2 := by
      have hb := mul_lt_mul_of_pos_left ht hpos
      have he : (M + 1) * r = ε / 2 := by dsimp only [r]; field_simp
      rwa [he] at hb
    exact (htime.trans (mul_le_mul_of_nonneg_right (by linarith : M ≤ M + 1)
      (abs_nonneg _))).trans_lt hb
  rw [dist_eq_norm]
  exact (norm_sub_le_norm_sub_add_norm_sub _ (X n p.1 q.2) _).trans_lt
    ((add_lt_add hspace' htime').trans_eq (by ring))

theorem norm_logFlow_family_le {ι : Type*} {T M R : ℝ} (hT : 0 ≤ T)
    (hM0 : 0 ≤ M) (v X : ι → ℝ → E → E)
    (hX : ∀ n t, t ∈ Icc 0 T → ∀ a,
      HasDerivAt (fun s => X n s a) (v n t (X n t a)) t)
    (hinit : ∀ n a, X n 0 a = a)
    (hM : ∀ n t, t ∈ Icc 0 T → ∀ x, ‖v n t x‖ ≤ M)
    (n : ι) {t : ℝ} (ht : t ∈ Icc 0 T) {a : E} (ha : ‖a‖ ≤ R) :
    ‖X n t a‖ ≤ R + M * T := by
  have hb := norm_trajectory_sub_time_le (fun t ht => hX n t ht a) (hM n) ⟨le_rfl, hT⟩ ht
  rw [hinit, sub_zero, abs_of_nonneg ht.1] at hb
  calc
    _ ≤ ‖X n t a - a‖ + ‖a‖ := norm_le_norm_sub_add _ _
    _ ≤ M * t + R := add_le_add hb ha
    _ ≤ _ := by nlinarith [ht.2]

theorem uniform_subseq_logFlow_family [ProperSpace E] {T C M R : ℝ}
    (hT : 0 ≤ T) (hC : 0 ≤ C) (hM0 : 0 ≤ M)
    (v X : ℕ → ℝ → E → E)
    (hXc : ∀ n, Continuous (Function.uncurry (X n)))
    (hX : ∀ n t, t ∈ Icc 0 T → ∀ a,
      HasDerivAt (fun s => X n s a) (v n t (X n t a)) t)
    (hinit : ∀ n a, X n 0 a = a)
    (hM : ∀ n t, t ∈ Icc 0 T → ∀ x, ‖v n t x‖ ≤ M)
    (hlip : ∀ n t, t ∈ Icc 0 T → ∀ x y, ‖x - y‖ ≤ 1 / 2 →
      ‖v n t x - v n t y‖ ≤ C * logFlowModulus ‖x - y‖) :
    ∃ F : Icc (0 : ℝ) T × closedBall (0 : E) R → E, Continuous F ∧
      ∃ φ : ℕ → ℕ, StrictMono φ ∧
        TendstoUniformly (fun n (p : Icc (0 : ℝ) T × closedBall (0 : E) R) =>
          X (φ n) p.1 p.2) F atTop := by
  have hequi := uniformEquicontinuous_logFlow_family hT hC hM0 v X hXc hX hinit hM hlip
  let j : Icc (0 : ℝ) T × closedBall (0 : E) R → Icc (0 : ℝ) T × E :=
    fun p => (p.1, p.2)
  have hj : UniformContinuous j := uniformContinuous_fst.prodMk
    (uniformContinuous_subtype_val.comp uniformContinuous_snd)
  have huc : UniformContinuous (fun p : Icc (0 : ℝ) T × closedBall (0 : E) R =>
      (UniformFun.ofFun (fun n => X n (j p).1 (j p).2) : ℕ →ᵤ E)) :=
    (uniformEquicontinuous_iff_uniformContinuous.mp hequi).comp hj
  have heq : Equicontinuous (fun n (p : Icc (0 : ℝ) T × closedBall (0 : E) R) => X n p.1 p.2) :=
    (uniformEquicontinuous_iff_uniformContinuous.mpr huc).equicontinuous
  have hvalues (n : ℕ) (p : Icc (0 : ℝ) T × closedBall (0 : E) R) :
      X n p.1 p.2 ∈ closedBall (0 : E) (R + M * T) :=
    mem_closedBall_zero_iff.mpr (norm_logFlow_family_le hT hM0 v X hX hinit hM n p.1.property
      (mem_closedBall_zero_iff.mp p.2.property))
  obtain ⟨F, hF, _, φ, hφ, hlim⟩ := uniform_subseq_of_equicontinuous_compact
    (fun n (p : Icc (0 : ℝ) T × closedBall (0 : E) R) => X n p.1 p.2) heq
    (isCompact_closedBall (0 : E) (R + M * T)) hvalues
  exact ⟨F, hF, φ, hφ, hlim⟩

end Euler2D

end
