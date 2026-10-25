module

public import RequestProject.Euler.LogFlowCompactness

/-!
# Uniform compactness of the actual inverse particle maps

A time rescaling puts every shorter comparison interval into one fixed
outer window.  Reversing actual trajectories then controls inverse maps
in space.  Their time modulus follows from the true two-sided inverse
identities and the common speed bound.
-/

@[expose] public section

noncomputable section

open Set Filter Topology Real Metric
open scoped UniformConvergence

namespace Euler2D

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- One distance threshold works for every comparison horizon at most `T`.
The proof rescales the actual ODE to the fixed window `[0,T+1]`. -/
theorem logFlow_uniform_endpoint_stability {T C ε : ℝ}
    (hT : 0 ≤ T) (hC : 0 ≤ C) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ S ∈ Icc (0 : ℝ) T,
      ∀ (v : ℝ → E → E) (X Y : ℝ → E),
      Continuous X → Continuous Y →
      (∀ t ∈ Icc 0 S, HasDerivAt X (v t (X t)) t) →
      (∀ t ∈ Icc 0 S, HasDerivAt Y (v t (Y t)) t) →
      (∀ t ∈ Icc 0 S, ∀ x y : E, ‖x - y‖ ≤ 1 / 2 →
        ‖v t x - v t y‖ ≤ C * logFlowModulus ‖x - y‖) →
      ‖X 0 - Y 0‖ ≤ δ → ‖X S - Y S‖ < ε := by
  let U := T + 1
  have hU : 0 < U := by dsimp only [U]; linarith
  obtain ⟨δ, hδ, hstable⟩ := logFlow_uniform_stability (E := E) hU.le hC hε
  refine ⟨δ, hδ, fun S hS v X Y hXc hYc hX hY hlip hinit => ?_⟩
  let a := S / U
  have ha : 0 ≤ a := div_nonneg hS.1 hU.le
  have ha1 : a ≤ 1 := (div_le_one hU).mpr (by dsimp only [U]; linarith [hS.2])
  have haU : a * U = S := div_mul_cancel₀ S hU.ne'
  have htime (r : ℝ) (hr : r ∈ Icc 0 U) : a * r ∈ Icc 0 S :=
    ⟨mul_nonneg ha hr.1, (mul_le_mul_of_nonneg_left hr.2 ha).trans_eq haU⟩
  let V : ℝ → E → E := fun r x => a • v (a * r) x
  let A : ℝ → E := fun r => X (a * r)
  let B : ℝ → E := fun r => Y (a * r)
  have hAd (r : ℝ) (hr : r ∈ Icc 0 U) : HasDerivAt A (V r (A r)) r := by
    simpa only [A, V, Function.comp_def, mul_one] using
      (hX (a * r) (htime r hr)).scomp r ((hasDerivAt_id r).const_mul a)
  have hBd (r : ℝ) (hr : r ∈ Icc 0 U) : HasDerivAt B (V r (B r)) r := by
    simpa only [B, V, Function.comp_def, mul_one] using
      (hY (a * r) (htime r hr)).scomp r ((hasDerivAt_id r).const_mul a)
  have hVlip (r : ℝ) (hr : r ∈ Icc 0 U) (x y : E) (hxy : ‖x - y‖ ≤ 1 / 2) :
      ‖V r x - V r y‖ ≤ C * logFlowModulus ‖x - y‖ := by
    have hmod : 0 ≤ logFlowModulus ‖x - y‖ := by
      have hm := monotoneOn_logFlowModulus (show (0 : ℝ) ∈ Icc 0 1 by simp)
        ⟨norm_nonneg _, by linarith⟩ (norm_nonneg (x - y))
      simpa only [logFlowModulus, zero_mul, sub_self] using hm
    dsimp only [V]
    rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_nonneg ha]
    exact (mul_le_mul_of_nonneg_left (hlip _ (htime r hr) x y hxy) ha).trans
      (mul_le_of_le_one_left (mul_nonneg hC hmod) ha1)
  have hlast := hstable V A B
    (hXc.comp (continuous_const.mul continuous_id))
    (hYc.comp (continuous_const.mul continuous_id)) hAd hBd hVlip
    (by simpa only [A, B, mul_zero] using hinit) U ⟨hU.le, le_rfl⟩
  simpa only [A, B, haU] using hlast

/-- Reverse actual forward trajectories to get a common spatial modulus
for their genuine inverse maps.  No regularity assumption on `Y` is used. -/
theorem inverse_logFlow_uniform_spatial_stability {ι : Type*} {T C ε : ℝ}
    (hT : 0 ≤ T) (hC : 0 ≤ C) (hε : 0 < ε)
    (v X Y : ι → ℝ → E → E)
    (hXc : ∀ n, Continuous (Function.uncurry (X n)))
    (hX : ∀ n t, t ∈ Icc 0 T → ∀ a,
      HasDerivAt (fun s => X n s a) (v n t (X n t a)) t)
    (hinit : ∀ n a, X n 0 a = a)
    (hright : ∀ n t, t ∈ Icc 0 T → ∀ a, X n t (Y n t a) = a)
    (hlip : ∀ n t, t ∈ Icc 0 T → ∀ x y, ‖x - y‖ ≤ 1 / 2 →
      ‖v n t x - v n t y‖ ≤ C * logFlowModulus ‖x - y‖) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ n t, t ∈ Icc 0 T → ∀ a b,
      ‖a - b‖ ≤ δ → ‖Y n t a - Y n t b‖ < ε := by
  obtain ⟨δ, hδ, hstable⟩ := logFlow_uniform_endpoint_stability (E := E) hT hC hε
  refine ⟨δ, hδ, fun n t ht a b hab => ?_⟩
  have htime (r : ℝ) (hr : r ∈ Icc 0 t) : t - r ∈ Icc 0 T :=
    ⟨by linarith [hr.2], by linarith [hr.1, ht.2]⟩
  have hrev (a : E) (r : ℝ) (hr : r ∈ Icc 0 t) :
      HasDerivAt (fun s => X n (t - s) (Y n t a))
        (-v n (t - r) (X n (t - r) (Y n t a))) r := by
    simpa only [Function.comp_def, id_eq, zero_sub, neg_one_smul] using
      (hX n (t - r) (htime r hr) (Y n t a)).scomp r
        ((hasDerivAt_const r t).sub (hasDerivAt_id r))
  have hcomp (a : E) : Continuous (fun r => X n (t - r) (Y n t a)) :=
    (hXc n).comp ((continuous_const.sub continuous_id).prodMk continuous_const)
  have hlast := hstable t ht (fun r x => -v n (t - r) x)
    (fun r => X n (t - r) (Y n t a)) (fun r => X n (t - r) (Y n t b))
    (hcomp a) (hcomp b) (hrev a) (hrev b)
    (by
      intro r hr x y hxy
      simpa only [neg_sub_neg, norm_sub_rev] using hlip n (t - r) (htime r hr) x y hxy)
    (by simpa only [sub_zero, hright n t ht] using hab)
  simpa only [sub_self, hinit] using hlast

/-- The inverse family has a common modulus in both time and space,
derived from actual trajectories and their two-sided inverse laws. -/
theorem uniformEquicontinuous_inverse_logFlow_family {ι : Type*} {T C M : ℝ}
    (hT : 0 ≤ T) (hC : 0 ≤ C) (hM0 : 0 ≤ M)
    (v X Y : ι → ℝ → E → E)
    (hXc : ∀ n, Continuous (Function.uncurry (X n)))
    (hX : ∀ n t, t ∈ Icc 0 T → ∀ a,
      HasDerivAt (fun s => X n s a) (v n t (X n t a)) t)
    (hinit : ∀ n a, X n 0 a = a)
    (hright : ∀ n t, t ∈ Icc 0 T → ∀ a, X n t (Y n t a) = a)
    (hleft : ∀ n t, t ∈ Icc 0 T → ∀ a, Y n t (X n t a) = a)
    (hM : ∀ n t, t ∈ Icc 0 T → ∀ x, ‖v n t x‖ ≤ M)
    (hlip : ∀ n t, t ∈ Icc 0 T → ∀ x y, ‖x - y‖ ≤ 1 / 2 →
      ‖v n t x - v n t y‖ ≤ C * logFlowModulus ‖x - y‖) :
    UniformEquicontinuous (fun n (p : Icc (0 : ℝ) T × E) => Y n p.1 p.2) := by
  apply Metric.uniformEquicontinuous_iff.mpr
  intro ε hε
  obtain ⟨d, hd, hspace⟩ := inverse_logFlow_uniform_spatial_stability hT hC
    (div_pos hε (by norm_num : (0 : ℝ) < 2)) v X Y hXc hX hinit hright hlip
  let r := d / (M + 1)
  have hM1 : 0 < M + 1 := by linarith
  have hr : 0 < r := div_pos hd hM1
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
  have hspace' : ‖Y n p.1 p.2 - Y n p.1 q.2‖ < ε / 2 :=
    hspace n p.1 p.1.property p.2 q.2 ha.le
  let b := Y n q.1 q.2
  have hfast := norm_trajectory_sub_time_le (fun t ht => hX n t ht b) (hM n)
    q.1.property p.1.property
  have hq : X n q.1 b = q.2 := hright n q.1 q.1.property q.2
  rw [hq] at hfast
  have hprod : (M + 1) * |(p.1 : ℝ) - q.1| < d := by
    have hb := mul_lt_mul_of_pos_left ht hM1
    have he : (M + 1) * r = d := by dsimp only [r]; field_simp
    rwa [he] at hb
  have hnear : ‖q.2 - X n p.1 b‖ < d := by
    rw [norm_sub_rev]
    exact (hfast.trans (mul_le_mul_of_nonneg_right (by linarith : M ≤ M + 1)
      (abs_nonneg _))).trans_lt hprod
  have htime' : ‖Y n p.1 q.2 - Y n q.1 q.2‖ < ε / 2 := by
    have hh := hspace n p.1 p.1.property q.2 (X n p.1 b) hnear.le
    rw [hleft n p.1 p.1.property b] at hh
    exact hh
  rw [dist_eq_norm]
  exact (norm_sub_le_norm_sub_add_norm_sub _ (Y n p.1 q.2) _).trans_lt
    ((add_lt_add hspace' htime').trans_eq (by ring))

/-- A bounded speed controls how far inverse particles can lie from
their terminal positions. -/
theorem norm_inverse_logFlow_family_le {ι : Type*} {T M R : ℝ}
    (hT : 0 ≤ T) (hM0 : 0 ≤ M) (v X Y : ι → ℝ → E → E)
    (hX : ∀ n t, t ∈ Icc 0 T → ∀ a,
      HasDerivAt (fun s => X n s a) (v n t (X n t a)) t)
    (hinit : ∀ n a, X n 0 a = a)
    (hright : ∀ n t, t ∈ Icc 0 T → ∀ a, X n t (Y n t a) = a)
    (hM : ∀ n t, t ∈ Icc 0 T → ∀ x, ‖v n t x‖ ≤ M)
    (n : ι) {t : ℝ} (ht : t ∈ Icc 0 T) {a : E} (ha : ‖a‖ ≤ R) :
    ‖Y n t a‖ ≤ R + M * T := by
  have hb := norm_trajectory_sub_time_le (fun s hs => hX n s hs (Y n t a)) (hM n)
    ⟨le_rfl, hT⟩ ht
  rw [hinit, hright n t ht a, sub_zero, abs_of_nonneg ht.1, norm_sub_rev] at hb
  calc
    _ ≤ ‖Y n t a - a‖ + ‖a‖ := norm_le_norm_sub_add _ _
    _ ≤ M * t + R := add_le_add hb ha
    _ ≤ _ := by nlinarith [ht.2]

theorem uniform_subseq_inverse_logFlow_family [ProperSpace E] {T C M R : ℝ}
    (hT : 0 ≤ T) (hC : 0 ≤ C) (hM0 : 0 ≤ M)
    (v X Y : ℕ → ℝ → E → E)
    (hXc : ∀ n, Continuous (Function.uncurry (X n)))
    (hX : ∀ n t, t ∈ Icc 0 T → ∀ a,
      HasDerivAt (fun s => X n s a) (v n t (X n t a)) t)
    (hinit : ∀ n a, X n 0 a = a)
    (hright : ∀ n t, t ∈ Icc 0 T → ∀ a, X n t (Y n t a) = a)
    (hleft : ∀ n t, t ∈ Icc 0 T → ∀ a, Y n t (X n t a) = a)
    (hM : ∀ n t, t ∈ Icc 0 T → ∀ x, ‖v n t x‖ ≤ M)
    (hlip : ∀ n t, t ∈ Icc 0 T → ∀ x y, ‖x - y‖ ≤ 1 / 2 →
      ‖v n t x - v n t y‖ ≤ C * logFlowModulus ‖x - y‖) :
    ∃ F : Icc (0 : ℝ) T × closedBall (0 : E) R → E, Continuous F ∧
      ∃ φ : ℕ → ℕ, StrictMono φ ∧
        TendstoUniformly (fun n (p : Icc (0 : ℝ) T × closedBall (0 : E) R) =>
          Y (φ n) p.1 p.2) F atTop := by
  have hequi := uniformEquicontinuous_inverse_logFlow_family hT hC hM0 v X Y
    hXc hX hinit hright hleft hM hlip
  let j : Icc (0 : ℝ) T × closedBall (0 : E) R → Icc (0 : ℝ) T × E :=
    fun p => (p.1, p.2)
  have hj : UniformContinuous j := uniformContinuous_fst.prodMk
    (uniformContinuous_subtype_val.comp uniformContinuous_snd)
  have huc : UniformContinuous (fun p : Icc (0 : ℝ) T × closedBall (0 : E) R =>
      (UniformFun.ofFun (fun n => Y n (j p).1 (j p).2) : ℕ →ᵤ E)) :=
    (uniformEquicontinuous_iff_uniformContinuous.mp hequi).comp hj
  have heq : Equicontinuous (fun n (p : Icc (0 : ℝ) T × closedBall (0 : E) R) => Y n p.1 p.2) :=
    (uniformEquicontinuous_iff_uniformContinuous.mpr huc).equicontinuous
  have hvalues (n : ℕ) (p : Icc (0 : ℝ) T × closedBall (0 : E) R) :
      Y n p.1 p.2 ∈ closedBall (0 : E) (R + M * T) :=
    mem_closedBall_zero_iff.mpr (norm_inverse_logFlow_family_le hT hM0 v X Y
      hX hinit hright hM n p.1.property (mem_closedBall_zero_iff.mp p.2.property))
  obtain ⟨F, hF, _, φ, hφ, hlim⟩ := uniform_subseq_of_equicontinuous_compact
    (fun n (p : Icc (0 : ℝ) T × closedBall (0 : E) R) => Y n p.1 p.2) heq
    (isCompact_closedBall (0 : E) (R + M * T)) hvalues
  exact ⟨F, hF, φ, hφ, hlim⟩

end Euler2D

end
