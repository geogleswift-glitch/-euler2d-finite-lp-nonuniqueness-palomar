module

public import RequestProject.Euler.LogFlowVelocityStability

/-! A uniform velocity approximation converges to the same actual
unique particle family for every initial point. The actual inverse
maps then converge by their genuine two-sided identities. -/

@[expose] public section

set_option maxHeartbeats 1500000

noncomputable section

open Set Filter Topology Metric

namespace Euler2D

theorem tendstoUniformly_logFlow_of_velocity_approximation
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {T C : ℝ} (hT : 0 ≤ T) (hC : 0 ≤ C)
    {vn : ℕ → ℝ → E → E} {v : ℝ → E → E}
    {Xn : ℕ → ℝ → E → E} {X : ℝ → E → E}
    (hXnc : ∀ n, Continuous (Function.uncurry (Xn n)))
    (hXc : Continuous (Function.uncurry X))
    (hXnd : ∀ n t, t ∈ Icc (0 : ℝ) T → ∀ a,
      HasDerivAt (fun s => Xn n s a) (vn n t (Xn n t a)) t)
    (hXd : ∀ t ∈ Icc (0 : ℝ) T, ∀ a,
      HasDerivAt (fun s => X s a) (v t (X t a)) t)
    (hinit : ∀ n a, Xn n 0 a = X 0 a)
    (hmod : ∀ n t, t ∈ Icc (0 : ℝ) T → ∀ x y : E, ‖x - y‖ ≤ 1 / 2 →
      ‖vn n t x - vn n t y‖ ≤ C * logFlowModulus ‖x - y‖)
    (hconv : TendstoUniformly (fun n (p : ℝ × E) => vn n p.1 p.2) (Function.uncurry v) atTop) :
    TendstoUniformly (fun n (p : Icc (0 : ℝ) T × E) => Xn n p.1 p.2)
      (fun p => X p.1 p.2) atTop := by
  rw [Metric.tendstoUniformly_iff] at hconv ⊢
  intro ε hε
  obtain ⟨δ, hδ, hstable⟩ := logFlow_uniform_velocity_stability hT hC hε (E := E)
  filter_upwards [hconv δ hδ] with n hn p
  have hfield (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) (x : E) : ‖vn n t x - v t x‖ ≤ δ := by
    have he := (hn (t, x)).le
    simpa only [Function.uncurry_apply_pair, dist_eq_norm, norm_sub_rev] using he
  have hbound := hstable (vn n) v (fun t => Xn n t p.2) (fun t => X t p.2)
    ((hXnc n).comp (continuous_id.prodMk continuous_const))
    (hXc.comp (continuous_id.prodMk continuous_const))
    (fun t ht => hXnd n t ht p.2) (fun t ht => hXd t ht p.2)
    (hmod n) hfield (hinit n p.2) p.1 p.1.property
  simpa only [dist_eq_norm, norm_sub_rev] using hbound

theorem tendsto_inverse_of_uniform_forward_limit
    {E : Type*} [PseudoMetricSpace E] {F G : ℕ → E → E} {f g : E → E}
    (hg : Continuous g) (hleft : Function.LeftInverse g f)
    (hFnright : ∀ n, Function.RightInverse (G n) (F n))
    (hconv : TendstoUniformly F f atTop) (a : E) :
    Tendsto (fun n => G n a) atTop (𝓝 (g a)) := by
  have hin : Tendsto (fun n => f (G n a)) atTop (𝓝 a) := by
    rw [Metric.tendsto_atTop]
    rw [Metric.tendstoUniformly_iff] at hconv
    intro ε hε
    obtain ⟨N, hN⟩ := eventually_atTop.mp (hconv ε hε)
    refine ⟨N, fun n hn => ?_⟩
    have he := hN n hn (G n a)
    simpa only [hFnright n a, dist_comm] using he
  have hout := (hg.tendsto a).comp hin
  have he : (g ∘ fun n => f (G n a)) = (fun n => G n a) :=
    funext (fun n => hleft (G n a))
  rw [he] at hout
  exact hout

end Euler2D

end
