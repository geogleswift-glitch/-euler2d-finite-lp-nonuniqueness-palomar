module

public import RequestProject.Euler.PlanarLogParticleFlow

/-! A time buffer converts actual logarithmic particle solutions into
a homeomorphism family with true derivatives at both endpoints of the
requested interval. Clamping is used only outside that buffer. -/

@[expose] public section

noncomputable section

open Set Filter Topology Metric
open scoped NNReal

namespace Euler2D

theorem exists_planarLogHomeomorphFlow_of_uniform_approximation
    {v : ℝ → R2 → R2} (hv : Continuous (Function.uncurry v))
    (vn : ℕ → ℝ → R2 → R2) (Kn : ℕ → ℝ≥0) (M C : ℝ≥0)
    (hvn : ∀ n, IsBoundedLipschitzVelocity (vn n) (Kn n) M)
    (hmod : ∀ n t x y, ‖x - y‖ ≤ 1 / 2 →
      ‖vn n t x - vn n t y‖ ≤ (C : ℝ) * logFlowModulus ‖x - y‖)
    (hconv : TendstoUniformly (fun n (p : ℝ × R2) => vn n p.1 p.2)
      (Function.uncurry v) atTop)
    {T : ℝ} (hT : 0 ≤ T) :
    ∃ F : ℝ → R2 ≃ₜ R2,
      Continuous (fun p : ℝ × R2 => F p.1 p.2) ∧
      Continuous (fun p : ℝ × R2 => (F p.1).symm p.2) ∧
      (∀ a, F 0 a = a) ∧
      ∀ t ∈ Icc (0 : ℝ) T, ∀ a,
        HasDerivAt (fun s => F s a) (v t (F t a)) t := by
  let w : ℝ → R2 → R2 := fun t x => v (t - 1) x
  let wn : ℕ → ℝ → R2 → R2 := fun n t x => vn n (t - 1) x
  have hshift : Continuous (fun p : ℝ × R2 => (p.1 - 1, p.2)) :=
    (continuous_fst.sub continuous_const).prodMk continuous_snd
  have hw : Continuous (Function.uncurry w) := hv.comp hshift
  have hwn (n : ℕ) : IsBoundedLipschitzVelocity (wn n) (Kn n) M :=
    ⟨(hvn n).continuous.comp hshift, fun t => (hvn n).lipschitz (t - 1),
      fun t x => (hvn n).norm_le (t - 1) x⟩
  have hconvw : TendstoUniformly (fun n (p : ℝ × R2) => wn n p.1 p.2)
      (Function.uncurry w) atTop := by
    rw [Metric.tendstoUniformly_iff] at hconv ⊢
    intro ε hε
    filter_upwards [hconv ε hε] with n hn p
    exact hn (p.1 - 1, p.2)
  have hU : 0 ≤ T + 2 := by linarith
  obtain ⟨S⟩ := exists_planarLogParticleFlow_of_uniform_approximation hw wn Kn M C hwn
    (fun n t x y hxy => hmod n (t - 1) x y hxy) hconvw hU
  have h1 : (1 : ℝ) ∈ Icc (0 : ℝ) (T + 2) := by constructor <;> linarith
  let start : Icc (0 : ℝ) (T + 2) := ⟨1, h1⟩
  let c : ℝ → Icc (0 : ℝ) (T + 2) := fun t => Set.projIcc 0 (T + 2) hU (t + 1)
  let F : ℝ → R2 ≃ₜ R2 := fun t => (S.homeomorph start).symm.trans (S.homeomorph (c t))
  have hc : Continuous (fun t : ℝ => (c t : ℝ)) :=
    continuous_subtype_val.comp ((continuous_projIcc (h := hU)).comp
      (continuous_id.add continuous_const))
  have hforward : Continuous (fun p : ℝ × R2 => F p.1 p.2) := by
    have hback1 : Continuous (fun a => S.backward 1 a) :=
      S.continuous_backward.comp (continuous_const.prodMk continuous_id)
    have h := S.continuous_forward.comp
      ((hc.comp continuous_fst).prodMk (hback1.comp continuous_snd))
    exact h.congr (fun _ => rfl)
  have hbackward : Continuous (fun p : ℝ × R2 => (F p.1).symm p.2) := by
    have hf1 : Continuous (fun a => S.forward 1 a) :=
      S.continuous_forward.comp (continuous_const.prodMk continuous_id)
    have h := hf1.comp (S.continuous_backward.comp
      ((hc.comp continuous_fst).prodMk continuous_snd))
    exact h.congr (fun _ => rfl)
  refine ⟨F, hforward, hbackward, ?_, ?_⟩
  · intro a
    change S.forward (Set.projIcc 0 (T + 2) hU ((0 : ℝ) + 1)) (S.backward 1 a) = a
    rw [zero_add, Set.projIcc_of_mem hU h1]
    exact S.right_inv 1 h1 a
  · intro t ht a
    have htU : t + 1 ∈ Icc (0 : ℝ) (T + 2) := by
      constructor <;> linarith [ht.1, ht.2]
    have heq : (fun s => F s a) =ᶠ[𝓝 t]
        (fun s => S.forward (s + 1) (S.backward 1 a)) := by
      filter_upwards [Ioo_mem_nhds (by linarith [ht.1] : -1 < t)
        (by linarith [ht.2] : t < T + 1)] with s hs
      change S.forward (Set.projIcc 0 (T + 2) hU (s + 1)) (S.backward 1 a) = _
      have hsU : s + 1 ∈ Icc (0 : ℝ) (T + 2) := by constructor <;> linarith [hs.1, hs.2]
      rw [Set.projIcc_of_mem hU hsU]
    have hd := (S.derivative (t + 1) htU (S.backward 1 a)).scomp t
      ((hasDerivAt_id t).add_const 1)
    have hd' : HasDerivAt (fun s => S.forward (s + 1) (S.backward 1 a))
        (v t (S.forward (t + 1) (S.backward 1 a))) t := by
      simpa only [w, Function.comp_def, add_sub_cancel_right, one_smul] using hd
    have hf := hd'.congr_of_eventuallyEq heq
    simpa only [heq.eq_of_nhds] using hf

end Euler2D

end
