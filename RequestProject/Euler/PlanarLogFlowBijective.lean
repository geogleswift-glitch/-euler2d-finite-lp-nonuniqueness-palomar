module

public import RequestProject.Euler.PlanarTrajectoryReversal

/-! Actual bijectivity of the selected planar flow. -/

@[expose] public section

noncomputable section

open Set Filter Topology
open scoped NNReal

namespace Euler2D

theorem logParticleFamily_injective {T : ℝ} {C : ℝ≥0}
    {v X : ℝ → R2 → R2} (hXc : Continuous (Function.uncurry X))
    (hinit : ∀ a, X 0 a = a)
    (hX : ∀ s ∈ Icc (0 : ℝ) T, ∀ a, HasDerivAt (fun r => X r a) (v s (X s a)) s)
    (hmod : ∀ s x y, ‖x - y‖ ≤ 1 / 2 →
      ‖v s x - v s y‖ ≤ (C : ℝ) * logFlowModulus ‖x - y‖)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) : Function.Injective (X t) := by
  intro a b hab
  have hc (c : R2) : Continuous (fun r => X (t - r) c) :=
    hXc.comp ((continuous_const.sub continuous_id).prodMk continuous_const)
  have hd (c : R2) (s : ℝ) (hs : s ∈ Icc (0 : ℝ) t) :
      HasDerivAt (fun r => X (t - r) c)
        (reversePlanarVelocity t v s (X (t - s) c)) s :=
    hasDerivAt_reverse_particleCurve
      (fun r hr => hX r ⟨hr.1, hr.2.trans ht.2⟩ c) hs
  have he := logParticleCurve_unique ht.1 C.coe_nonneg (hc a) (hc b) (hd a) (hd b)
    (fun s _ x y hxy => logMod_reversePlanarVelocity t hmod s x y hxy)
    (by simpa only [sub_zero] using hab)
  simpa only [sub_self, hinit] using he (show t ∈ Icc (0 : ℝ) t from ⟨ht.1, le_rfl⟩)

theorem planarParticleFamily_surjective_of_approximation
    {v : ℝ → R2 → R2} (hv : Continuous (Function.uncurry v))
    (vn : ℕ → ℝ → R2 → R2) (Kn : ℕ → ℝ≥0) (M C : ℝ≥0)
    (hvn : ∀ n, IsBoundedLipschitzVelocity (vn n) (Kn n) M)
    (hmod : ∀ n s x y, ‖x - y‖ ≤ 1 / 2 →
      ‖vn n s x - vn n s y‖ ≤ (C : ℝ) * logFlowModulus ‖x - y‖)
    (hconv : TendstoUniformly (fun n (p : ℝ × R2) => vn n p.1 p.2)
      (Function.uncurry v) atTop)
    {T : ℝ} {X : ℝ → R2 → R2} (hXc : Continuous (Function.uncurry X))
    (hinit : ∀ a, X 0 a = a)
    (hX : ∀ s ∈ Icc (0 : ℝ) T, ∀ a, HasDerivAt (fun r => X r a) (v s (X s a)) s)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) : Function.Surjective (X t) := by
  intro a
  obtain ⟨Y, hYc, hY0, hYd⟩ := exists_planarParticleCurve_of_uniform_approximation
    (continuous_reversePlanarVelocity t hv) (fun n => reversePlanarVelocity t (vn n)) Kn M C
    (fun n => isBoundedLipschitzVelocity_reverse t (hvn n))
    (fun n => logMod_reversePlanarVelocity t (hmod n))
    (tendstoUniformly_reversePlanarVelocity t hconv) ht.1 a
  have hRc : Continuous (fun s => Y (t - s)) := hYc.comp (continuous_const.sub continuous_id)
  have hRd (s : ℝ) (hs : s ∈ Icc (0 : ℝ) t) :
      HasDerivAt (fun r => Y (t - r)) (v s (Y (t - s))) s := by
    have hd := hasDerivAt_reverse_particleCurve hYd hs
    rwa [reversePlanarVelocity_reverse] at hd
  have he := logParticleCurve_unique ht.1 C.coe_nonneg
    (hXc.comp (continuous_id.prodMk continuous_const)) hRc
    (fun s hs => hX s ⟨hs.1, hs.2.trans ht.2⟩ (Y t)) hRd
    (fun s _ x y hxy => logMod_planarVelocity_of_uniform_approximation hmod hconv s x y hxy)
    (by simpa only [sub_zero] using hinit (Y t))
  refine ⟨Y t, ?_⟩
  simpa only [sub_self, hY0] using he (show t ∈ Icc (0 : ℝ) t from ⟨ht.1, le_rfl⟩)

end Euler2D

end
