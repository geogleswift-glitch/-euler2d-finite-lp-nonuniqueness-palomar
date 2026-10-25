module

public import RequestProject.Euler.PlanarTrajectorySelection
public import RequestProject.Euler.LogFlowContinuity

/-! Actual jointly continuous planar particle families selected from approximations. -/

@[expose] public section

noncomputable section

open Set Filter Topology Metric MeasureTheory
open scoped NNReal

namespace Euler2D

theorem norm_planarVelocity_of_uniform_approximation
    {v : ℝ → R2 → R2} {vn : ℕ → ℝ → R2 → R2} {Kn : ℕ → ℝ≥0} {M : ℝ≥0}
    (hvn : ∀ n, IsBoundedLipschitzVelocity (vn n) (Kn n) M)
    (hconv : TendstoUniformly (fun n (p : ℝ × R2) => vn n p.1 p.2)
      (Function.uncurry v) atTop) (t : ℝ) (x : R2) : ‖v t x‖ ≤ M :=
  le_of_tendsto (hconv.tendsto_at (t, x)).norm (Eventually.of_forall fun n => (hvn n).norm_le t x)

theorem logMod_planarVelocity_of_uniform_approximation
    {v : ℝ → R2 → R2} {vn : ℕ → ℝ → R2 → R2} {C : ℝ≥0}
    (hmod : ∀ n t x y, ‖x - y‖ ≤ 1 / 2 →
      ‖vn n t x - vn n t y‖ ≤ (C : ℝ) * logFlowModulus ‖x - y‖)
    (hconv : TendstoUniformly (fun n (p : ℝ × R2) => vn n p.1 p.2)
      (Function.uncurry v) atTop) (t : ℝ) (x y : R2) (hxy : ‖x - y‖ ≤ 1 / 2) :
    ‖v t x - v t y‖ ≤ (C : ℝ) * logFlowModulus ‖x - y‖ :=
  le_of_tendsto (((hconv.tendsto_at (t, x)).sub (hconv.tendsto_at (t, y))).norm)
    (Eventually.of_forall fun n => hmod n t x y hxy)

theorem exists_continuous_planarParticleFamily
    {v : ℝ → R2 → R2} (hv : Continuous (Function.uncurry v))
    (vn : ℕ → ℝ → R2 → R2) (Kn : ℕ → ℝ≥0) (M C : ℝ≥0)
    (hvn : ∀ n, IsBoundedLipschitzVelocity (vn n) (Kn n) M)
    (hmod : ∀ n t x y, ‖x - y‖ ≤ 1 / 2 →
      ‖vn n t x - vn n t y‖ ≤ (C : ℝ) * logFlowModulus ‖x - y‖)
    (hconv : TendstoUniformly (fun n (p : ℝ × R2) => vn n p.1 p.2)
      (Function.uncurry v) atTop)
    {T : ℝ} (hT : 0 ≤ T) :
    ∃ X : ℝ → R2 → R2, Continuous (Function.uncurry X) ∧
      (∀ a, X 0 a = a) ∧
      ∀ t ∈ Icc (0 : ℝ) T, ∀ a, HasDerivAt (fun s => X s a) (v t (X t a)) t := by
  classical
  choose Y hYc hYinit hYd using fun a =>
    exists_planarParticleCurve_of_uniform_approximation hv vn Kn M C hvn hmod hconv hT a
  let Z : ℝ → R2 → R2 := fun t a => Y a t
  have hZc : Continuous (fun p : Icc (0 : ℝ) T × R2 => Z p.1 p.2) :=
    (uniformContinuous_logParticleFamily hT C.coe_nonneg M.coe_nonneg v Z hYc
      (fun t ht a => hYd a t ht) hYinit
      (fun t _ x => norm_planarVelocity_of_uniform_approximation hvn hconv t x)
      (fun t _ x y hxy => logMod_planarVelocity_of_uniform_approximation hmod hconv t x y hxy)).continuous
  let vi : Icc (0 : ℝ) T → R2 → R2 := fun t x => v t x
  let Zi : Icc (0 : ℝ) T → R2 → R2 := fun t a => Z t a
  have hvi : Continuous (Function.uncurry vi) :=
    hv.comp ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
  have hZic : Continuous (Function.uncurry Zi) := hZc
  have hg := continuous_clampedParticleDerivative (v := vi) (X := Zi) hT hvi hZic
  have hInt (t : Icc (0 : ℝ) T) (a : R2) :
      Zi t a = a + ∫ s in (0 : ℝ)..(t : ℝ), clampedParticleDerivative hT vi Zi s a := by
    have hgc : Continuous (fun s => clampedParticleDerivative hT vi Zi s a) :=
      hg.comp (continuous_id.prodMk continuous_const)
    have hd (s : ℝ) (hs : s ∈ uIcc (0 : ℝ) (t : ℝ)) :
        HasDerivAt (fun r => Z r a) (clampedParticleDerivative hT vi Zi s a) s := by
      have hs' : s ∈ Icc (0 : ℝ) T := by
        rw [uIcc_of_le t.property.1] at hs
        exact ⟨hs.1, hs.2.trans t.property.2⟩
      simpa only [clampedParticleDerivative, vi, Zi, projIcc_of_mem hT hs'] using hYd a s hs'
    have hf := intervalIntegral.integral_eq_sub_of_hasDerivAt hd (hgc.intervalIntegrable 0 t)
    change Z t a = a + _
    rw [hf]
    change Y a t = a + (Y a t - Y a 0)
    rw [hYinit a]
    abel
  refine ⟨particleIntegralExtension hT vi Zi, continuous_particleIntegralExtension hT hvi hZic,
    particleIntegralExtension_zero hT vi Zi, ?_⟩
  intro t ht a
  simpa only [particleVelocityExtension, vi, projIcc_of_mem hT ht] using
    particleIntegralExtension_hasDerivAt_on_Icc hT hvi hZic hInt ht a

end Euler2D

end
