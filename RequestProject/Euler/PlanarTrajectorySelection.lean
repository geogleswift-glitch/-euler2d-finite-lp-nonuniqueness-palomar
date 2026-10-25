module

public import RequestProject.Euler.SmoothParticleFlow
public import RequestProject.Euler.LogFlowCompactness
public import RequestProject.Euler.ParticleEquationLimit

/-! Actual planar particle trajectories obtained from bounded smooth approximations.

Compactness supplies a curve.  FTC and dominated convergence retain the
literal ODE; a true integral primitive supplies derivatives at both endpoints.
-/

@[expose] public section

noncomputable section

open Set Filter Topology Metric MeasureTheory
open scoped NNReal

namespace Euler2D

theorem exists_planarParticleCurve_of_uniform_approximation
    {v : ℝ → R2 → R2} (hv : Continuous (Function.uncurry v))
    (vn : ℕ → ℝ → R2 → R2) (Kn : ℕ → ℝ≥0) (M C : ℝ≥0)
    (hvn : ∀ n, IsBoundedLipschitzVelocity (vn n) (Kn n) M)
    (hmod : ∀ n t x y, ‖x - y‖ ≤ 1 / 2 →
      ‖vn n t x - vn n t y‖ ≤ (C : ℝ) * logFlowModulus ‖x - y‖)
    (hconv : TendstoUniformly (fun n (p : ℝ × R2) => vn n p.1 p.2)
      (Function.uncurry v) atTop)
    {T : ℝ} (hT : 0 ≤ T) (a : R2) :
    ∃ X : ℝ → R2, Continuous X ∧ X 0 = a ∧
      ∀ t ∈ Icc (0 : ℝ) T, HasDerivAt X (v t (X t)) t := by
  let Xn : ℕ → ℝ → R2 → R2 := fun n => boundedParticleForward (hvn n) hT
  have hXc (n : ℕ) : Continuous (Function.uncurry (Xn n)) :=
    boundedParticleForward_continuous (hvn n) hT
  have hXn (n : ℕ) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) (b : R2) :
      HasDerivAt (fun s => Xn n s b) (vn n t (Xn n t b)) t :=
    boundedParticleForward_hasDerivAt (hvn n) hT ht b
  have hinit (n : ℕ) (b : R2) : Xn n 0 b = b := boundedParticleForward_zero (hvn n) hT b
  obtain ⟨F, hF, φ, hφ, hlim⟩ := uniform_subseq_logFlow_family
    (R := ‖a‖) hT C.coe_nonneg M.coe_nonneg vn Xn hXc hXn hinit
    (fun n t _ x => (hvn n).norm_le t x) (fun n t _ x y hxy => hmod n t x y hxy)
  let aa : closedBall (0 : R2) ‖a‖ := ⟨a, mem_closedBall_zero_iff.mpr le_rfl⟩
  let Z : ℝ → R2 := fun t => F (projIcc 0 T hT t, aa)
  have hZc : Continuous Z := hF.comp ((continuous_projIcc (h := hT)).prodMk continuous_const)
  have hZlim (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) :
      Tendsto (fun n => Xn (φ n) t a) atTop (𝓝 (Z t)) := by
    have hc : projIcc 0 T hT t = (⟨t, ht⟩ : Icc (0 : ℝ) T) := projIcc_of_mem hT ht
    simpa only [Z, hc, aa] using hlim.tendsto_at (⟨t, ht⟩, aa)
  have hconvφ : TendstoUniformly (fun n (p : ℝ × R2) => vn (φ n) p.1 p.2)
      (Function.uncurry v) atTop := by
    intro U hU
    exact hφ.tendsto_atTop.eventually (hconv U hU)
  let gn : ℕ → ℝ → R2 := fun n t => vn (φ n) t (Xn (φ n) t a)
  let g : ℝ → R2 := fun t => v t (Z t)
  have hgnc (n : ℕ) : Continuous (gn n) :=
    (hvn (φ n)).continuous.comp (continuous_id.prodMk
      ((hXc (φ n)).comp (continuous_id.prodMk continuous_const)))
  have hgc : Continuous g := hv.comp (continuous_id.prodMk hZc)
  have hglim (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) :
      Tendsto (fun n => gn n t) atTop (𝓝 (g t)) := by
    have hp : Tendsto (fun n => (t, Xn (φ n) t a)) atTop (𝓝 (t, Z t)) :=
      tendsto_const_nhds.prodMk_nhds (hZlim t ht)
    exact hconvφ.tendsto_comp hv.continuousAt hp
  have hInt (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) :
      Z t = a + ∫ s in (0 : ℝ)..t, g s := by
    apply particle_integral_eq_of_tendsto (M := (M : ℝ))
      (Xn := fun n t => Xn (φ n) t a) (gn := gn)
      (fun n => hinit (φ n) a) (fun n s hs => hXn (φ n) s hs a)
      (fun n => (hgnc n).aestronglyMeasurable)
      (fun n => Filter.Eventually.of_forall (fun s => (hvn (φ n)).norm_le s _))
      ?_ hZlim ht
    filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
    exact hglim s hs
  let X : ℝ → R2 := fun t => a + ∫ s in (0 : ℝ)..t, g s
  have hXd (t : ℝ) : HasDerivAt X (g t) t :=
    (intervalIntegral.integral_hasDerivAt_right (hgc.intervalIntegrable 0 t)
      hgc.aestronglyMeasurable.stronglyMeasurableAtFilter hgc.continuousAt).const_add a
  refine ⟨X, continuous_iff_continuousAt.mpr (fun t => (hXd t).continuousAt), ?_, ?_⟩
  · simp only [X, intervalIntegral.integral_same, add_zero]
  · intro t ht
    have he : X t = Z t := (hInt t ht).symm
    simpa only [g, ← he] using hXd t

end Euler2D

end
