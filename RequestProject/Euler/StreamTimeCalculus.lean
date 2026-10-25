module

public import RequestProject.Euler.StreamFunction

/-!
# Time differentiation of the actual stream decomposition

Joint smoothness makes the time and spatial derivatives commute. The
explicit stream function of an Euler test therefore differentiates to
an actual scalar test and gives the component identities used in the
vorticity-to-momentum calculation.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ContDiff

namespace Euler2D

lemma timeDerivative_eq_joint_fderiv {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {χ : ℝ → R2 → F} (hχ : Differentiable ℝ (Function.uncurry χ)) (t : ℝ) (x : R2) :
    deriv (fun s => χ s x) t = fderiv ℝ (Function.uncurry χ) (t, x) (1, 0) := by
  have hline : HasDerivAt (fun s : ℝ => (s, x)) ((1 : ℝ), (0 : R2)) t :=
    (hasDerivAt_id t).prodMk (hasDerivAt_const t x)
  exact ((hχ (t, x)).hasFDerivAt.comp_hasDerivAt t hline).deriv

lemma spatialDerivative_eq_joint_fderiv {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {χ : ℝ → R2 → F} (hχ : Differentiable ℝ (Function.uncurry χ))
    (t : ℝ) (x : R2) (i : Fin 2) :
    pd i (χ t) x = fderiv ℝ (Function.uncurry χ) (t, x) (0, EuclideanSpace.single i 1) := by
  have hline : HasFDerivAt (fun y : R2 => (t, y))
      (ContinuousLinearMap.inr ℝ ℝ R2) x := hasFDerivAt_prodMk_right t x
  have hd := (hχ (t, x)).hasFDerivAt.comp x hline
  unfold pd
  rw [show χ t = Function.uncurry χ ∘ (fun y : R2 => (t, y)) from rfl, hd.fderiv]
  rfl

lemma contDiff_timeDerivative {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {χ : ℝ → R2 → F} (hχ : ContDiff ℝ ∞ (Function.uncurry χ)) :
    ContDiff ℝ ∞ (Function.uncurry (fun t x => deriv (fun s => χ s x) t)) := by
  have heq : Function.uncurry (fun t x => deriv (fun s => χ s x) t) =
      fun p : ℝ × R2 => fderiv ℝ (Function.uncurry χ) p (1, 0) := by
    funext p
    exact timeDerivative_eq_joint_fderiv (hχ.differentiable (by simp)) p.1 p.2
  rw [heq]
  exact (hχ.fderiv_right (by simp)).clm_apply contDiff_const

lemma contDiff_spatialDerivative {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {χ : ℝ → R2 → F} (hχ : ContDiff ℝ ∞ (Function.uncurry χ)) (i : Fin 2) :
    ContDiff ℝ ∞ (Function.uncurry (fun t x => pd i (χ t) x)) := by
  have heq : Function.uncurry (fun t x => pd i (χ t) x) =
      fun p : ℝ × R2 => fderiv ℝ (Function.uncurry χ) p (0, EuclideanSpace.single i 1) := by
    funext p
    exact spatialDerivative_eq_joint_fderiv (hχ.differentiable (by simp)) p.1 p.2 i
  rw [heq]
  exact (hχ.fderiv_right (by simp)).clm_apply contDiff_const

lemma fderiv_directional_comm {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F}
    (hf : ContDiff ℝ ∞ f) (x v w : E) :
    fderiv ℝ (fun y => fderiv ℝ f y v) x w =
      fderiv ℝ (fun y => fderiv ℝ f y w) x v := by
  have hd : Differentiable ℝ (fderiv ℝ f) :=
    (hf.fderiv_right (by simp) : ContDiff ℝ ∞ (fderiv ℝ f)).differentiable (by simp)
  rw [fderiv_clm_apply (hd x) (differentiableAt_const v),
    fderiv_clm_apply (hd x) (differentiableAt_const w)]
  simpa using (hf.contDiffAt.isSymmSndFDerivAt (by
    simp only [minSmoothness_of_isRCLikeNormedField]
    change ((2 : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞)
    exact WithTop.coe_le_coe.mpr le_top)).eq w v

/-- Classical mixed partials in the time and each physical spatial
coordinate agree for any jointly smooth family. -/
theorem pd_timeDerivative_comm {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {χ : ℝ → R2 → F} (hχ : ContDiff ℝ ∞ (Function.uncurry χ))
    (i : Fin 2) (t : ℝ) (x : R2) :
    pd i (fun y => deriv (fun s => χ s y) t) x =
      deriv (fun s => pd i (χ s) x) t := by
  rw [spatialDerivative_eq_joint_fderiv ((contDiff_timeDerivative hχ).differentiable (by simp)),
    timeDerivative_eq_joint_fderiv ((contDiff_spatialDerivative hχ i).differentiable (by simp))]
  have htime : Function.uncurry (fun t x => deriv (fun s => χ s x) t) =
      fun p : ℝ × R2 => fderiv ℝ (Function.uncurry χ) p (1, 0) := by
    funext p
    exact timeDerivative_eq_joint_fderiv (hχ.differentiable (by simp)) p.1 p.2
  have hspace : Function.uncurry (fun t x => pd i (χ t) x) =
      fun p : ℝ × R2 => fderiv ℝ (Function.uncurry χ) p (0, EuclideanSpace.single i 1) := by
    funext p
    exact spatialDerivative_eq_joint_fderiv (hχ.differentiable (by simp)) p.1 p.2 i
  rw [htime, hspace]
  exact fderiv_directional_comm hχ (t, x) (1, 0) (0, EuclideanSpace.single i 1)

theorem isScalarTest_timeDerivative {χ : ℝ → R2 → ℝ}
    (hχ : ContDiff ℝ ∞ (Function.uncurry χ)) (hper : ∀ t, IsTorusPeriodic (χ t)) (t : ℝ) :
    IsScalarTest (fun x => deriv (fun s => χ s x) t) := by
  refine ⟨(contDiff_timeDerivative hχ).comp (contDiff_const.prodMk contDiff_id), ?_⟩
  intro x i
  have heq : (fun s => χ s (x + EuclideanSpace.single i (2 * Real.pi))) =
      fun s => χ s x := funext fun s => hper s x i
  change deriv (fun s => χ s (x + EuclideanSpace.single i (2 * Real.pi))) t =
    deriv (fun s => χ s x) t
  rw [heq]

lemma eulerTest_stream_time_test {T : ℝ} {φ : ℝ → R2 → R2} (hφ : IsEulerTest T φ) (t : ℝ) :
    IsScalarTest (fun x => deriv (fun s => streamFunction (φ s) x) t) :=
  isScalarTest_timeDerivative (contDiff_streamFunction_family hφ.smooth)
    (eulerTest_streamFunction hφ).periodic t

lemma deriv_sub_spatialDerivative {a : ℝ → ℝ} {χ : ℝ → R2 → ℝ}
    (ha : Differentiable ℝ a) (hχ : ContDiff ℝ ∞ (Function.uncurry χ))
    (i : Fin 2) (t : ℝ) (x : R2) :
    deriv (fun s => a s - pd i (χ s) x) t =
      deriv a t - pd i (fun y => deriv (fun s => χ s y) t) x := by
  have hp : ContDiff ℝ ∞ (fun s : ℝ => pd i (χ s) x) :=
    (contDiff_spatialDerivative hχ i).comp (contDiff_id.prodMk contDiff_const)
  change deriv (a - fun s => pd i (χ s) x) t = _
  rw [deriv_sub (ha t) (hp.differentiable (by simp) t), ← pd_timeDerivative_comm hχ i t x]

lemma deriv_add_spatialDerivative {a : ℝ → ℝ} {χ : ℝ → R2 → ℝ}
    (ha : Differentiable ℝ a) (hχ : ContDiff ℝ ∞ (Function.uncurry χ))
    (i : Fin 2) (t : ℝ) (x : R2) :
    deriv (fun s => a s + pd i (χ s) x) t =
      deriv a t + pd i (fun y => deriv (fun s => χ s y) t) x := by
  have hp : ContDiff ℝ ∞ (fun s : ℝ => pd i (χ s) x) :=
    (contDiff_spatialDerivative hχ i).comp (contDiff_id.prodMk contDiff_const)
  change deriv (a + fun s => pd i (χ s) x) t = _
  rw [deriv_add (ha t) (hp.differentiable (by simp) t), ← pd_timeDerivative_comm hχ i t x]

lemma eulerTest_stream_deriv_zero {T : ℝ} {φ : ℝ → R2 → R2}
    (hφ : IsEulerTest T φ) (t : ℝ) (x : R2) :
    deriv (fun s => φ s x 0) t =
      deriv (fun s => streamConstant (φ s) 0) t -
        pd 1 (fun y => deriv (fun s => streamFunction (φ s) y) t) x := by
  have heq : (fun s => φ s x 0) = fun s => streamConstant (φ s) 0 -
      pd 1 (streamFunction (φ s)) x := by
    funext s
    have hh := congrArg (fun v : R2 => v 0) ((eulerTest_stream_decomposition hφ).2.2.2 s x)
    simpa only [PiLp.add_apply, torusVec_apply_zero, sub_eq_add_neg] using hh
  rw [heq]
  exact deriv_sub_spatialDerivative
    (((EuclideanSpace.proj 0 : R2 →L[ℝ] ℝ).contDiff.comp
      (contDiff_streamConstant_family hφ.smooth)).differentiable (by simp))
    (contDiff_streamFunction_family hφ.smooth) 1 t x

lemma eulerTest_stream_deriv_one {T : ℝ} {φ : ℝ → R2 → R2}
    (hφ : IsEulerTest T φ) (t : ℝ) (x : R2) :
    deriv (fun s => φ s x 1) t =
      deriv (fun s => streamConstant (φ s) 1) t +
        pd 0 (fun y => deriv (fun s => streamFunction (φ s) y) t) x := by
  have heq : (fun s => φ s x 1) = fun s => streamConstant (φ s) 1 +
      pd 0 (streamFunction (φ s)) x := by
    funext s
    have hh := congrArg (fun v : R2 => v 1) ((eulerTest_stream_decomposition hφ).2.2.2 s x)
    simpa only [PiLp.add_apply, torusVec_apply_one] using hh
  rw [heq]
  exact deriv_add_spatialDerivative
    (((EuclideanSpace.proj 1 : R2 →L[ℝ] ℝ).contDiff.comp
      (contDiff_streamConstant_family hφ.smooth)).differentiable (by simp))
    (contDiff_streamFunction_family hφ.smooth) 0 t x

lemma eulerTest_stream_pd_zero {T : ℝ} {φ : ℝ → R2 → R2}
    (hφ : IsEulerTest T φ) (j : Fin 2) (t : ℝ) (x : R2) :
    pd j (φ t) x 0 = -pd j (pd 1 (streamFunction (φ t))) x := by
  have hslice : ContDiff ℝ ∞ (φ t) := hφ.smooth.comp (contDiff_const.prodMk contDiff_id)
  have heq : (fun y => φ t y 0) = fun y => streamConstant (φ t) 0 -
      pd 1 (streamFunction (φ t)) y := by
    funext y
    have hh := congrArg (fun v : R2 => v 0) ((eulerTest_stream_decomposition hφ).2.2.2 t y)
    simpa only [PiLp.add_apply, torusVec_apply_zero, sub_eq_add_neg] using hh
  rw [← torus_pd_component (φ t) x (hslice.differentiable (by simp) x) j 0, heq]
  simp only [pd, fderiv_const_sub, ContinuousLinearMap.neg_apply]
  rfl

lemma eulerTest_stream_pd_one {T : ℝ} {φ : ℝ → R2 → R2}
    (hφ : IsEulerTest T φ) (j : Fin 2) (t : ℝ) (x : R2) :
    pd j (φ t) x 1 = pd j (pd 0 (streamFunction (φ t))) x := by
  have hslice : ContDiff ℝ ∞ (φ t) := hφ.smooth.comp (contDiff_const.prodMk contDiff_id)
  have heq : (fun y => φ t y 1) = fun y => streamConstant (φ t) 1 +
      pd 0 (streamFunction (φ t)) y := by
    funext y
    have hh := congrArg (fun v : R2 => v 1) ((eulerTest_stream_decomposition hφ).2.2.2 t y)
    simpa only [PiLp.add_apply, torusVec_apply_one] using hh
  rw [← torus_pd_component (φ t) x (hslice.differentiable (by simp) x) j 1, heq]
  simp only [pd, fderiv_const_add]
  rfl

end Euler2D

end
