module

public import RequestProject.Euler.WeakDivergenceLogFlowExistence
public import RequestProject.Euler.PlanarLogHomeomorphFlow
public import RequestProject.Euler.LogFlowIntervalUniqueness
public import RequestProject.Euler.ComplexPlanarBiotSavart

/-! Actual area-preserving homeomorphism flows of weakly divergence
free logarithmic velocities, with true derivatives at both endpoints.
The complex and real Euclidean plane realizations agree exactly. -/

@[expose] public section

set_option maxHeartbeats 2500000

noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal

namespace Euler2D

theorem exists_measurePreserving_logHomeomorphFlow
    {v : ℝ → R2 → R2} {M C : ℝ≥0}
    (hv : Continuous (Function.uncurry v)) (hM : ∀ t x, ‖v t x‖ ≤ M)
    (hlog : ∀ t x y, ‖x - y‖ ≤ 1 / 2 → ‖v t x - v t y‖ ≤ C * logFlowModulus ‖x - y‖)
    (hdiv : ∀ t, IsPlanarWeaklyDivergenceFree (v t)) {T : ℝ} (hT : 0 ≤ T) :
    ∃ F : ℝ → R2 ≃ₜ R2,
      Continuous (fun p : ℝ × R2 => F p.1 p.2) ∧
      Continuous (fun p : ℝ × R2 => (F p.1).symm p.2) ∧
      (∀ a, F 0 a = a) ∧
      (∀ t ∈ Icc (0 : ℝ) T, ∀ a, HasDerivAt (fun s => F s a) (v t (F t a)) t) ∧
      ∀ t ∈ Icc (0 : ℝ) T, MeasurePreserving (F t) volume volume ∧
        MeasurePreserving (F t).symm volume volume := by
  obtain ⟨K, hK, _hs, hmod, hconv⟩ := exists_smoothBoundedLogVelocityApproximation hv hM hlog
  obtain ⟨F, hFc, hFic, hF0, hFd⟩ := exists_planarLogHomeomorphFlow_of_uniform_approximation hv
    (smoothBoundedLogVelocityApproximation v) K M C hK hmod hconv hT
  obtain ⟨S, hSarea⟩ := exists_measurePreserving_weakDivergence_logFlow hv hM hlog hdiv hT
  have heq (a : R2) : ∀ t ∈ Icc (0 : ℝ) T, F t a = S.forward t a :=
    logFlow_unique C.coe_nonneg
      (hFc.comp (continuous_id.prodMk continuous_const))
      (S.continuous_forward.comp (continuous_id.prodMk continuous_const))
      (fun t ht => hFd t ht a) (fun t ht => S.derivative t ht a)
      ((hF0 a).trans (S.initial a).symm) (fun t _ x y hxy => hlog t x y hxy)
  refine ⟨F, hFc, hFic, hF0, hFd, ?_⟩
  intro t ht
  have hm : MeasurePreserving (F t) volume volume := by
    have he : (F t : R2 → R2) = S.forward t := funext (fun a => heq a t ht)
    rw [he]
    exact (hSarea t ht).1
  exact ⟨hm, MeasurePreserving.symm (F t).toMeasurableEquiv hm⟩

theorem exists_complex_measurePreserving_logHomeomorphFlow
    {v : ℝ → ℂ → ℂ} {M C : ℝ≥0}
    (hv : Continuous (Function.uncurry v)) (hM : ∀ t z, ‖v t z‖ ≤ M)
    (hlog : ∀ t z w, ‖z - w‖ ≤ 1 / 2 → ‖v t z - v t w‖ ≤ C * logFlowModulus ‖z - w‖)
    (hdiv : ∀ t, IsPlanarWeaklyDivergenceFree (fun x : R2 =>
      complexPhysicalPlane (v t (complexPhysicalPlane.symm x)))) {T : ℝ} (hT : 0 ≤ T) :
    ∃ F : ℝ → ℂ ≃ₜ ℂ,
      Continuous (fun p : ℝ × ℂ => F p.1 p.2) ∧
      Continuous (fun p : ℝ × ℂ => (F p.1).symm p.2) ∧
      (∀ a, F 0 a = a) ∧
      (∀ t ∈ Icc (0 : ℝ) T, ∀ a, HasDerivAt (fun s => F s a) (v t (F t a)) t) ∧
      ∀ t ∈ Icc (0 : ℝ) T, MeasurePreserving (F t) volume volume ∧
        MeasurePreserving (F t).symm volume volume := by
  let vr : ℝ → R2 → R2 := fun t x => complexPhysicalPlane (v t (complexPhysicalPlane.symm x))
  have hvr : Continuous (Function.uncurry vr) := complexPhysicalPlane.continuous.comp
    (hv.comp (continuous_fst.prodMk (complexPhysicalPlane.symm.continuous.comp continuous_snd)))
  have hMr (t : ℝ) (x : R2) : ‖vr t x‖ ≤ M := by
    simpa only [vr, LinearIsometryEquiv.norm_map] using hM t (complexPhysicalPlane.symm x)
  have hlogr (t : ℝ) (x y : R2) (hxy : ‖x - y‖ ≤ 1 / 2) :
      ‖vr t x - vr t y‖ ≤ C * logFlowModulus ‖x - y‖ := by
    have hs : ‖complexPhysicalPlane.symm x - complexPhysicalPlane.symm y‖ ≤ 1 / 2 := by
      simpa only [← map_sub, LinearIsometryEquiv.norm_map] using hxy
    simpa only [vr, ← map_sub, LinearIsometryEquiv.norm_map] using
      hlog t (complexPhysicalPlane.symm x) (complexPhysicalPlane.symm y) hs
  obtain ⟨G, hGc, hGic, hG0, hGd, hGarea⟩ := exists_measurePreserving_logHomeomorphFlow hvr hMr hlogr hdiv hT
  let F : ℝ → ℂ ≃ₜ ℂ := fun t => complexPhysicalPlane.toHomeomorph.trans
    ((G t).trans complexPhysicalPlane.symm.toHomeomorph)
  have hFc : Continuous (fun p : ℝ × ℂ => F p.1 p.2) := complexPhysicalPlane.symm.continuous.comp
    (hGc.comp (continuous_fst.prodMk (complexPhysicalPlane.continuous.comp continuous_snd)))
  have hFic : Continuous (fun p : ℝ × ℂ => (F p.1).symm p.2) := complexPhysicalPlane.symm.continuous.comp
    (hGic.comp (continuous_fst.prodMk (complexPhysicalPlane.continuous.comp continuous_snd)))
  refine ⟨F, hFc, hFic, ?_, ?_, ?_⟩
  · intro a
    change complexPhysicalPlane.symm (G 0 (complexPhysicalPlane a)) = a
    rw [hG0, LinearIsometryEquiv.symm_apply_apply]
  · intro t ht a
    have hd := complexPhysicalPlane.symm.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt t
      (hGd t ht (complexPhysicalPlane a))
    change HasDerivAt (fun s => F s a)
      (complexPhysicalPlane.symm (complexPhysicalPlane (v t (F t a)))) t at hd
    simpa only [LinearIsometryEquiv.symm_apply_apply] using hd
  · intro t ht
    have hm : MeasurePreserving (F t) volume volume :=
      complexPhysicalPlane.symm.measurePreserving.comp ((hGarea t ht).1.comp complexPhysicalPlane.measurePreserving)
    exact ⟨hm, MeasurePreserving.symm (F t).toMeasurableEquiv hm⟩

end Euler2D

end
