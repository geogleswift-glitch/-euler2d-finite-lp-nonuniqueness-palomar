module

public import RequestProject.Euler.SmoothParticleFlow

/-!
# Quantitative estimates for the actual finite-window particle flow

These estimates concern the selected, genuinely existing particle trajectories.
They provide the exponential spatial bound and the linearization error equation
needed to differentiate the flow with respect to its initial particle position.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology Metric
open scoped NNReal

namespace Euler2D

theorem boundedParticleFlow_dist_le {v : ℝ → R2 → R2} {K M : ℝ≥0}
    (hv : IsBoundedLipschitzVelocity v K M) {T : ℝ} (hT : 0 ≤ T)
    (s t : ParticleTime T) (a b : R2) :
    dist (boundedParticleFlow hv hT s t a) (boundedParticleFlow hv hT s t b) ≤
      dist a b * Real.exp ((K : ℝ) * |(t : ℝ) - s|) := by
  by_cases hst : (s : ℝ) ≤ t
  · have hd := dist_le_of_trajectories_ODE hv.lipschitz
      (boundedParticleFlow_continuous_time hv hT s a).continuousOn
      (fun u hu => (boundedParticleFlow_hasDerivAt hv hT s a
        (by constructor <;> linarith [s.2.1, t.2.2, hu.1, hu.2])).hasDerivWithinAt)
      (boundedParticleFlow_continuous_time hv hT s b).continuousOn
      (fun u hu => (boundedParticleFlow_hasDerivAt hv hT s b
        (by constructor <;> linarith [s.2.1, t.2.2, hu.1, hu.2])).hasDerivWithinAt)
      (by simpa only [boundedParticleFlow_initial] using le_refl (dist a b))
      (t : ℝ) ⟨hst, le_rfl⟩
    simpa only [abs_of_nonneg (sub_nonneg.mpr hst)] using hd
  · have hts : (t : ℝ) ≤ s := le_of_not_ge hst
    have hvel : ∀ u, LipschitzWith K (fun x => -v (-u) x) :=
      fun u => (hv.lipschitz (-u)).neg
    have hder (a : R2) (u : ℝ) (hu : u ∈ Ico (-(s : ℝ)) (-(t : ℝ))) :
        HasDerivAt (fun r => boundedParticleFlow hv hT s (-r) a)
          (-v (-u) (boundedParticleFlow hv hT s (-u) a)) u := by
      have hd := (boundedParticleFlow_hasDerivAt hv hT s a
        (t := -u) (by constructor <;> linarith [s.2.2, t.2.1, hu.1, hu.2])).scomp u
          (hasDerivAt_neg u)
      simpa only [Function.comp_def, neg_one_smul] using hd
    have hd := dist_le_of_trajectories_ODE hvel
      ((boundedParticleFlow_continuous_time hv hT s a).comp continuous_neg).continuousOn
      (fun u hu => (hder a u hu).hasDerivWithinAt)
      ((boundedParticleFlow_continuous_time hv hT s b).comp continuous_neg).continuousOn
      (fun u hu => (hder b u hu).hasDerivWithinAt)
      (a := -(s : ℝ)) (b := -(t : ℝ))
      (by simpa only [Function.comp_apply, neg_neg, boundedParticleFlow_initial]
        using le_refl (dist a b))
      (-(t : ℝ)) ⟨neg_le_neg hts, le_rfl⟩
    simpa only [Function.comp_apply, neg_neg, neg_sub_neg,
      abs_of_nonpos (sub_nonpos.mpr hts), neg_sub] using hd

theorem boundedParticleFlow_lipschitz_space {v : ℝ → R2 → R2} {K M : ℝ≥0}
    (hv : IsBoundedLipschitzVelocity v K M) {T : ℝ} (hT : 0 ≤ T)
    (s t : ParticleTime T) :
    LipschitzWith ⟨Real.exp ((K : ℝ) * |(t : ℝ) - s|), (Real.exp_pos _).le⟩
      (boundedParticleFlow hv hT s t) := by
  apply LipschitzWith.of_dist_le_mul
  intro a b
  change dist (boundedParticleFlow hv hT s t a) (boundedParticleFlow hv hT s t b) ≤
    Real.exp ((K : ℝ) * |(t : ℝ) - s|) * dist a b
  simpa only [mul_comm] using boundedParticleFlow_dist_le hv hT s t a b

theorem boundedParticleFlow_dist_lower_le {v : ℝ → R2 → R2} {K M : ℝ≥0}
    (hv : IsBoundedLipschitzVelocity v K M) {T : ℝ} (hT : 0 ≤ T)
    (s t : ParticleTime T) (a b : R2) :
    dist a b ≤ dist (boundedParticleFlow hv hT s t a) (boundedParticleFlow hv hT s t b) *
      Real.exp ((K : ℝ) * |(t : ℝ) - s|) := by
  have hd := boundedParticleFlow_dist_le hv hT t s
    (boundedParticleFlow hv hT s t a) (boundedParticleFlow hv hT s t b)
  simpa only [boundedParticleFlow_inverse, abs_sub_comm] using hd

def particleDisplacement {v : ℝ → R2 → R2} {K M : ℝ≥0}
    (hv : IsBoundedLipschitzVelocity v K M) {T : ℝ} (hT : 0 ≤ T)
    (s : ParticleTime T) (a h : R2) (t : ℝ) : R2 :=
  boundedParticleFlow hv hT s t (a + h) - boundedParticleFlow hv hT s t a

def flowVelocityRemainder {v : ℝ → R2 → R2} {K M : ℝ≥0}
    (hv : IsBoundedLipschitzVelocity v K M) {T : ℝ} (hT : 0 ≤ T)
    (s : ParticleTime T) (a h : R2) (B : ℝ → R2 →L[ℝ] R2) (t : ℝ) : R2 :=
  v t (boundedParticleFlow hv hT s t (a + h)) - v t (boundedParticleFlow hv hT s t a) -
    B t (particleDisplacement hv hT s a h t)

def flowLinearizationError {v : ℝ → R2 → R2} {K M : ℝ≥0}
    (hv : IsBoundedLipschitzVelocity v K M) {T : ℝ} (hT : 0 ≤ T)
    (s : ParticleTime T) (a h : R2) (A : ℝ → R2 →L[ℝ] R2) (t : ℝ) : R2 :=
  particleDisplacement hv hT s a h t - A t h

theorem flowLinearizationError_hasDerivAt {v : ℝ → R2 → R2} {K M : ℝ≥0}
    (hv : IsBoundedLipschitzVelocity v K M) {T : ℝ} (hT : 0 ≤ T)
    (s : ParticleTime T) (a h : R2) {A B : ℝ → R2 →L[ℝ] R2}
    {t : ℝ} (ht : t ∈ Ioo (-1 : ℝ) (T + 1))
    (hA : HasDerivAt A ((B t).comp (A t)) t) :
    HasDerivAt (flowLinearizationError hv hT s a h A)
      (B t (flowLinearizationError hv hT s a h A t) +
        flowVelocityRemainder hv hT s a h B t) t := by
  have hd := (boundedParticleFlow_hasDerivAt hv hT s (a + h) ht).sub
    (boundedParticleFlow_hasDerivAt hv hT s a ht)
  have hAh := hA.clm_apply (hasDerivAt_const t h)
  simp only [ContinuousLinearMap.comp_apply, map_zero, add_zero] at hAh
  convert hd.sub hAh using 1 <;>
    (try funext r) <;>
    (try simp only [flowLinearizationError, flowVelocityRemainder, particleDisplacement,
      Pi.sub_def, map_sub]) <;> abel

/-- A uniform Taylor-remainder bound controls the actual spatial
linearization error by the inhomogeneous Grönwall bound. -/
theorem norm_flowLinearizationError_le {v : ℝ → R2 → R2} {K M : ℝ≥0}
    (hv : IsBoundedLipschitzVelocity v K M) {T : ℝ} (hT : 0 ≤ T)
    (s t : ParticleTime T) (hst : (s : ℝ) ≤ t) (a h : R2)
    {A B : ℝ → R2 →L[ℝ] R2} (hAc : Continuous A)
    (hA0 : A s = ContinuousLinearMap.id ℝ R2)
    (hAd : ∀ u ∈ Ico (s : ℝ) (t : ℝ), HasDerivAt A ((B u).comp (A u)) u)
    (hB : ∀ u ∈ Ico (s : ℝ) (t : ℝ), ‖B u‖ ≤ K)
    {ε : ℝ} (hrem : ∀ u ∈ Ico (s : ℝ) (t : ℝ),
      ‖flowVelocityRemainder hv hT s a h B u‖ ≤ ε) :
    ‖flowLinearizationError hv hT s a h A t‖ ≤ gronwallBound 0 K ε ((t : ℝ) - s) := by
  have he : Continuous (flowLinearizationError hv hT s a h A) :=
    ((boundedParticleFlow_continuous_time hv hT s (a + h)).sub
      (boundedParticleFlow_continuous_time hv hT s a)).sub (hAc.clm_apply continuous_const)
  have he0 : flowLinearizationError hv hT s a h A s = 0 := by
    simp only [flowLinearizationError, particleDisplacement, boundedParticleFlow_initial,
      hA0, ContinuousLinearMap.id_apply, add_sub_cancel_left, sub_self]
  apply norm_le_gronwallBound_of_norm_deriv_right_le he.continuousOn
    (fun u hu => (flowLinearizationError_hasDerivAt hv hT s a h
      (by constructor <;> linarith [s.2.1, t.2.2, hu.1, hu.2]) (hAd u hu)).hasDerivWithinAt)
    (by simp only [he0, norm_zero, le_refl]) ?_ (t : ℝ) ⟨hst, le_rfl⟩
  intro u hu
  calc
    ‖B u (flowLinearizationError hv hT s a h A u) + flowVelocityRemainder hv hT s a h B u‖ ≤
        ‖B u (flowLinearizationError hv hT s a h A u)‖ +
          ‖flowVelocityRemainder hv hT s a h B u‖ := norm_add_le _ _
    _ ≤ ‖B u‖ * ‖flowLinearizationError hv hT s a h A u‖ + ε :=
      add_le_add ((B u).le_opNorm _) (hrem u hu)
    _ ≤ _ := by gcongr; exact hB u hu

lemma norm_spatialVelocityDerivative_le {v : ℝ → R2 → R2} {K M : ℝ≥0}
    (hv : IsBoundedLipschitzVelocity v K M) (t : ℝ) (x : R2) :
    ‖fderiv ℝ (v t) x‖ ≤ K := norm_fderiv_le_of_lipschitz ℝ (hv.lipschitz t)

end Euler2D

end
