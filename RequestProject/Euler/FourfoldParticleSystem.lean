module

public import RequestProject.Euler.FourfoldParticleSymmetry

/-! Genuine self-consistent particle systems whose fourfold symmetry is a conclusion. -/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal ContDiff BoundedContinuousFunction

namespace Euler2D

def smoothRegularizedParticleSystemOfDisplacement
    {K : R2 → R2} {w : R2 → ℝ} {L M : ℝ≥0}
    (hKC1 : ContDiff ℝ 1 K) (hK : LipschitzWith L K)
    (hM : ∀ x, ‖K x‖ ≤ M) (hKper : IsTorusPeriodic K)
    (hKdiv : ∀ x, pd 0 K x 0 + pd 1 K x 1 = 0) (hw : Integrable w μT)
    {T : ℝ} (hT : 0 ≤ T) (η : ℝ → ParticleDisplacement)
    (hη : Continuous η) (hη0 : η 0 = 0)
    (hηd : ∀ t ∈ Icc (0 : ℝ) T, HasDerivAt η
      (RegularizedParticleConstruction.displacementField hK hM hw (η t)) t) :
    SmoothRegularizedParticleSystem K w T L M := by
  let hv := boundedLipschitzVelocity_regularizedLabelVelocity hK hM hw hη
  have hODE (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) (a : R2) :
      HasDerivAt (fun s => a + η s a)
        (regularizedLabelVelocity K w (η t) (a + η t a)) t :=
    regularizedDisplacement_particle_derivative hK hM hw (hηd t ht) a
  have hC1 := isC1SpatialVelocity_regularizedLabelVelocity hKC1 hK hM hw hη
  have hper : ∀ t, IsTorusPeriodic (fun x => regularizedLabelVelocity K w (η t) x) :=
    fun t => isTorusPeriodic_regularizedLabelVelocity hKper w (η t)
  have hdiv : ∀ t x, pd 0 (regularizedLabelVelocity K w (η t)) x 0 +
      pd 1 (regularizedLabelVelocity K w (η t)) x 1 = 0 :=
    fun t x => divergence_regularizedLabelVelocity hKC1 hK hM hw hKdiv (η t) x
  exact {
    velocity := fun t x => regularizedLabelVelocity K w (η t) x
    forward := boundedParticleForward hv hT
    backward := boundedParticleBackward hv hT
    bounded := hv
    spatialC1 := hC1
    periodic := hper
    divergence_zero := hdiv
    forward_continuous := boundedParticleForward_continuous hv hT
    backward_continuous := boundedParticleBackward_continuous hv hT
    initial := boundedParticleForward_zero hv hT
    derivative := fun _ ht a => boundedParticleForward_hasDerivAt hv hT ht a
    forward_area := fun _ ht =>
      torusAreaPreserving_boundedParticleForward_of_spatialC1 hv hC1 hT hdiv hper ht
    backward_area := torusAreaPreserving_boundedParticleBackward_all_of_spatialC1
      hv hC1 hT hdiv hper
    forward_lattice := boundedParticleForward_lattice_equivariant hv hT hper
    backward_lattice := boundedParticleBackward_lattice_equivariant hv hT hper
    backward_forward := fun _ ht a => boundedParticleBackward_forward hv hT ht a
    forward_backward := fun _ ht a => boundedParticleForward_backward hv hT ht a
    pushForward := isVorticityPushForward_boundedParticleForward_of_spatialC1
      hv hC1 hT hdiv hper hw
    label_integral := by
      intro t ht x
      conv_lhs => unfold regularizedLabelVelocity
      apply integral_congr_ae
      filter_upwards with b
      rw [← regularizedDisplacement_eq_boundedParticleForward hη hη0 hv hT hODE ht b]
    transported_integral := fun _ ht x => regularizedLabelVelocity_eq_transported_integral
      hK hM hKper hw hη hη0 hv hC1 hT hdiv hODE ht x
  }

structure IsFourfoldParticleSystem {K : R2 → R2} {w : R2 → ℝ} {T : ℝ} {L M : ℝ≥0}
    (S : SmoothRegularizedParticleSystem K w T L M) : Prop where
  forward : ∀ t ∈ Icc (0 : ℝ) T, ∀ a,
    S.forward t (torusQuarterTurn a) = torusQuarterTurn (S.forward t a)
  backward : ∀ t ∈ Icc (0 : ℝ) T, ∀ a,
    S.backward t (torusQuarterTurn a) = torusQuarterTurn (S.backward t a)
  velocity : ∀ t ∈ Icc (0 : ℝ) T, ∀ x,
    S.velocity t (torusQuarterTurn x) = perpJ (S.velocity t x)

lemma eq_center_of_eq_torusQuarterTurn {x : R2} (hx : x = torusQuarterTurn x) :
    x = torusCenter := by
  have h0 := congrArg (fun z : R2 => z 0) hx
  have h1 := congrArg (fun z : R2 => z 1) hx
  change x 0 = torusQuarterTurn x 0 at h0
  change x 1 = torusQuarterTurn x 1 at h1
  rw [torusQuarterTurn_zero] at h0
  rw [torusQuarterTurn_one] at h1
  ext i
  fin_cases i
  · change x 0 = Real.pi
    linarith
  · change x 1 = Real.pi
    linarith

lemma eq_zero_of_eq_perpJ {x : R2} (hx : x = perpJ x) : x = 0 := by
  have h0 := congrArg (fun z : R2 => z 0) hx
  have h1 := congrArg (fun z : R2 => z 1) hx
  change x 0 = -x 1 at h0
  change x 1 = x 0 at h1
  ext i
  fin_cases i
  · change x 0 = 0
    linarith
  · change x 1 = 0
    linarith

namespace IsFourfoldParticleSystem

variable {K : R2 → R2} {w : R2 → ℝ} {T : ℝ} {L M : ℝ≥0}
  {S : SmoothRegularizedParticleSystem K w T L M} (hS : IsFourfoldParticleSystem S)

include hS

theorem forward_center {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    S.forward t torusCenter = torusCenter := by
  apply eq_center_of_eq_torusQuarterTurn
  simpa only [torusQuarterTurn_center] using hS.forward t ht torusCenter

theorem backward_center {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    S.backward t torusCenter = torusCenter := by
  apply eq_center_of_eq_torusQuarterTurn
  simpa only [torusQuarterTurn_center] using hS.backward t ht torusCenter

theorem velocity_center {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    S.velocity t torusCenter = 0 := by
  apply eq_zero_of_eq_perpJ
  simpa only [torusQuarterTurn_center] using hS.velocity t ht torusCenter

end IsFourfoldParticleSystem

theorem exists_smoothRegularizedParticleSystem_fourfold
    {K : R2 → R2} {w : R2 → ℝ} {L M : ℝ≥0}
    (hKC1 : ContDiff ℝ 1 K) (hK : LipschitzWith L K)
    (hM : ∀ x, ‖K x‖ ≤ M) (hKper : IsTorusPeriodic K)
    (hKdiv : ∀ x, pd 0 K x 0 + pd 1 K x 1 = 0)
    (hKrot : ∀ x, K (torusQuarterTurn x) = perpJ (K x))
    (hw : Integrable w μT) (hwper : IsTorusPeriodic w)
    (hwrot : ∀ x, w (torusQuarterTurn x) = w x)
    {T : ℝ} (hT : 0 ≤ T) :
    ∃ S : SmoothRegularizedParticleSystem K w T L M, IsFourfoldParticleSystem S := by
  obtain ⟨η, hη, hη0, hηd⟩ := exists_regularizedDisplacement_dynamics hK hM hw hT
  let S := smoothRegularizedParticleSystemOfDisplacement hKC1 hK hM hKper hKdiv hw hT η hη hη0 hηd
  let hv := boundedLipschitzVelocity_regularizedLabelVelocity hK hM hw hη
  have hODE (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) (a : R2) :
      HasDerivAt (fun s => a + η s a)
        (regularizedLabelVelocity K w (η t) (a + η t a)) t :=
    regularizedDisplacement_particle_derivative hK hM hw (hηd t ht) a
  have hsym := regularizedDisplacement_quarterTurn_of_dynamics
    hK hM hw hKper hKrot hwper hwrot hη hη0 hT hηd
  have hηsym (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) (a : R2) :
      η t (torusQuarterTurn a) = perpJ (η t a) := by
    have he := congrArg (fun ζ : ParticleDisplacement => ζ a) (hsym t ht)
    change -perpJ (η t (torusQuarterTurn a)) = η t a at he
    have hh := congrArg perpJ he
    rwa [perpJ_neg_perpJ_apply] at hh
  have hforward (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) (a : R2) :
      S.forward t (torusQuarterTurn a) = torusQuarterTurn (S.forward t a) := by
    dsimp only [S, smoothRegularizedParticleSystemOfDisplacement]
    change boundedParticleForward hv hT t (torusQuarterTurn a) =
      torusQuarterTurn (boundedParticleForward hv hT t a)
    rw [← regularizedDisplacement_eq_boundedParticleForward hη hη0 hv hT hODE ht (torusQuarterTurn a),
      ← regularizedDisplacement_eq_boundedParticleForward hη hη0 hv hT hODE ht a,
      torusQuarterTurn_add, hηsym t ht a]
  refine ⟨S, hforward, ?_, ?_⟩
  · intro t ht a
    have hinj : Function.Injective (S.forward t) :=
      Function.LeftInverse.injective (S.backward_forward t ht)
    apply hinj
    rw [S.forward_backward t ht, hforward t ht, S.forward_backward t ht]
  · intro t ht x
    have hηper : IsTorusPeriodic (η t : R2 → R2) :=
      regularizedDisplacement_isTorusPeriodic hKper hη hη0 hv hT hODE ht
    have he := regularizedLabelVelocity_quarterDisplacement
      hK hM hw hKper hKrot hwper hwrot (η t) hηper x
    rw [hsym t ht] at he
    have hh := congrArg perpJ he
    rw [perpJ_neg_perpJ_apply] at hh
    dsimp only [S, smoothRegularizedParticleSystemOfDisplacement]
    exact hh.symm

theorem exists_fourfoldRegularizedTorusParticleSystem_with_symmetry
    {w : R2 → ℝ} (hw : Integrable w μT) (hwper : IsTorusPeriodic w)
    (hwrot : ∀ x, w (torusQuarterTurn x) = w x)
    {T : ℝ} (hT : 0 ≤ T) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ C : ℝ≥0, ∃ S : SmoothRegularizedParticleSystem
      (fourfoldRegularizedTorusKernel ε hε) w T C C, IsFourfoldParticleSystem S := by
  obtain ⟨C, hM, _hD, hK⟩ := fourfoldRegularizedTorusKernel_bounds hε hε1
  exact ⟨C, exists_smoothRegularizedParticleSystem_fourfold
    ((fourfoldRegularizedTorusKernel_smooth hε hε1).of_le (by simp)) hK hM
    (fourfoldRegularizedTorusKernel_periodic ε hε)
    (fourfoldRegularizedTorusKernel_divergence hε hε1)
    (fourfoldRegularizedTorusKernel_quarterTurn hε hε1) hw hwper hwrot hT⟩

end Euler2D

end
