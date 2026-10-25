module

public import RequestProject.Euler.RegularizedParticleSystem
public import RequestProject.Euler.PeriodicLogFlowCompactness

/-!
# The actual displacement-space equation, retained with its Banach derivative

This exposes the derivative already provided by Picard--Lindelöf, before
evaluating at a particle label.  Spatial periodicity is subsequently
derived from the genuine lifted particle flow.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal ContDiff BoundedContinuousFunction

namespace Euler2D

theorem exists_regularizedDisplacement_dynamics
    {K : R2 → R2} {w : R2 → ℝ} {L M : ℝ≥0}
    (hK : LipschitzWith L K) (hM : ∀ x, ‖K x‖ ≤ M) (hw : Integrable w μT)
    {T : ℝ} (hT : 0 ≤ T) :
    ∃ η : ℝ → ParticleDisplacement, Continuous η ∧ η 0 = 0 ∧
      ∀ t ∈ Icc (0 : ℝ) T, HasDerivAt η
        (RegularizedParticleConstruction.displacementField hK hM hw (η t)) t := by
  let F := RegularizedParticleConstruction.displacementField hK hM hw
  have hFL := RegularizedParticleConstruction.lipschitz_displacementField hK hM hw
  obtain ⟨η, hη, hη0, hηd⟩ := exists_boundedODE_continuous_curve
    (f := fun _ : ℝ => F) (K := 2 * L * particleLabelMass w) (M := M * particleLabelMass w)
    (hFL.continuous.comp continuous_snd) (fun _ => hFL)
    (fun _ ζ => by simpa only [NNReal.coe_mul] using
      RegularizedParticleConstruction.norm_displacementField_le hK hM hw ζ)
    hT (0 : ParticleDisplacement)
  refine ⟨η, hη, hη0, fun t ht => hηd t ?_⟩
  constructor <;> linarith [ht.1, ht.2]

theorem boundedLipschitzVelocity_regularizedLabelVelocity
    {K : R2 → R2} {w : R2 → ℝ} {L M : ℝ≥0}
    (hK : LipschitzWith L K) (hM : ∀ x, ‖K x‖ ≤ M) (hw : Integrable w μT)
    {η : ℝ → ParticleDisplacement} (hη : Continuous η) :
    IsBoundedLipschitzVelocity (fun t x => regularizedLabelVelocity K w (η t) x)
      (L * particleLabelMass w) (M * particleLabelMass w) := by
  refine ⟨?_, fun t => RegularizedParticleConstruction.lipschitz_labelVelocity hK hM hw (η t), ?_⟩
  · have hηfst : Continuous (fun p : ℝ × R2 => η p.1) := hη.comp continuous_fst
    have hpair : Continuous (fun p : ℝ × R2 => (η p.1, p.2)) := hηfst.prodMk continuous_snd
    have hvc : Continuous (fun p : ParticleDisplacement × R2 =>
        regularizedLabelVelocity K w p.1 p.2) :=
      (RegularizedParticleConstruction.lipschitz_joint_labelVelocity hK hM hw).continuous
    exact (hvc.comp hpair).congr (fun _ => rfl)
  · intro t x
    simpa only [NNReal.coe_mul] using
      RegularizedParticleConstruction.norm_labelVelocity_le hM hw (η t) x

theorem regularizedDisplacement_particle_derivative
    {K : R2 → R2} {w : R2 → ℝ} {L M : ℝ≥0}
    (hK : LipschitzWith L K) (hM : ∀ x, ‖K x‖ ≤ M) (hw : Integrable w μT)
    {η : ℝ → ParticleDisplacement} {t : ℝ}
    (hηd : HasDerivAt η
      (RegularizedParticleConstruction.displacementField hK hM hw (η t)) t) (a : R2) :
    HasDerivAt (fun s => a + η s a)
      (regularizedLabelVelocity K w (η t) (a + η t a)) t := by
  have hd := (BoundedContinuousFunction.evalCLM ℝ a).hasFDerivAt.comp_hasDerivAt t hηd
  exact hd.const_add a

theorem regularizedDisplacement_isTorusPeriodic
    {K : R2 → R2} {w : R2 → ℝ} {η : ℝ → ParticleDisplacement} {L M : ℝ≥0}
    (hKper : IsTorusPeriodic K) (hη : Continuous η) (hη0 : η 0 = 0)
    (hv : IsBoundedLipschitzVelocity (fun t x => regularizedLabelVelocity K w (η t) x) L M)
    {T : ℝ} (hT : 0 ≤ T)
    (hODE : ∀ t ∈ Icc (0 : ℝ) T, ∀ a : R2,
      HasDerivAt (fun s => a + η s a)
        (regularizedLabelVelocity K w (η t) (a + η t a)) t)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) : IsTorusPeriodic (η t : R2 → R2) := by
  have hper : ∀ s, IsTorusPeriodic (fun x => regularizedLabelVelocity K w (η s) x) :=
    fun s => isTorusPeriodic_regularizedLabelVelocity hKper w (η s)
  have hperiodic := isTorusPeriodic_flow_displacement
    (boundedParticleForward_lattice_equivariant hv hT hper t)
  have heq : (fun a => boundedParticleForward hv hT t a - a) = (η t : R2 → R2) := by
    funext a
    rw [← regularizedDisplacement_eq_boundedParticleForward hη hη0 hv hT hODE ht a]
    abel
  rwa [heq] at hperiodic

end Euler2D

end
