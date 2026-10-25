module

public import RequestProject.Euler.RegularizedDisplacementDynamics
public import RequestProject.Euler.FourfoldKernelSymmetry
public import RequestProject.Euler.FourfoldRegularizedParticleSystem

/-!
# Fourfold symmetry of genuine self-consistent particle systems

The displacement-space equation is conjugated by a bounded linear
operator.  The actual torus change of variables proves covariance of
its nonlinear vector field, and Banach-space ODE uniqueness retains
the symmetry from the zero initial displacement.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal ContDiff BoundedContinuousFunction

namespace Euler2D

def quarterTurnDisplacementPrecomp : ParticleDisplacement →L[ℝ] ParticleDisplacement :=
  LinearMap.mkContinuous
    { toFun := fun η => η.compContinuous ⟨torusQuarterTurn, torusQuarterTurn_smooth.continuous⟩
      map_add' := by intro η ξ; ext a; rfl
      map_smul' := by intro c η; ext a; rfl }
    1 (fun η => by
      simpa only [one_mul] using BoundedContinuousFunction.norm_compContinuous_le η
        ⟨torusQuarterTurn, torusQuarterTurn_smooth.continuous⟩)

/-- The actual pullback of a displacement by the inverse value rotation. -/
def quarterTurnDisplacement : ParticleDisplacement →L[ℝ] ParticleDisplacement :=
  ((-perpJL).compLeftContinuousBounded R2).comp quarterTurnDisplacementPrecomp

@[simp] lemma quarterTurnDisplacement_apply (η : ParticleDisplacement) (a : R2) :
    quarterTurnDisplacement η a = -perpJ (η (torusQuarterTurn a)) := rfl

lemma perpJ_neg_perpJ_apply (x : R2) : perpJ (-perpJ x) = x := by
  ext i
  fin_cases i <;> simp [perpJ]

lemma neg_perpJ_perpJ_apply (x : R2) : -perpJ (perpJ x) = x := by
  rw [← perpJ_neg]
  exact perpJ_neg_perpJ_apply x

lemma perpJ_quarterTurnDisplacement (η : ParticleDisplacement) (a : R2) :
    perpJ (quarterTurnDisplacement η a) = η (torusQuarterTurn a) := by
  rw [quarterTurnDisplacement_apply, perpJ_neg_perpJ_apply]

theorem regularizedLabelVelocity_quarterDisplacement
    {K : R2 → R2} {w : R2 → ℝ} {L M : ℝ≥0}
    (hK : LipschitzWith L K) (hM : ∀ x, ‖K x‖ ≤ M) (hw : Integrable w μT)
    (hKper : IsTorusPeriodic K) (hKrot : ∀ x, K (torusQuarterTurn x) = perpJ (K x))
    (hwper : IsTorusPeriodic w) (hwrot : ∀ x, w (torusQuarterTurn x) = w x)
    (η : ParticleDisplacement) (hηper : IsTorusPeriodic (η : R2 → R2)) (x : R2) :
    regularizedLabelVelocity K w (quarterTurnDisplacement η) x =
      -perpJ (regularizedLabelVelocity K w η (torusQuarterTurn x)) := by
  let H : R2 → R2 := fun b =>
    w b • K (torusQuarterTurn x - (b + η b) + torusCenter)
  have hHi : Integrable H μT :=
    RegularizedParticleConstruction.integrable_label_integrand hK hM hw η _
  have hHper : IsTorusPeriodic H := by
    intro b i
    dsimp only [H]
    rw [hwper b i, hηper b i]
    congr 1
    have he : torusQuarterTurn x - (b + EuclideanSpace.single i (2 * Real.pi) + η b) +
        torusCenter + EuclideanSpace.single i (2 * Real.pi) =
      torusQuarterTurn x - (b + η b) + torusCenter := by abel
    have hp := hKper (torusQuarterTurn x -
      (b + EuclideanSpace.single i (2 * Real.pi) + η b) + torusCenter) i
    rw [he] at hp
    exact hp.symm
  have hchange := torusAreaPreserving_torusQuarterTurn.integral_comp hHi.aestronglyMeasurable hHper
  have hvrot : regularizedLabelVelocity K w η (torusQuarterTurn x) =
      perpJ (regularizedLabelVelocity K w (quarterTurnDisplacement η) x) := by
    calc
      _ = ∫ b in torusBox, H b := rfl
      _ = ∫ b in torusBox, H (torusQuarterTurn b) := hchange.symm
      _ = ∫ b in torusBox, perpJ (w b • K (x - (b + quarterTurnDisplacement η b) + torusCenter)) := by
        apply integral_congr_ae
        filter_upwards with b
        dsimp only [H]
        have he : torusQuarterTurn (b + quarterTurnDisplacement η b) =
            torusQuarterTurn b + η (torusQuarterTurn b) := by
          rw [torusQuarterTurn_add, perpJ_quarterTurnDisplacement]
        rw [hwrot b, ← he, torusQuarterTurn_kernel_argument, hKrot, perpJ_smul]
      _ = _ := perpJL.integral_comp_comm
        (RegularizedParticleConstruction.integrable_label_integrand hK hM hw
          (quarterTurnDisplacement η) x)
  rw [hvrot, neg_perpJ_perpJ_apply]

theorem displacementField_quarterDisplacement
    {K : R2 → R2} {w : R2 → ℝ} {L M : ℝ≥0}
    (hK : LipschitzWith L K) (hM : ∀ x, ‖K x‖ ≤ M) (hw : Integrable w μT)
    (hKper : IsTorusPeriodic K) (hKrot : ∀ x, K (torusQuarterTurn x) = perpJ (K x))
    (hwper : IsTorusPeriodic w) (hwrot : ∀ x, w (torusQuarterTurn x) = w x)
    (η : ParticleDisplacement) (hηper : IsTorusPeriodic (η : R2 → R2)) :
    RegularizedParticleConstruction.displacementField hK hM hw (quarterTurnDisplacement η) =
      quarterTurnDisplacement (RegularizedParticleConstruction.displacementField hK hM hw η) := by
  apply BoundedContinuousFunction.ext
  intro a
  change regularizedLabelVelocity K w (quarterTurnDisplacement η) (a + quarterTurnDisplacement η a) =
    -perpJ (regularizedLabelVelocity K w η (torusQuarterTurn a + η (torusQuarterTurn a)))
  rw [regularizedLabelVelocity_quarterDisplacement hK hM hw hKper hKrot hwper hwrot η hηper,
    torusQuarterTurn_add, perpJ_quarterTurnDisplacement]

theorem regularizedDisplacement_quarterTurn_of_dynamics
    {K : R2 → R2} {w : R2 → ℝ} {L M : ℝ≥0}
    (hK : LipschitzWith L K) (hM : ∀ x, ‖K x‖ ≤ M) (hw : Integrable w μT)
    (hKper : IsTorusPeriodic K) (hKrot : ∀ x, K (torusQuarterTurn x) = perpJ (K x))
    (hwper : IsTorusPeriodic w) (hwrot : ∀ x, w (torusQuarterTurn x) = w x)
    {η : ℝ → ParticleDisplacement} (hη : Continuous η) (hη0 : η 0 = 0)
    {T : ℝ} (hT : 0 ≤ T)
    (hηd : ∀ t ∈ Icc (0 : ℝ) T, HasDerivAt η
      (RegularizedParticleConstruction.displacementField hK hM hw (η t)) t) :
    ∀ t ∈ Icc (0 : ℝ) T, quarterTurnDisplacement (η t) = η t := by
  let F := RegularizedParticleConstruction.displacementField hK hM hw
  let hv := boundedLipschitzVelocity_regularizedLabelVelocity hK hM hw hη
  have hODE (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) (a : R2) :
      HasDerivAt (fun s => a + η s a)
        (regularizedLabelVelocity K w (η t) (a + η t a)) t :=
    regularizedDisplacement_particle_derivative hK hM hw (hηd t ht) a
  have hperiodic (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) : IsTorusPeriodic (η t : R2 → R2) :=
    regularizedDisplacement_isTorusPeriodic hKper hη hη0 hv hT hODE ht
  let ζ : ℝ → ParticleDisplacement := fun t => quarterTurnDisplacement (η t)
  have hζc : Continuous ζ := quarterTurnDisplacement.continuous.comp hη
  have hζd (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) : HasDerivAt ζ (F (ζ t)) t := by
    change HasDerivAt (fun s => quarterTurnDisplacement (η s)) (F (quarterTurnDisplacement (η t))) t
    have he : F (quarterTurnDisplacement (η t)) = quarterTurnDisplacement (F (η t)) :=
      displacementField_quarterDisplacement hK hM hw hKper hKrot hwper hwrot (η t) (hperiodic t ht)
    rw [he]
    exact quarterTurnDisplacement.hasFDerivAt.comp_hasDerivAt t (hηd t ht)
  have hFL := RegularizedParticleConstruction.lipschitz_displacementField hK hM hw
  have heq : EqOn η ζ (Icc (0 : ℝ) T) :=
    ODE_solution_unique_of_mem_Icc_right (v := fun _ : ℝ => F) (s := fun _ => univ)
      (fun _ _ => hFL.lipschitzOnWith)
      hη.continuousOn (fun t ht => (hηd t ⟨ht.1, ht.2.le⟩).hasDerivWithinAt)
      (fun _ _ => trivial)
      hζc.continuousOn (fun t ht => (hζd t ⟨ht.1, ht.2.le⟩).hasDerivWithinAt)
      (fun _ _ => trivial) (by simp only [ζ, hη0, map_zero])
  intro t ht
  exact (heq ht).symm

end Euler2D

end
