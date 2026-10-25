module

public import RequestProject.Euler.SmoothFlowVariational
public import RequestProject.Euler.TorusTransport

/-!
# Actual self-consistent particle dynamics for bounded Lipschitz kernels

The particle displacement is a curve in the Banach space of bounded
continuous functions on the covering plane.  Its vector field is the
actual weighted label integral.  Global bounds and a Lipschitz estimate
give a genuine Picard--Lindelöf construction on every finite time window.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal ContDiff BoundedContinuousFunction

namespace Euler2D

abbrev ParticleDisplacement := R2 →ᵇ R2

/-- The actual absolute mass of the fixed signed initial density. -/
def particleLabelMass (w : R2 → ℝ) : ℝ≥0 :=
  ⟨∫ b, ‖w b‖ ∂μT, integral_nonneg (fun _ => norm_nonneg _)⟩

/-- The velocity induced by the current particle positions, integrated
against the fixed initial labels. -/
def regularizedLabelVelocity (K : R2 → R2) (w : R2 → ℝ)
    (η : ParticleDisplacement) (x : R2) : R2 :=
  ∫ b, w b • K (x - (b + η b) + torusCenter) ∂μT

lemma isTorusPeriodic_regularizedLabelVelocity {K : R2 → R2} (hK : IsTorusPeriodic K)
    (w : R2 → ℝ) (η : ParticleDisplacement) :
    IsTorusPeriodic (regularizedLabelVelocity K w η) := by
  intro x i
  apply integral_congr_ae
  filter_upwards with b
  have he : x + EuclideanSpace.single i (2 * Real.pi) - (b + η b) + torusCenter =
      (x - (b + η b) + torusCenter) + EuclideanSpace.single i (2 * Real.pi) := by abel
  rw [he, hK]

namespace RegularizedParticleConstruction

variable {K : R2 → R2} {w : R2 → ℝ} {L M : ℝ≥0}
    (hK : LipschitzWith L K) (hM : ∀ x, ‖K x‖ ≤ M) (hw : Integrable w μT)

include hK hM hw

lemma integrable_label_integrand (η : ParticleDisplacement) (x : R2) :
    Integrable (fun b => w b • K (x - (b + η b) + torusCenter)) μT := by
  apply (hw.norm.const_mul (M : ℝ)).mono'
  · exact hw.aestronglyMeasurable.smul
      (hK.continuous.comp (continuous_const.sub (continuous_id.add η.continuous) |>.add
        continuous_const)).aestronglyMeasurable
  · filter_upwards with b
    rw [norm_smul]
    calc
      ‖w b‖ * ‖K (x - (b + η b) + torusCenter)‖ ≤ ‖w b‖ * M :=
        mul_le_mul_of_nonneg_left (hM _) (norm_nonneg _)
      _ = (M : ℝ) * ‖w b‖ := mul_comm _ _

omit hK in
lemma norm_labelVelocity_le (η : ParticleDisplacement) (x : R2) :
    ‖regularizedLabelVelocity K w η x‖ ≤ (M : ℝ) * particleLabelMass w := by
  unfold regularizedLabelVelocity
  calc
    _ ≤ ∫ b, (M : ℝ) * ‖w b‖ ∂μT :=
      norm_integral_le_of_norm_le (hw.norm.const_mul _)
        (Eventually.of_forall fun b => by
          rw [norm_smul, mul_comm (M : ℝ)]
          exact mul_le_mul_of_nonneg_left (hM _) (norm_nonneg _))
    _ = _ := integral_const_mul _ _

lemma norm_labelVelocity_sub_le (η ξ : ParticleDisplacement) (x y : R2) :
    ‖regularizedLabelVelocity K w η x - regularizedLabelVelocity K w ξ y‖ ≤
      (L : ℝ) * particleLabelMass w * (dist x y + dist η ξ) := by
  rw [regularizedLabelVelocity, regularizedLabelVelocity,
    ← integral_sub (integrable_label_integrand hK hM hw η x)
      (integrable_label_integrand hK hM hw ξ y)]
  calc
    _ ≤ ∫ b, ((L : ℝ) * (dist x y + dist η ξ)) * ‖w b‖ ∂μT := by
      apply norm_integral_le_of_norm_le (hw.norm.const_mul _)
      filter_upwards with b
      rw [← smul_sub, norm_smul]
      have ha : dist (x - (b + η b) + torusCenter) (y - (b + ξ b) + torusCenter) ≤
          dist x y + dist η ξ := by
        rw [dist_eq_norm]
        have he : x - (b + η b) + torusCenter - (y - (b + ξ b) + torusCenter) =
            (x - y) - (η b - ξ b) := by abel
        rw [he]
        exact (norm_sub_le _ _).trans (by
          simpa only [dist_eq_norm] using
            add_le_add (le_refl ‖x - y‖)
              (BoundedContinuousFunction.dist_coe_le_dist (f := η) (g := ξ) b))
      have hb := (hK.dist_le_mul _ _).trans (mul_le_mul_of_nonneg_left ha L.2)
      calc
        _ ≤ ‖w b‖ * ((L : ℝ) * (dist x y + dist η ξ)) :=
          mul_le_mul_of_nonneg_left (by simpa only [dist_eq_norm] using hb) (norm_nonneg _)
        _ = _ := mul_comm _ _
    _ = _ := by simp only [integral_const_mul, particleLabelMass, NNReal.coe_mk]; ring

lemma lipschitz_labelVelocity (η : ParticleDisplacement) :
    LipschitzWith (L * particleLabelMass w) (regularizedLabelVelocity K w η) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simpa only [dist_self, add_zero, NNReal.coe_mul, dist_eq_norm] using
    norm_labelVelocity_sub_le hK hM hw η η x y

/-- The actual nonlinear displacement vector field, as an element of
the bounded continuous function space. -/
def displacementField (η : ParticleDisplacement) : ParticleDisplacement :=
  BoundedContinuousFunction.mkOfBound
    ⟨fun a => regularizedLabelVelocity K w η (a + η a),
      (lipschitz_labelVelocity hK hM hw η).continuous.comp
        (continuous_id.add η.continuous)⟩
    (2 * ((M : ℝ) * particleLabelMass w))
    (BoundedContinuousFunction.dist_le_two_norm' (fun a => norm_labelVelocity_le hM hw η (a + η a)))

lemma norm_displacementField_le (η : ParticleDisplacement) :
    ‖displacementField hK hM hw η‖ ≤ (M : ℝ) * particleLabelMass w :=
  (BoundedContinuousFunction.norm_le (by positivity)).mpr
    (fun a => norm_labelVelocity_le hM hw η (a + η a))

lemma lipschitz_displacementField :
    LipschitzWith (2 * L * particleLabelMass w) (displacementField hK hM hw) := by
  apply LipschitzWith.of_dist_le_mul
  intro η ξ
  apply (BoundedContinuousFunction.dist_le (by positivity)).mpr
  intro a
  change ‖regularizedLabelVelocity K w η (a + η a) -
    regularizedLabelVelocity K w ξ (a + ξ a)‖ ≤ _
  calc
    _ ≤ (L : ℝ) * particleLabelMass w * (dist (a + η a) (a + ξ a) + dist η ξ) :=
      norm_labelVelocity_sub_le hK hM hw η ξ _ _
    _ ≤ (L : ℝ) * particleLabelMass w * (dist η ξ + dist η ξ) := by
      gcongr
      simpa only [dist_add_left] using BoundedContinuousFunction.dist_coe_le_dist (f := η) (g := ξ) a
    _ = _ := by simp only [NNReal.coe_mul, NNReal.coe_ofNat]; ring

lemma lipschitz_joint_labelVelocity :
    LipschitzWith (2 * L * particleLabelMass w)
      (fun p : ParticleDisplacement × R2 => regularizedLabelVelocity K w p.1 p.2) := by
  apply LipschitzWith.of_dist_le_mul
  intro p q
  rw [dist_eq_norm]
  calc
    _ ≤ (L : ℝ) * particleLabelMass w * (dist p.2 q.2 + dist p.1 q.1) :=
      norm_labelVelocity_sub_le hK hM hw _ _ _ _
    _ ≤ (L : ℝ) * particleLabelMass w * (dist p q + dist p q) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact add_le_add (by rw [Prod.dist_eq]; exact le_max_right _ _)
        (by rw [Prod.dist_eq]; exact le_max_left _ _)
    _ = _ := by simp only [NNReal.coe_mul, NNReal.coe_ofNat]; ring

end RegularizedParticleConstruction

set_option maxHeartbeats 400000 in
/-- Picard--Lindelöf constructs a genuine self-consistent label flow on
every finite window.  Both its driving velocity and its particle ODE
are the explicit weighted kernel integrals. -/
theorem exists_regularizedParticle_system {K : R2 → R2} {w : R2 → ℝ} {L M : ℝ≥0}
    (hK : LipschitzWith L K) (hM : ∀ x, ‖K x‖ ≤ M) (hw : Integrable w μT)
    {T : ℝ} (hT : 0 ≤ T) :
    ∃ η : ℝ → ParticleDisplacement,
      Continuous η ∧ η 0 = 0 ∧
      IsBoundedLipschitzVelocity
        (fun t x => regularizedLabelVelocity K w (η t) x)
        (L * particleLabelMass w) (M * particleLabelMass w) ∧
      Continuous (fun p : ℝ × R2 => p.2 + η p.1 p.2) ∧
      ∀ t ∈ Icc (0 : ℝ) T, ∀ a : R2,
        HasDerivAt (fun s => a + η s a)
          (regularizedLabelVelocity K w (η t) (a + η t a)) t := by
  let F : ParticleDisplacement → ParticleDisplacement :=
    RegularizedParticleConstruction.displacementField hK hM hw
  have hFL := RegularizedParticleConstruction.lipschitz_displacementField hK hM hw
  have hFc : Continuous (Function.uncurry (fun _ : ℝ => F)) :=
    hFL.continuous.comp continuous_snd
  obtain ⟨η, hη, hη0, hηd⟩ := exists_boundedODE_continuous_curve
    (f := fun _ : ℝ => F) (K := 2 * L * particleLabelMass w) (M := M * particleLabelMass w)
    hFc
    (fun _ => hFL)
    (fun _ ζ => by simpa only [NNReal.coe_mul] using
      RegularizedParticleConstruction.norm_displacementField_le hK hM hw ζ)
    hT (0 : ParticleDisplacement)
  refine ⟨η, hη, hη0, ?_, ?_, ?_⟩
  · refine ⟨?_, fun t => RegularizedParticleConstruction.lipschitz_labelVelocity hK hM hw (η t), ?_⟩
    · have hηfst : Continuous (fun p : ℝ × R2 => η p.1) := hη.comp continuous_fst
      have hpair : Continuous (fun p : ℝ × R2 => (η p.1, p.2)) :=
        hηfst.prodMk continuous_snd
      have hvc : Continuous (fun p : ParticleDisplacement × R2 =>
          regularizedLabelVelocity K w p.1 p.2) :=
        (RegularizedParticleConstruction.lipschitz_joint_labelVelocity hK hM hw).continuous
      exact (hvc.comp hpair).congr (fun _ => rfl)
    · intro t x
      simpa only [NNReal.coe_mul] using
        RegularizedParticleConstruction.norm_labelVelocity_le hM hw (η t) x
  · have hηfst : Continuous (fun p : ℝ × R2 => η p.1) := hη.comp continuous_fst
    exact continuous_snd.add (hηfst.eval continuous_snd)
  · intro t ht a
    have hd := (BoundedContinuousFunction.evalCLM ℝ a).hasFDerivAt.comp_hasDerivAt t
      (hηd t (by constructor <;> linarith [ht.1, ht.2]))
    exact hd.const_add a

end Euler2D

end
