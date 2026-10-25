module

public import RequestProject.Euler.PlanarMaterialParticleUniqueness
public import RequestProject.Euler.TorusKernelSymmetry

/-! Quarter-turn symmetry of the actual whole-plane material particle
equation. Conjugation uses change of variables on all of physical space;
neither the kernel nor the density is assumed periodic. -/

@[expose] public section

set_option maxHeartbeats 2500000

noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal

namespace Euler2D

def torusQuarterTurnInverse (x : R2) : R2 :=
  torusCenter - perpJ (x - torusCenter)

@[simp] theorem torusQuarterTurn_inverse_apply (x : R2) :
    torusQuarterTurn (torusQuarterTurnInverse x) = x := by
  ext i
  fin_cases i <;> simp [torusQuarterTurn, torusQuarterTurnInverse, perpJ]

@[simp] theorem torusQuarterTurnInverse_apply (x : R2) :
    torusQuarterTurnInverse (torusQuarterTurn x) = x := by
  ext i
  fin_cases i <;> simp [torusQuarterTurn, torusQuarterTurnInverse, perpJ]

theorem continuous_torusQuarterTurnInverse : Continuous torusQuarterTurnInverse :=
  continuous_const.sub (perpJL.continuous.comp (continuous_id.sub continuous_const))

def torusQuarterTurnHomeomorph : R2 ≃ₜ R2 where
  toFun := torusQuarterTurn
  invFun := torusQuarterTurnInverse
  left_inv := torusQuarterTurnInverse_apply
  right_inv := torusQuarterTurn_inverse_apply
  continuous_toFun := torusQuarterTurn_smooth.continuous
  continuous_invFun := continuous_torusQuarterTurnInverse

theorem integral_comp_torusQuarterTurn_unconditional
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (f : R2 → F) :
    (∫ x, f (torusQuarterTurn x)) = ∫ x, f x :=
  measurePreserving_torusQuarterTurn.integral_comp
    torusQuarterTurnHomeomorph.measurableEmbedding f

theorem torusQuarterTurn_sub (x y : R2) :
    torusQuarterTurn x - torusQuarterTurn y = perpJ (x - y) := by
  ext i
  fin_cases i <;> simp [torusQuarterTurn, perpJ] <;> ring

theorem neg_perpJ_perpJ_identity (x : R2) : -perpJ (perpJ x) = x := by
  ext i
  fin_cases i <;> simp [perpJ]

theorem hasFDerivAt_torusQuarterTurnInverse (x : R2) :
    HasFDerivAt torusQuarterTurnInverse (-perpJL) x := by
  convert (((-perpJL).hasFDerivAt (x := x - torusCenter)).comp x
    ((hasFDerivAt_id x).sub_const torusCenter)).const_add torusCenter using 1

theorem planarMaterialLabelVelocity_quarterConjugate
    {K : R2 → R2} {w : R2 → ℝ}
    (hKrot : ∀ x, K (perpJ x) = perpJ (K x))
    (hwrot : ∀ x, w (torusQuarterTurn x) = w x) (X : R2 → R2) (x : R2) :
    planarMaterialLabelVelocity K w
      (fun a => torusQuarterTurnInverse (X (torusQuarterTurn a))) x =
      -perpJ (planarMaterialLabelVelocity K w X (torusQuarterTurn x)) := by
  have he : planarMaterialLabelVelocity K w X (torusQuarterTurn x) =
      perpJ (planarMaterialLabelVelocity K w
        (fun a => torusQuarterTurnInverse (X (torusQuarterTurn a))) x) := by
    unfold planarMaterialLabelVelocity
    rw [← integral_comp_torusQuarterTurn_unconditional]
    calc
      _ = ∫ b, perpJ (w b • K
          (x - torusQuarterTurnInverse (X (torusQuarterTurn b)))) := by
        apply integral_congr_ae
        exact ae_of_all _ (fun b => by
          dsimp only
          rw [hwrot b]
          have harg : torusQuarterTurn x - X (torusQuarterTurn b) =
              perpJ (x - torusQuarterTurnInverse (X (torusQuarterTurn b))) := by
            rw [← torusQuarterTurn_sub, torusQuarterTurn_inverse_apply]
          rw [harg, hKrot, perpJ_smul])
      _ = _ := perpJLinearIsometryEquiv.toLinearIsometry.integral_comp_comm _
  rw [he, neg_perpJ_perpJ_identity]

namespace PlanarMaterialParticleFlow

variable {K : R2 → R2} {w : R2 → ℝ} {T : ℝ}

def quarterConjugate (P : PlanarMaterialParticleFlow K w T)
    (hKrot : ∀ x, K (perpJ x) = perpJ (K x))
    (hwrot : ∀ x, w (torusQuarterTurn x) = w x) :
    PlanarMaterialParticleFlow K w T where
  velocity := fun t x => -perpJ (P.velocity t (torusQuarterTurn x))
  forward := fun t a => torusQuarterTurnInverse (P.forward t (torusQuarterTurn a))
  continuous_velocity := (-perpJL).continuous.comp (P.continuous_velocity.comp
    (continuous_fst.prodMk (torusQuarterTurn_smooth.continuous.comp continuous_snd)))
  continuous_forward := continuous_torusQuarterTurnInverse.comp (P.continuous_forward.comp
    (continuous_fst.prodMk (torusQuarterTurn_smooth.continuous.comp continuous_snd)))
  initial := fun a => by rw [P.initial, torusQuarterTurnInverse_apply]
  derivative := fun t ht a => by
    rw [torusQuarterTurn_inverse_apply]
    exact (hasFDerivAt_torusQuarterTurnInverse _).comp_hasDerivAt t
      (P.derivative t ht (torusQuarterTurn a))
  source_integral := fun t ht x => by
    rw [P.source_integral t ht]
    exact (planarMaterialLabelVelocity_quarterConjugate hKrot hwrot (P.forward t) x).symm

theorem forward_quarterTurn (P : PlanarMaterialParticleFlow K w T)
    {L M : ℝ≥0} (hw : Integrable w) (hK : LipschitzWith L K)
    (hM : ∀ x, ‖K x‖ ≤ M) (hKrot : ∀ x, K (perpJ x) = perpJ (K x))
    (hwrot : ∀ x, w (torusQuarterTurn x) = w x) (hT : 0 ≤ T)
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) (a : R2) :
    P.forward t (torusQuarterTurn a) = torusQuarterTurn (P.forward t a) := by
  have he := P.forward_eq (P.quarterConjugate hKrot hwrot) hw hK hM hT t ht a
  have hh := congrArg torusQuarterTurn he
  simpa only [quarterConjugate, torusQuarterTurn_inverse_apply] using hh.symm

end PlanarMaterialParticleFlow

namespace SmoothPlanarRegularizedParticleSystem

variable {K : R2 → R2} {w : R2 → ℝ} {T : ℝ} {L M : ℝ≥0}

theorem forward_quarterTurn (S : SmoothPlanarRegularizedParticleSystem K w T L M)
    {LK MK : ℝ≥0} (hw : Integrable w μT) (hK : LipschitzWith LK K)
    (hM : ∀ x, ‖K x‖ ≤ MK) (hKrot : ∀ x, K (perpJ x) = perpJ (K x))
    (hwrot : ∀ x, planarBoxSource w (torusQuarterTurn x) = planarBoxSource w x)
    (hT : 0 ≤ T) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) (a : R2) :
    S.particles.forward t (torusQuarterTurn a) = torusQuarterTurn (S.particles.forward t a) :=
  S.toMaterialFlow.forward_quarterTurn (integrable_planarBoxSource hw) hK hM hKrot hwrot hT t ht a

theorem backward_quarterTurn (S : SmoothPlanarRegularizedParticleSystem K w T L M)
    {LK MK : ℝ≥0} (hw : Integrable w μT) (hK : LipschitzWith LK K)
    (hM : ∀ x, ‖K x‖ ≤ MK) (hKrot : ∀ x, K (perpJ x) = perpJ (K x))
    (hwrot : ∀ x, planarBoxSource w (torusQuarterTurn x) = planarBoxSource w x)
    (hT : 0 ≤ T) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) (a : R2) :
    S.particles.backward t (torusQuarterTurn a) = torusQuarterTurn (S.particles.backward t a) := by
  have he := S.forward_quarterTurn hw hK hM hKrot hwrot hT t ht (S.particles.backward t a)
  rw [S.particles.right_inv t ht a] at he
  have hh := congrArg (S.particles.backward t) he
  rw [S.particles.left_inv t ht] at hh
  exact hh.symm

end SmoothPlanarRegularizedParticleSystem

end Euler2D

end
