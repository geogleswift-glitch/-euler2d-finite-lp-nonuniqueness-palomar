module

public import RequestProject.Euler.CircularMaterialGrowingEquation
public import RequestProject.Euler.CircularFieldQuadraticRemainder

/-! A genuine scalar growing equation for an actual forced nonlinear
contour curve. The error is derived from the original field and has
the proved quadratic bound, uniformly along the circular orbit. -/

@[expose] public section

set_option maxHeartbeats 18000000
set_option maxRecDepth 7500

noncomputable section

open Complex Set
open scoped NNReal ContDiff

namespace Euler2D

local instance (priority := 2000) nonlinearGrowingLittle_group (γ : ℝ≥0) :
    NormedAddCommGroup (LittleContourSpace γ) := Submodule.normedAddCommGroup (LittleContourSpace γ)
local instance (priority := 2000) nonlinearGrowingLittle_space (γ : ℝ≥0) :
    NormedSpace ℝ (LittleContourSpace γ) := Submodule.normedSpace (LittleContourSpace γ)
local instance nonlinearGrowingReal_tower (γ : ℝ≥0) :
    IsScalarTower ℝ ℝ (Fin 2 → LittleContourSpace γ) where
  smul_assoc a b Z := (smul_smul a b Z).symm

theorem exists_circularNonlinear_growing_equation {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1) :
    ∃ C > 0, ∃ r > 0, ∀ (a : ℝ) (y : ℝ → Fin 2 → LittleContourSpace γ)
      (p : Fin 2 → LittleContourSpace γ) (t : ℝ),
      HasDerivAt y (a • circularBanachField hγ hγ1 (y t) + p) t →
      ‖y t - littleCircularMaterialContours hγ hγ1 (a * t)‖ ≤ r →
      let S := fun u => contourParameterShiftFamilyCLM (ι := Fin 2) γ
        (fun i => (-a * circularContourAngularVelocities i) * u)
      let W := fun u => circularUnstableCoordinateCLM γ
        (S u (y u - littleCircularMaterialContours hγ hγ1 (a * u)))
      ∃ E : ℂ,
        ‖E‖ ≤ |a| * ‖circularUnstableCoordinateCLM γ‖ * C *
          ‖y t - littleCircularMaterialContours hγ hγ1 (a * t)‖ ^ 2 ∧
        HasDerivAt W ((a : ℂ) * lamStar * W t + circularUnstableCoordinateCLM γ (S t p) + E) t := by
  obtain ⟨C, hC, r, hr, hquad⟩ := exists_circularField_uniform_quadratic_remainder hγ hγ1
  refine ⟨C, hC, r, hr, ?_⟩
  intro a y p t hy hsmall
  dsimp only
  let H := fun u => y u - littleCircularMaterialContours hγ hγ1 (a * u)
  let F := circularBanachField hγ hγ1
  let z := littleCircularMaterialContours hγ hγ1 (a * t)
  let R := F (y t) - F z - fderiv ℝ F z (H t)
  let S := fun u => contourParameterShiftFamilyCLM (ι := Fin 2) γ
    (fun i => (-a * circularContourAngularVelocities i) * u)
  let E : ℂ := (a : ℂ) * circularUnstableCoordinateCLM γ (S t R)
  have hsum : z + H t = y t := by dsimp only [z, H]; abel
  have hR : ‖R‖ ≤ C * ‖H t‖ ^ 2 := by
    have hh := (hquad (a * t) (H t) hsmall).2
    rw [show littleCircularMaterialContours hγ hγ1 (a * t) + H t = y t from hsum] at hh
    exact hh
  have hclock : HasDerivAt (fun u : ℝ => a * u) a t := by
    simpa only [id_eq, mul_one] using (hasDerivAt_id t).const_mul a
  have hc := (littleCircularMaterialContours_hasDerivAt hγ hγ1 (a * t)).scomp t hclock
  have hdH := hy.sub hc
  change HasDerivAt H ((a • F (y t) + p) - a • F z) t at hdH
  have hvector : (a • F (y t) + p) - a • F z =
      a • fderiv ℝ F z (H t) + (p + a • R) := by
    dsimp only [R]
    rw [smul_sub, smul_sub]
    abel
  rw [hvector] at hdH
  have hg := hasDerivAt_circularMaterialGrowingCoordinate_linearized hγ hγ1 a hdH
  have hsource : circularUnstableCoordinateCLM γ (S t (p + a • R)) =
      circularUnstableCoordinateCLM γ (S t p) + E := by
    rw [(S t).map_add, (S t).map_smul, (circularUnstableCoordinateCLM γ).map_add,
      (circularUnstableCoordinateCLM γ).map_smul]
    rfl
  have hproj : ‖circularUnstableCoordinateCLM γ (S t R)‖ ≤
      ‖circularUnstableCoordinateCLM γ‖ * ‖R‖ := by
    have hh := (circularUnstableCoordinateCLM γ).le_opNorm (S t R)
    rwa [norm_contourParameterShiftFamilyCLM] at hh
  refine ⟨E, ?_, ?_⟩
  · change ‖E‖ ≤ |a| * ‖circularUnstableCoordinateCLM γ‖ * C * ‖H t‖ ^ 2
    calc
      _ = |a| * ‖circularUnstableCoordinateCLM γ (S t R)‖ := by
        dsimp only [E]
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      _ ≤ |a| * (‖circularUnstableCoordinateCLM γ‖ * ‖R‖) :=
        mul_le_mul_of_nonneg_left hproj (abs_nonneg a)
      _ ≤ |a| * (‖circularUnstableCoordinateCLM γ‖ * (C * ‖H t‖ ^ 2)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hR (norm_nonneg _)) (abs_nonneg a)
      _ = _ := by ring
  · change HasDerivAt (fun u => circularUnstableCoordinateCLM γ (S u (H u)))
      ((a : ℂ) * lamStar * circularUnstableCoordinateCLM γ (S t (H t)) +
        circularUnstableCoordinateCLM γ (S t p) + E) t
    change HasDerivAt (fun u => circularUnstableCoordinateCLM γ (S u (H u)))
      ((a : ℂ) * lamStar * circularUnstableCoordinateCLM γ (S t (H t)) +
        circularUnstableCoordinateCLM γ (S t (p + a • R))) t at hg
    rw [hsource] at hg
    simpa only [add_assoc] using hg

end Euler2D

end
