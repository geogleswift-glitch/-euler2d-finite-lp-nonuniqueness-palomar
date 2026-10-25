module

public import RequestProject.Euler.FiniteContourPhaseFlow
public import RequestProject.Euler.ContourStarGeometry

/-! The actual circular material reference orbit in the genuine little
Banach space. Its strong time derivative is the original phase field;
pointwise circular dynamics alone are not used as a substitute for this. -/

@[expose] public section

noncomputable section

open Set Filter Topology Metric Complex
open scoped NNReal ContDiff

namespace Euler2D

local instance (priority := 2000) circularBanachC1_group (γ : ℝ≥0) :
    NormedAddCommGroup (ContourC1Space γ) := Submodule.normedAddCommGroup (contourC1GraphSubmodule γ)
local instance (priority := 2000) circularBanachC1_space (γ : ℝ≥0) :
    NormedSpace ℝ (ContourC1Space γ) := Submodule.normedSpace (contourC1GraphSubmodule γ)
local instance (priority := 2000) circularBanachLittle_group (γ : ℝ≥0) :
    NormedAddCommGroup (LittleContourSpace γ) := Submodule.normedAddCommGroup (LittleContourSpace γ)
local instance (priority := 2000) circularBanachLittle_space (γ : ℝ≥0) :
    NormedSpace ℝ (LittleContourSpace γ) := Submodule.normedSpace (LittleContourSpace γ)

theorem refCircle_phase_decomposition (r θ b : ℝ) :
    refCircle r (θ + b) = (Real.cos b : ℂ) * refCircle r θ +
      (Real.sin b : ℂ) * refCircle r (θ + Real.pi / 2) := by
  have he (c : ℝ) : exp (((θ + c : ℝ) : ℂ) * I) =
      exp ((θ : ℂ) * I) * exp ((c : ℂ) * I) := by
    rw [show (((θ + c : ℝ) : ℂ) * I) = (θ : ℂ) * I + (c : ℂ) * I by push_cast; ring,
      exp_add]
  have hq : exp (((Real.pi / 2 : ℝ) : ℂ) * I) = I := by
    push_cast
    exact exp_pi_div_two_mul_I
  simp only [refCircle, he, hq, exp_mul_I, ofReal_cos, ofReal_sin]
  ring

def littleCircularReference {γ : ℝ≥0} (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1)
    (i : Fin 2) : LittleContourSpace γ :=
  littleReferenceCircle hγ hγ1.le (circularContourRadii i)

def circularReferenceC1 {γ : ℝ≥0} (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1)
    (i : Fin 2) : ContourC1Space γ := (littleCircularReference hγ hγ1 i).val

@[simp] theorem lift_circularReferenceC1 {γ : ℝ≥0} (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1)
    (i : Fin 2) : ContourC1Space.lift γ (circularReferenceC1 hγ hγ1 i) =
      refCircle (circularContourRadii i) := rfl

def littleCircularMaterialContours {γ : ℝ≥0} (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1)
    (t : ℝ) (i : Fin 2) : LittleContourSpace γ :=
  Real.cos (circularContourAngularVelocities i * t) • littleCircularReference hγ hγ1 i +
    Real.sin (circularContourAngularVelocities i * t) •
      contourParameterShiftLittleCLM γ (Real.pi / 2) (littleCircularReference hγ hγ1 i)

theorem lift_littleCircularMaterialContours {γ : ℝ≥0} (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1)
    (t : ℝ) (i : Fin 2) (θ : ℝ) :
    LittleContourSpace.lift γ (littleCircularMaterialContours hγ hγ1 t i) θ =
      circularMaterialContours t i θ := by
  change (Real.cos (circularContourAngularVelocities i * t) : ℝ) •
      refCircle (circularContourRadii i) θ +
    (Real.sin (circularContourAngularVelocities i * t) : ℝ) •
      LittleContourSpace.lift γ
        (contourParameterShiftLittleCLM γ (Real.pi / 2) (littleCircularReference hγ hγ1 i)) θ = _
  rw [lift_contourParameterShiftLittleCLM]
  change (Real.cos (circularContourAngularVelocities i * t) : ℝ) •
      refCircle (circularContourRadii i) θ +
    (Real.sin (circularContourAngularVelocities i * t) : ℝ) •
      refCircle (circularContourRadii i) (θ + Real.pi / 2) = _
  simp only [Complex.real_smul, circularMaterialContours]
  exact (refCircle_phase_decomposition _ _ _).symm

theorem contDiff_littleCircularMaterialContours {γ : ℝ≥0} (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1) :
    ContDiff ℝ ∞ (littleCircularMaterialContours hγ hγ1) := by
  apply contDiff_pi.mpr
  intro i
  have hp : ContDiff ℝ ∞ (fun t : ℝ => circularContourAngularVelocities i * t) :=
    contDiff_const.mul contDiff_id
  exact (hp.cos.smul contDiff_const).add (hp.sin.smul contDiff_const)

theorem admissible_littleCircularReference {γ : ℝ≥0} (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1) :
    IsAdmissibleLittleContourFamily (circularReferenceC1 hγ hγ1) circularContourRadii
      (littleCircularReference hγ hγ1) := by
  have hr (i : Fin 2) : 0 < circularContourRadii i := by
    fin_cases i <;> simp [circularContourRadii, cellA_pos]
  have hinj : Function.Injective circularContourRadii := by
    intro i j h
    fin_cases i <;> fin_cases j <;>
      simp_all [circularContourRadii, cellA_lt_one.ne, cellA_lt_one.ne.symm]
  constructor
  · intro i
    change ‖(littleCircularReference hγ hγ1 i).val - (littleCircularReference hγ hγ1 i).val‖ < _
    simp only [sub_self, norm_zero]
    exact div_pos (mul_pos (by norm_num) (hr i)) Real.pi_pos
  · intro i j hij
    refine ⟨|circularContourRadii i - circularContourRadii j|,
      abs_pos.mpr (sub_ne_zero.mpr (fun h => hij (hinj h))), ?_⟩
    intro x y
    obtain ⟨θ, rfl⟩ := QuotientAddGroup.mk_surjective x
    obtain ⟨φ, rfl⟩ := QuotientAddGroup.mk_surjective y
    change |circularContourRadii i - circularContourRadii j| ≤
      ‖refCircle (circularContourRadii i) θ - refCircle (circularContourRadii j) φ‖
    simpa only [norm_refCircle_actual, abs_of_pos (hr i), abs_of_pos (hr j)] using
      abs_norm_sub_norm_le (refCircle (circularContourRadii i) θ) (refCircle (circularContourRadii j) φ)

theorem phaseAdmissible_littleCircularMaterialContours {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1) (t : ℝ) :
    IsPhaseAdmissibleLittleContourFamily (circularReferenceC1 hγ hγ1) circularContourRadii
      (littleCircularMaterialContours hγ hγ1 t) := by
  let b : Fin 2 → ℝ := fun i => circularContourAngularVelocities i * t
  refine ⟨b, ?_⟩
  have he : contourParameterShiftFamilyCLM γ (-b) (littleCircularMaterialContours hγ hγ1 t) =
      littleCircularReference hγ hγ1 := by
    funext i
    apply Subtype.ext
    apply ContourC1Space.ext
    intro x
    obtain ⟨θ, rfl⟩ := QuotientAddGroup.mk_surjective x
    change LittleContourSpace.lift γ
      (contourParameterShiftLittleCLM γ ((-b) i) (littleCircularMaterialContours hγ hγ1 t i)) θ =
      refCircle (circularContourRadii i) θ
    rw [lift_contourParameterShiftLittleCLM, lift_littleCircularMaterialContours]
    dsimp only [circularMaterialContours, b, Pi.neg_apply]
    congr 1
    ring
  rw [he]
  exact admissible_littleCircularReference hγ hγ1

set_option maxHeartbeats 600000 in
theorem littleCircularMaterialContours_hasDerivAt {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1) (t : ℝ) :
    HasDerivAt (littleCircularMaterialContours hγ hγ1)
      (finiteContourPhaseFieldTotal hγ hγ1 (circularReferenceC1 hγ hγ1) circularContourRadii
        (fun i => by fin_cases i <;> simp [circularContourRadii, cellA_pos])
        (lift_circularReferenceC1 hγ hγ1) circularContourStrengths
        (littleCircularMaterialContours hγ hγ1 t)) t := by
  let D : Fin 2 → LittleContourSpace γ := fun i =>
    (-Real.sin (circularContourAngularVelocities i * t) * circularContourAngularVelocities i) •
      littleCircularReference hγ hγ1 i +
    (Real.cos (circularContourAngularVelocities i * t) * circularContourAngularVelocities i) •
      contourParameterShiftLittleCLM γ (Real.pi / 2) (littleCircularReference hγ hγ1 i)
  have hd : HasDerivAt (littleCircularMaterialContours hγ hγ1) D t := by
    apply hasDerivAt_pi.mpr
    intro i
    have hp := (hasDerivAt_id t).const_mul (circularContourAngularVelocities i)
    simpa only [littleCircularMaterialContours, D, Function.comp_def, Pi.add_def, id_eq, mul_one] using
      (((Real.hasDerivAt_cos _).comp t hp).smul_const (littleCircularReference hγ hγ1 i)).add
        (((Real.hasDerivAt_sin _).comp t hp).smul_const
          (contourParameterShiftLittleCLM γ (Real.pi / 2) (littleCircularReference hγ hγ1 i)))
  convert hd using 1
  funext i
  apply Subtype.ext
  apply ContourC1Space.ext
  intro x
  obtain ⟨θ, rfl⟩ := QuotientAddGroup.mk_surjective x
  have he := ((LittleContourSpace.eval γ (θ : ContourCircle)).comp
    (ContinuousLinearMap.proj i)).hasFDerivAt.comp_hasDerivAt t hd
  change HasDerivAt (fun s => LittleContourSpace.lift γ (littleCircularMaterialContours hγ hγ1 s i) θ)
    (LittleContourSpace.lift γ (D i) θ) t at he
  simp_rw [lift_littleCircularMaterialContours hγ hγ1] at he
  have hu := he.unique (circularMaterialContours_hasDerivAt t i θ)
  change LittleContourSpace.lift γ
    (finiteContourPhaseFieldTotal hγ hγ1 (circularReferenceC1 hγ hγ1) circularContourRadii _ _
      circularContourStrengths (littleCircularMaterialContours hγ hγ1 t) i) θ =
    LittleContourSpace.lift γ (D i) θ
  rw [lift_finiteContourPhaseFieldTotal hγ hγ1 (circularReferenceC1 hγ hγ1) circularContourRadii
    _ _ circularContourStrengths (littleCircularMaterialContours hγ hγ1 t)
    (phaseAdmissible_littleCircularMaterialContours hγ hγ1 t)]
  have hefun : (fun j => LittleContourSpace.lift γ (littleCircularMaterialContours hγ hγ1 t j)) =
      circularMaterialContours t := by
    funext j φ
    exact lift_littleCircularMaterialContours hγ hγ1 t j φ
  rw [hefun]
  exact hu.symm

theorem littleCircularMaterialContours_period {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1) :
    littleCircularMaterialContours hγ hγ1 period = littleCircularMaterialContours hγ hγ1 0 := by
  funext i
  apply Subtype.ext
  apply ContourC1Space.ext
  intro x
  obtain ⟨θ, rfl⟩ := QuotientAddGroup.mk_surjective x
  change LittleContourSpace.lift γ (littleCircularMaterialContours hγ hγ1 period i) θ =
    LittleContourSpace.lift γ (littleCircularMaterialContours hγ hγ1 0 i) θ
  rw [lift_littleCircularMaterialContours, lift_littleCircularMaterialContours,
    circularMaterialContours_period]

end Euler2D

end
