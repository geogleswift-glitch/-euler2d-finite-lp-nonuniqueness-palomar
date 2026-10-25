module

public import RequestProject.Euler.CircularPeriodConstraints
public import RequestProject.Euler.ContourMaterialArea

/-! Conservation of the original area functional throughout the
actual union of small phase neighborhoods of the circular orbit. -/

@[expose] public section

noncomputable section

open Complex Set Filter Topology Metric MeasureTheory
open scoped NNReal ContDiff ComplexConjugate

namespace Euler2D

local instance (priority := 2000) circularPhaseAreaC1_group (γ : ℝ≥0) :
    NormedAddCommGroup (ContourC1Space γ) := Submodule.normedAddCommGroup (contourC1GraphSubmodule γ)
local instance (priority := 2000) circularPhaseAreaC1_space (γ : ℝ≥0) :
    NormedSpace ℝ (ContourC1Space γ) := Submodule.normedSpace (contourC1GraphSubmodule γ)
local instance (priority := 2000) circularPhaseAreaLittle_group (γ : ℝ≥0) :
    NormedAddCommGroup (LittleContourSpace γ) := Submodule.normedAddCommGroup (LittleContourSpace γ)
local instance (priority := 2000) circularPhaseAreaLittle_space (γ : ℝ≥0) :
    NormedSpace ℝ (LittleContourSpace γ) := Submodule.normedSpace (LittleContourSpace γ)

theorem contourArea_parameterShiftC1 {γ : ℝ≥0} (b : ℝ) (Z : ContourC1Space γ) :
    contourArea γ (contourParameterShiftC1 b Z) = contourArea γ Z := by
  have he : ContourC1Space.lift γ (contourParameterShiftC1 b Z) =
      fun θ => ContourC1Space.lift γ Z (θ + b) := funext (lift_contourParameterShiftC1 b Z)
  change loopArea (ContourC1Space.lift γ (contourParameterShiftC1 b Z)) =
    loopArea (ContourC1Space.lift γ Z)
  rw [he]
  unfold loopArea
  congr 1
  have hd : deriv (fun θ => ContourC1Space.lift γ Z (θ + b)) =
      fun θ => deriv (ContourC1Space.lift γ Z) (θ + b) := by
    funext θ
    rw [ContourC1Space.deriv_lift]
    exact ((ContourC1Space.hasDerivAt_lift Z (θ + b)).comp_add_const θ b).deriv
  rw [hd]
  have hp : Function.Periodic (fun θ =>
      (conj (ContourC1Space.lift γ Z θ) * deriv (ContourC1Space.lift γ Z) θ).im)
      (2 * Real.pi) := by
    intro θ
    dsimp only
    rw [ContourC1Space.periodic_lift Z θ, periodic_deriv (ContourC1Space.periodic_lift Z) θ]
  simpa only [sub_neg_eq_add] using integral_period_comp_sub hp (-b)

theorem contourAreaDerivative_parameterShiftC1 {γ : ℝ≥0} (b : ℝ)
    (Z V : ContourC1Space γ) :
    contourAreaDerivative (contourParameterShiftC1 b Z) (contourParameterShiftC1 b V) =
      contourAreaDerivative Z V := by
  have hleft := (hasFDerivAt_contourArea (contourParameterShiftC1 b Z)).comp Z
    (contourParameterShiftC1CLM γ b).hasFDerivAt
  have he : (fun W : ContourC1Space γ => contourArea γ (contourParameterShiftC1 b W)) =
      contourArea γ := funext (contourArea_parameterShiftC1 b)
  change HasFDerivAt (fun W : ContourC1Space γ => contourArea γ (contourParameterShiftC1 b W))
    ((contourAreaDerivative (contourParameterShiftC1 b Z)).comp (contourParameterShiftC1CLM γ b)) Z
    at hleft
  rw [he] at hleft
  exact congrArg (fun A : ContourC1Space γ →L[ℝ] ℝ => A V)
    (hleft.unique (hasFDerivAt_contourArea Z))

def circularQuarterPhaseDomain {γ : ℝ≥0} (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1) :
    Set (Fin 2 → LittleContourSpace γ) :=
  circularBanachDomain hγ hγ1 ∩
    {Z | ∃ b : Fin 2 → ℝ, ∀ i,
      ‖(contourParameterShiftFamilyCLM γ (-b) Z i).val - circularReferenceC1 hγ hγ1 i‖ <
        circularContourRadii i / 4}

set_option maxHeartbeats 600000 in
theorem isOpen_circularQuarterPhaseDomain {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1) :
    IsOpen (circularQuarterPhaseDomain hγ hγ1) := by
  apply (isOpen_phaseAdmissibleLittleContourFamilies _ _).inter
  have he : {Z : Fin 2 → LittleContourSpace γ | ∃ b : Fin 2 → ℝ, ∀ i,
      ‖(contourParameterShiftFamilyCLM γ (-b) Z i).val - circularReferenceC1 hγ hγ1 i‖ <
        circularContourRadii i / 4} =
      ⋃ b : Fin 2 → ℝ, ⋂ i : Fin 2,
        {Z | ‖(contourParameterShiftFamilyCLM γ (-b) Z i).val - circularReferenceC1 hγ hγ1 i‖ <
          circularContourRadii i / 4} := by
    ext Z
    simp only [mem_setOf_eq, mem_iUnion, mem_iInter]
  rw [he]
  apply isOpen_iUnion
  intro b
  apply isOpen_iInter_of_finite
  intro i
  have hc : Continuous (fun Z : Fin 2 → LittleContourSpace γ =>
      (contourParameterShiftFamilyCLM γ (-b) Z i).val) :=
    (((LittleContourSpace.inclusion γ).comp (ContinuousLinearMap.proj i)).comp
      (contourParameterShiftFamilyCLM γ (-b))).continuous
  exact isOpen_lt (hc.sub continuous_const).norm continuous_const

theorem littleCircularMaterialContours_mem_quarterPhaseDomain {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1) (t : ℝ) :
    littleCircularMaterialContours hγ hγ1 t ∈ circularQuarterPhaseDomain hγ hγ1 := by
  refine ⟨phaseAdmissible_littleCircularMaterialContours hγ hγ1 t, ?_⟩
  let b : Fin 2 → ℝ := fun i => circularContourAngularVelocities i * t
  refine ⟨b, ?_⟩
  intro i
  have he : contourParameterShiftFamilyCLM γ (-b) (littleCircularMaterialContours hγ hγ1 t) i =
      littleCircularReference hγ hγ1 i := by
    apply Subtype.ext
    apply ContourC1Space.ext
    intro x
    obtain ⟨θ, rfl⟩ := QuotientAddGroup.mk_surjective x
    change LittleContourSpace.lift γ
      (contourParameterShiftLittleCLM γ (-b i) (littleCircularMaterialContours hγ hγ1 t i)) θ =
      refCircle (circularContourRadii i) θ
    rw [lift_contourParameterShiftLittleCLM, lift_littleCircularMaterialContours]
    dsimp only [circularMaterialContours, b]
    congr 1
    ring
  rw [he]
  change ‖(littleCircularReference hγ hγ1 i).val - (littleCircularReference hγ hγ1 i).val‖ < _
  simp only [sub_self, norm_zero]
  have hr : 0 < circularContourRadii i := by
    fin_cases i <;> simp [circularContourRadii, cellA_pos]
  exact div_pos hr (by norm_num)

set_option maxHeartbeats 900000 in
theorem contourAreaDerivative_circularBanachField_zero {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1)
    (Z : Fin 2 → LittleContourSpace γ) (hZ : Z ∈ circularQuarterPhaseDomain hγ hγ1)
    (i : Fin 2) :
    contourAreaDerivative (Z i).val (circularBanachField hγ hγ1 Z i).val = 0 := by
  obtain ⟨b, hb⟩ := hZ.2
  let Q : Fin 2 → ContourC1Space γ := fun j =>
    contourParameterShiftC1 (-b j) (Z j).val
  let V : Fin 2 → ContourC1Space γ := fun j =>
    contourParameterShiftC1 (-b j) (circularBanachField hγ hγ1 Z j).val
  have hsmall (j : Fin 2) : ‖Q j - circularReferenceC1 hγ hγ1 j‖ ≤ circularContourRadii j / 4 :=
    (hb j).le
  have hV (j : Fin 2) (θ : ℝ) : ContourC1Space.lift γ (V j) θ =
      contourC1BoundaryField circularContourStrengths Q j θ := by
    change ContourC1Space.lift γ
        (contourParameterShiftC1 (-b j) (circularBanachField hγ hγ1 Z j).val) θ = _
    rw [lift_contourParameterShiftC1]
    change LittleContourSpace.lift γ (circularBanachField hγ hγ1 Z j) (θ + -b j) = _
    rw [circularBanachField, lift_finiteContourPhaseFieldTotal hγ hγ1 _ _ _ _ _ Z hZ.1]
    have he : (fun k => ContourC1Space.lift γ (Q k)) =
        (fun k φ => LittleContourSpace.lift γ (Z k) (φ + -b k)) := by
      funext k φ
      exact lift_contourParameterShiftC1 (-b k) (Z k).val φ
    change _ = contourBoundaryField circularContourStrengths (fun k => ContourC1Space.lift γ (Q k)) j θ
    rw [he]
    exact (contourBoundaryField_reparametrize circularContourStrengths
      (fun k => LittleContourSpace.lift γ (Z k)) (-b)
      (fun k x => (LittleContourSpace.hasDerivAt_lift (Z k) x).differentiableAt)
      (fun k => LittleContourSpace.periodic_lift (Z k))
      (fun k => periodic_deriv (LittleContourSpace.periodic_lift (Z k))) j θ).symm
  have hzero : contourAreaDerivative (Q i) (V i) = 0 := by
    rw [contourAreaDerivative_apply]
    simp_rw [hV i]
    exact contourC1BoundaryField_normalFlux_zero circularContourStrengths Q
      (circularReferenceC1 hγ hγ1) circularContourRadii
      (fun j => by fin_cases j <;> simp [circularContourRadii, cellA_pos])
      (lift_circularReferenceC1 hγ hγ1) hsmall i
  rw [← contourAreaDerivative_parameterShiftC1 (-b i)]
  exact hzero

theorem circularBanachFlow_area {γ : ℝ≥0} (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1)
    {V : Set (Fin 2 → LittleContourSpace γ)} {T : ℝ}
    {X : (Fin 2 → LittleContourSpace γ) → ℝ → Fin 2 → LittleContourSpace γ}
    (hX : IsBanachFlowOn (circularBanachField hγ hγ1) (circularQuarterPhaseDomain hγ hγ1) V T X)
    {W : Fin 2 → LittleContourSpace γ} (hW : W ∈ V)
    {t : ℝ} (ht : t ∈ Icc 0 T) (i : Fin 2) :
    littleContourArea γ (X W t i) = littleContourArea γ (W i) := by
  have hd (s : ℝ) (hs : s ∈ Icc 0 T) :
      HasDerivAt (fun u => littleContourArea γ (X W u i)) 0 s := by
    have hi := ((LittleContourSpace.inclusion γ).comp (ContinuousLinearMap.proj i)).hasFDerivAt.comp_hasDerivAt s
      (hX.hasDerivAt W hW s hs)
    change HasDerivAt (fun u => (X W u i).val) (circularBanachField hγ hγ1 (X W s) i).val s at hi
    have ha := (hasFDerivAt_contourArea (X W s i).val).comp_hasDerivAt s hi
    change HasDerivAt (fun u => littleContourArea γ (X W u i))
      (contourAreaDerivative (X W s i).val (circularBanachField hγ hγ1 (X W s) i).val) s at ha
    rwa [contourAreaDerivative_circularBanachField_zero hγ hγ1 (X W s) (hX.mem W hW s hs) i] at ha
  have hscope : Set.uIcc 0 t ⊆ Icc 0 T := by
    rw [uIcc_of_le ht.1]
    exact Icc_subset_Icc le_rfl ht.2
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := 0) (b := t) (fun s hs => hd s (hscope hs))
    (intervalIntegral.intervalIntegrable_const :
      IntervalIntegrable (fun _ : ℝ => (0 : ℝ)) volume 0 t)
  have heq := sub_eq_zero.mp (by simpa only [intervalIntegral.integral_zero] using he.symm)
  simpa only [hX.initial W hW] using heq

end Euler2D

end
