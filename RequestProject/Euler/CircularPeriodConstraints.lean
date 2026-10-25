module

public import RequestProject.Euler.CircularContourPeriodMap
public import RequestProject.Euler.CircularFourierConstraints
public import RequestProject.Euler.BanachOpenODEUniqueness

/-! Rotation covariance of the original full-period Banach flow.
The field domain is the actual union of phase charts. -/

@[expose] public section

noncomputable section

open Complex Set Filter Topology Metric
open scoped NNReal ContDiff

namespace Euler2D

local instance (priority := 2000) periodConstraintC1_group (γ : ℝ≥0) :
    NormedAddCommGroup (ContourC1Space γ) := Submodule.normedAddCommGroup (contourC1GraphSubmodule γ)
local instance (priority := 2000) periodConstraintC1_space (γ : ℝ≥0) :
    NormedSpace ℝ (ContourC1Space γ) := Submodule.normedSpace (contourC1GraphSubmodule γ)
local instance (priority := 2000) periodConstraintLittle_group (γ : ℝ≥0) :
    NormedAddCommGroup (LittleContourSpace γ) := Submodule.normedAddCommGroup (LittleContourSpace γ)
local instance (priority := 2000) periodConstraintLittle_space (γ : ℝ≥0) :
    NormedSpace ℝ (LittleContourSpace γ) := Submodule.normedSpace (LittleContourSpace γ)

def contourRotationFamilyLittleCLM {ι : Type} [Fintype ι] (γ : ℝ≥0) (b : ℝ) :
    (ι → LittleContourSpace γ) →L[ℝ] (ι → LittleContourSpace γ) :=
  ContinuousLinearMap.pi (fun i => (contourRotationLittleCLM γ b).comp (ContinuousLinearMap.proj i))

@[simp] theorem contourRotationFamilyLittleCLM_apply {γ : ℝ≥0} {ι : Type} [Fintype ι]
    (b : ℝ) (Z : ι → LittleContourSpace γ) (i : ι) :
    contourRotationFamilyLittleCLM γ b Z i = contourRotationLittleCLM γ b (Z i) := rfl

theorem contourRotationLittleCLM_parameterShift_comm {γ : ℝ≥0} (b c : ℝ)
    (Z : LittleContourSpace γ) :
    contourParameterShiftLittleCLM γ c (contourRotationLittleCLM γ b Z) =
      contourRotationLittleCLM γ b (contourParameterShiftLittleCLM γ c Z) := by
  apply Subtype.ext
  apply ContourC1Space.ext
  intro x
  obtain ⟨θ, rfl⟩ := QuotientAddGroup.mk_surjective x
  change LittleContourSpace.lift γ
      (contourParameterShiftLittleCLM γ c (contourRotationLittleCLM γ b Z)) θ =
    LittleContourSpace.lift γ
      (contourRotationLittleCLM γ b (contourParameterShiftLittleCLM γ c Z)) θ
  simp only [lift_contourParameterShiftLittleCLM, lift_contourRotationLittleCLM, rotShift]
  congr 2
  ring

set_option maxHeartbeats 600000 in
theorem admissibleLittleContourFamily_rotation {γ : ℝ≥0} {ι : Type} [Fintype ι]
    (Z₀ : ι → ContourC1Space γ) (r : ι → ℝ)
    (href : ∀ i, ContourC1Space.lift γ (Z₀ i) = refCircle (r i))
    (b : ℝ) (Z : ι → LittleContourSpace γ)
    (hZ : IsAdmissibleLittleContourFamily Z₀ r Z) :
    IsAdmissibleLittleContourFamily Z₀ r (contourRotationFamilyLittleCLM γ b Z) := by
  constructor
  · intro i
    change ‖contourRotationC1 b (Z i).val - Z₀ i‖ < _
    have hfix := contourRotationC1_refCircle b (Z₀ i) (href i)
    have he : contourRotationC1 b ((Z i).val - Z₀ i) = contourRotationC1 b (Z i).val - Z₀ i := by
      change contourRotationC1CLM γ b ((Z i).val - Z₀ i) = _
      rw [map_sub]
      exact congrArg (contourRotationC1 b (Z i).val - ·) hfix
    rw [← he, norm_contourRotationC1]
    exact hZ.1 i
  · intro i j hij
    obtain ⟨σ, hσ, hsep⟩ := hZ.2 i j hij
    refine ⟨σ, hσ, ?_⟩
    intro x y
    obtain ⟨θ, rfl⟩ := QuotientAddGroup.mk_surjective x
    obtain ⟨φ, rfl⟩ := QuotientAddGroup.mk_surjective y
    change σ ≤ ‖LittleContourSpace.lift γ (contourRotationLittleCLM γ b (Z i)) θ -
      LittleContourSpace.lift γ (contourRotationLittleCLM γ b (Z j)) φ‖
    simp only [lift_contourRotationLittleCLM, rotShift, ← mul_sub, norm_mul,
      norm_exp_ofReal_mul_I, one_mul]
    have hh := hsep ((θ - b : ℝ) : ContourCircle) ((φ - b : ℝ) : ContourCircle)
    change σ ≤ ‖LittleContourSpace.lift γ (Z i) (θ - b) -
      LittleContourSpace.lift γ (Z j) (φ - b)‖ at hh
    exact hh

theorem phaseAdmissibleLittleContourFamily_rotation {γ : ℝ≥0} {ι : Type} [Fintype ι]
    (Z₀ : ι → ContourC1Space γ) (r : ι → ℝ)
    (href : ∀ i, ContourC1Space.lift γ (Z₀ i) = refCircle (r i))
    (b : ℝ) (Z : ι → LittleContourSpace γ)
    (hZ : IsPhaseAdmissibleLittleContourFamily Z₀ r Z) :
    IsPhaseAdmissibleLittleContourFamily Z₀ r (contourRotationFamilyLittleCLM γ b Z) := by
  obtain ⟨c, hc⟩ := hZ
  refine ⟨c, ?_⟩
  have he : contourParameterShiftFamilyCLM γ (-c) (contourRotationFamilyLittleCLM γ b Z) =
      contourRotationFamilyLittleCLM γ b (contourParameterShiftFamilyCLM γ (-c) Z) := by
    funext i
    exact contourRotationLittleCLM_parameterShift_comm b (-c i) (Z i)
  rw [he]
  exact admissibleLittleContourFamily_rotation Z₀ r href b _ hc

set_option maxHeartbeats 600000 in
theorem finiteContourPhaseFieldTotal_rotation {γ : ℝ≥0} {ι : Type} [Fintype ι]
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1)
    (Z₀ : ι → ContourC1Space γ) (r : ι → ℝ) (hr : ∀ i, 0 < r i)
    (href : ∀ i, ContourC1Space.lift γ (Z₀ i) = refCircle (r i)) (g : ι → ℝ)
    (b : ℝ) (Z : ι → LittleContourSpace γ)
    (hZ : IsPhaseAdmissibleLittleContourFamily Z₀ r Z) :
    finiteContourPhaseFieldTotal hγ hγ1 Z₀ r hr href g (contourRotationFamilyLittleCLM γ b Z) =
      contourRotationFamilyLittleCLM γ b (finiteContourPhaseFieldTotal hγ hγ1 Z₀ r hr href g Z) := by
  have hrot := phaseAdmissibleLittleContourFamily_rotation Z₀ r href b Z hZ
  funext i
  apply Subtype.ext
  apply ContourC1Space.ext
  intro x
  obtain ⟨θ, rfl⟩ := QuotientAddGroup.mk_surjective x
  change LittleContourSpace.lift γ
      (finiteContourPhaseFieldTotal hγ hγ1 Z₀ r hr href g (contourRotationFamilyLittleCLM γ b Z) i) θ =
    LittleContourSpace.lift γ
      (contourRotationLittleCLM γ b (finiteContourPhaseFieldTotal hγ hγ1 Z₀ r hr href g Z i)) θ
  rw [lift_contourRotationLittleCLM, lift_finiteContourPhaseFieldTotal hγ hγ1 Z₀ r hr href g _ hrot]
  change contourBoundaryField g
      (fun j => LittleContourSpace.lift γ (contourRotationLittleCLM γ b (Z j))) i θ = _
  simp_rw [lift_contourRotationLittleCLM]
  rw [contourBoundaryField_rotShift g _
    (fun j x => (LittleContourSpace.hasDerivAt_lift (Z j) x).differentiableAt)
    (fun j => LittleContourSpace.periodic_lift (Z j)) b i θ]
  unfold rotShift
  rw [lift_finiteContourPhaseFieldTotal hγ hγ1 Z₀ r hr href g Z hZ]

theorem circularBanachDomain_rotation {γ : ℝ≥0} (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1)
    (b : ℝ) {Z : Fin 2 → LittleContourSpace γ} (hZ : Z ∈ circularBanachDomain hγ hγ1) :
    contourRotationFamilyLittleCLM γ b Z ∈ circularBanachDomain hγ hγ1 :=
  phaseAdmissibleLittleContourFamily_rotation _ _ (lift_circularReferenceC1 hγ hγ1) b Z hZ

theorem circularBanachField_rotation {γ : ℝ≥0} (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1)
    (b : ℝ) {Z : Fin 2 → LittleContourSpace γ} (hZ : Z ∈ circularBanachDomain hγ hγ1) :
    circularBanachField hγ hγ1 (contourRotationFamilyLittleCLM γ b Z) =
      contourRotationFamilyLittleCLM γ b (circularBanachField hγ hγ1 Z) :=
  finiteContourPhaseFieldTotal_rotation hγ hγ1 _ _ _ _ _ b Z hZ

set_option maxHeartbeats 800000 in
theorem circularBanachFlow_fourfold {γ : ℝ≥0} (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1)
    {V : Set (Fin 2 → LittleContourSpace γ)} {T : ℝ}
    {X : (Fin 2 → LittleContourSpace γ) → ℝ → Fin 2 → LittleContourSpace γ}
    (hX : IsBanachFlowOn (circularBanachField hγ hγ1) (circularBanachDomain hγ hγ1) V T X)
    {W : Fin 2 → LittleContourSpace γ} (hW : W ∈ V)
    (hfour : ∀ i, W i ∈ fourfoldLittleContourSubmodule γ)
    {t : ℝ} (ht : t ∈ Icc 0 T) (i : Fin 2) :
    X W t i ∈ fourfoldLittleContourSubmodule γ := by
  let R := contourRotationFamilyLittleCLM (ι := Fin 2) γ (Real.pi / 2)
  have he0 : R W = W := by
    funext j
    have hj := hfour j
    change contourRotationLittleCLM γ (Real.pi / 2) (W j) - W j = 0 at hj
    exact sub_eq_zero.mp hj
  have hrotD (s : ℝ) (hs : s ∈ Icc 0 T) :
      HasDerivAt (fun u => R (X W u)) (circularBanachField hγ hγ1 (R (X W s))) s := by
    have hd := R.hasFDerivAt.comp_hasDerivAt s (hX.hasDerivAt W hW s hs)
    change HasDerivAt (fun u => R (X W u)) (R (circularBanachField hγ hγ1 (X W s))) s at hd
    rw [← circularBanachField_rotation hγ hγ1 (Real.pi / 2) (hX.mem W hW s hs)] at hd
    exact hd
  have he : EqOn (fun u => R (X W u)) (X W) (Icc 0 T) := by
    apply eqOn_of_banachODE_open
      (isOpen_phaseAdmissibleLittleContourFamilies _ _)
      (contDiffOn_finiteContourPhaseFieldTotal hγ hγ1 _ _ _ _ _ 1)
      (R.continuous.comp_continuousOn (hX.continuous W hW)) (hX.continuous W hW)
      (fun s hs => circularBanachDomain_rotation hγ hγ1 _ (hX.mem W hW s hs))
      (hX.mem W hW)
      (fun s hs => hrotD s ⟨hs.1, hs.2.le⟩)
      (fun s hs => hX.hasDerivAt W hW s ⟨hs.1, hs.2.le⟩)
    change R (X W 0) = X W 0
    rw [hX.initial W hW, he0]
  change contourRotationLittleCLM γ (Real.pi / 2) (X W t i) - X W t i = 0
  exact sub_eq_zero.mpr (congrFun (he ht) i)

end Euler2D

end
