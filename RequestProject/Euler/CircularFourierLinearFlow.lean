module

public import RequestProject.Euler.CircularGrowingVariation
public import RequestProject.Euler.CircularReferenceCompactness
public import RequestProject.Euler.BanachReferenceVariational
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! Every finite circular Fourier amplitude system is integrated by its
actual operator exponential and identified with the genuine period-map derivative. -/

@[expose] public section

noncomputable section

open Complex Set Filter Topology Metric
open scoped NNReal ContDiff

namespace Euler2D

abbrev CircularFourierVector := Fin 2 → ℂ
abbrev CircularFourierAmplitudes := CircularFourierVector × CircularFourierVector

def circularTangentialCouplingMatrix (N : ℕ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![-5 / 4, 3 / 4 * (cellA : ℂ) ^ N;
    5 / 4 * (cellA : ℂ) ^ (N + 4), -3 / 4]

def circularTangentialTransportMatrix (N : ℕ) : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.diagonal (fun i => -I * (N + 2 : ℕ) * circularContourAngularVelocities i)

def circularNormalGeneratorComplex (N : ℕ) : CircularFourierVector →L[ℂ] CircularFourierVector :=
  (I • (Bmat (N + 2)).map (fun r : ℝ => (r : ℂ))).mulVecLin.toContinuousLinearMap

def circularAmplitudeGeneratorComplex (N : ℕ) :
    CircularFourierAmplitudes →L[ℂ] CircularFourierAmplitudes :=
  (((I • (Bmat (N + 2)).map (fun r : ℝ => (r : ℂ))).mulVecLin.comp
      (LinearMap.fst ℂ CircularFourierVector CircularFourierVector)).prod
    (((circularTangentialCouplingMatrix N).mulVecLin.comp
      (LinearMap.fst ℂ CircularFourierVector CircularFourierVector)) +
      ((circularTangentialTransportMatrix N).mulVecLin.comp
        (LinearMap.snd ℂ CircularFourierVector CircularFourierVector)))).toContinuousLinearMap

def circularNormalGenerator (N : ℕ) : CircularFourierVector →L[ℝ] CircularFourierVector :=
  (circularNormalGeneratorComplex N).restrictScalars ℝ

def circularAmplitudeGenerator (N : ℕ) :
    CircularFourierAmplitudes →L[ℝ] CircularFourierAmplitudes :=
  (circularAmplitudeGeneratorComplex N).restrictScalars ℝ

theorem circularNormalGenerator_apply (N : ℕ) (η : CircularFourierVector) :
    circularNormalGenerator N η = circularAngularNormalAmplitude N η := rfl

theorem circularAmplitudeGenerator_apply (N : ℕ) (p : CircularFourierAmplitudes) :
    circularAmplitudeGenerator N p =
      (circularAngularNormalAmplitude N p.1,
        circularAngularTangentialAmplitude N p.1 p.2) := by
  apply Prod.ext
  · rfl
  · funext i
    change (circularTangentialCouplingMatrix N).mulVec p.1 i +
      (circularTangentialTransportMatrix N).mulVec p.2 i =
      circularAngularTangentialAmplitude N p.1 p.2 i
    unfold circularTangentialTransportMatrix
    rw [Matrix.mulVec_diagonal]
    fin_cases i <;>
      norm_num [circularAmplitudeGenerator, circularAmplitudeGeneratorComplex,
        circularTangentialCouplingMatrix, circularTangentialTransportMatrix,
        circularAngularTangentialAmplitude, circularMaterialTangentialAmplitude,
        circularContourAngularVelocities, Matrix.mulVec_diagonal, Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;>
      ring

def circularAmplitudeLinearFlow (N : ℕ) (p : CircularFourierAmplitudes) (t : ℝ) :
    CircularFourierAmplitudes := NormedSpace.exp (t • circularAmplitudeGenerator N) p

def circularNormalLinearFlow (N : ℕ) (η : CircularFourierVector) (t : ℝ) :
    CircularFourierVector := NormedSpace.exp (t • circularNormalGenerator N) η

theorem circularAmplitudeLinearFlow_hasDerivAt (N : ℕ) (p : CircularFourierAmplitudes) (t : ℝ) :
    HasDerivAt (circularAmplitudeLinearFlow N p)
      (circularAmplitudeGenerator N (circularAmplitudeLinearFlow N p t)) t := by
  unfold circularAmplitudeLinearFlow
  have hd := (hasDerivAt_exp_smul_const' (circularAmplitudeGenerator N) t).clm_apply
    (hasDerivAt_const t p)
  simpa only [ContinuousLinearMap.mul_apply, map_zero, add_zero] using hd

theorem circularNormalLinearFlow_hasDerivAt (N : ℕ) (η : CircularFourierVector) (t : ℝ) :
    HasDerivAt (circularNormalLinearFlow N η)
      (circularNormalGenerator N (circularNormalLinearFlow N η t)) t := by
  unfold circularNormalLinearFlow
  have hd := (hasDerivAt_exp_smul_const' (circularNormalGenerator N) t).clm_apply
    (hasDerivAt_const t η)
  simpa only [ContinuousLinearMap.mul_apply, map_zero, add_zero] using hd

theorem circularAmplitudeLinearFlow_zero (N : ℕ) (p : CircularFourierAmplitudes) :
    circularAmplitudeLinearFlow N p 0 = p := by
  change NormedSpace.exp ((0 : ℝ) • circularAmplitudeGenerator N) p = p
  have hz : (0 : ℝ) • circularAmplitudeGenerator N = 0 :=
    _root_.zero_smul ℝ (circularAmplitudeGenerator N)
  exact (congrArg (fun A : CircularFourierAmplitudes →L[ℝ] CircularFourierAmplitudes =>
    NormedSpace.exp A p) hz).trans
      (congrArg (fun A : CircularFourierAmplitudes →L[ℝ] CircularFourierAmplitudes => A p)
        (NormedSpace.exp_zero : NormedSpace.exp (0 : CircularFourierAmplitudes →L[ℝ] CircularFourierAmplitudes) = 1))

theorem circularNormalLinearFlow_zero (N : ℕ) (η : CircularFourierVector) :
    circularNormalLinearFlow N η 0 = η := by
  change NormedSpace.exp ((0 : ℝ) • circularNormalGenerator N) η = η
  have hz : (0 : ℝ) • circularNormalGenerator N = 0 :=
    _root_.zero_smul ℝ (circularNormalGenerator N)
  exact (congrArg (fun A : CircularFourierVector →L[ℝ] CircularFourierVector =>
    NormedSpace.exp A η) hz).trans
      (congrArg (fun A : CircularFourierVector →L[ℝ] CircularFourierVector => A η)
        (NormedSpace.exp_zero : NormedSpace.exp (0 : CircularFourierVector →L[ℝ] CircularFourierVector) = 1))

theorem circularAmplitudeLinearFlow_normal_hasDerivAt
    (N : ℕ) (p : CircularFourierAmplitudes) (t : ℝ) :
    HasDerivAt (fun s => (circularAmplitudeLinearFlow N p s).1)
      (circularAngularNormalAmplitude N (circularAmplitudeLinearFlow N p t).1) t := by
  have hd := (ContinuousLinearMap.fst ℝ CircularFourierVector CircularFourierVector).hasFDerivAt.comp_hasDerivAt
    t (circularAmplitudeLinearFlow_hasDerivAt N p t)
  change HasDerivAt (fun s => (circularAmplitudeLinearFlow N p s).1)
    (circularAmplitudeGenerator N (circularAmplitudeLinearFlow N p t)).1 t at hd
  simpa only [circularAmplitudeGenerator_apply] using hd

theorem circularAmplitudeLinearFlow_tangential_hasDerivAt
    (N : ℕ) (p : CircularFourierAmplitudes) (t : ℝ) :
    HasDerivAt (fun s => (circularAmplitudeLinearFlow N p s).2)
      (circularAngularTangentialAmplitude N (circularAmplitudeLinearFlow N p t).1
        (circularAmplitudeLinearFlow N p t).2) t := by
  have hd := (ContinuousLinearMap.snd ℝ CircularFourierVector CircularFourierVector).hasFDerivAt.comp_hasDerivAt
    t (circularAmplitudeLinearFlow_hasDerivAt N p t)
  change HasDerivAt (fun s => (circularAmplitudeLinearFlow N p s).2)
    (circularAmplitudeGenerator N (circularAmplitudeLinearFlow N p t)).2 t at hd
  simpa only [circularAmplitudeGenerator_apply] using hd

theorem circularAmplitudeLinearFlow_normal (N : ℕ) (p : CircularFourierAmplitudes)
    {t : ℝ} (ht : 0 ≤ t) :
    (circularAmplitudeLinearFlow N p t).1 = circularNormalLinearFlow N p.1 t := by
  have hαc : Continuous (fun s => (circularAmplitudeLinearFlow N p s).1) :=
    continuous_iff_continuousAt.mpr
      (fun s => (circularAmplitudeLinearFlow_normal_hasDerivAt N p s).continuousAt)
  have hβc : Continuous (circularNormalLinearFlow N p.1) :=
    continuous_iff_continuousAt.mpr
      (fun s => (circularNormalLinearFlow_hasDerivAt N p.1 s).continuousAt)
  have he : EqOn (fun s => (circularAmplitudeLinearFlow N p s).1)
      (circularNormalLinearFlow N p.1) (Icc (0 : ℝ) t) :=
    ODE_solution_unique_of_mem_Icc_right
      (v := fun _ z => circularNormalGenerator N z) (s := fun _ => (univ : Set CircularFourierVector))
      (fun _ _ => (circularNormalGenerator N).lipschitz.lipschitzOnWith)
      hαc.continuousOn
      (fun s _ => by
        simpa only [circularNormalGenerator_apply] using
          (circularAmplitudeLinearFlow_normal_hasDerivAt N p s).hasDerivWithinAt)
      (fun _ _ => mem_univ _)
      hβc.continuousOn
      (fun s _ => (circularNormalLinearFlow_hasDerivAt N p.1 s).hasDerivWithinAt)
      (fun _ _ => mem_univ _)
      (by rw [circularAmplitudeLinearFlow_zero, circularNormalLinearFlow_zero])
  exact he ⟨ht, le_rfl⟩

local instance (priority := 2000) fourierLinearFlowC1_group (γ : ℝ≥0) :
    NormedAddCommGroup (ContourC1Space γ) := Submodule.normedAddCommGroup (contourC1GraphSubmodule γ)
local instance (priority := 2000) fourierLinearFlowLittle_group (γ : ℝ≥0) :
    NormedAddCommGroup (LittleContourSpace γ) := Submodule.normedAddCommGroup (LittleContourSpace γ)
local instance (priority := 2000) fourierLinearFlowLittle_space (γ : ℝ≥0) :
    NormedSpace ℝ (LittleContourSpace γ) := Submodule.normedSpace (LittleContourSpace γ)

def circularFourierLinearVariation {γ : ℝ≥0} (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1)
    (N : ℕ) (p : CircularFourierAmplitudes) (t : ℝ) : Fin 2 → LittleContourSpace γ :=
  contourParameterShiftFamilyCLM γ (fun i => circularContourAngularVelocities i * t)
    (circularNormalModeLittle hγ hγ1.le N
      (circularAmplitudeLinearFlow N p t).1 (circularAmplitudeLinearFlow N p t).2)

theorem circularFourierLinearVariation_hasDerivAt {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1) (N : ℕ) (p : CircularFourierAmplitudes) (t : ℝ) :
    HasDerivAt (circularFourierLinearVariation hγ hγ1 N p)
      (fderiv ℝ (circularBanachField hγ hγ1) (littleCircularMaterialContours hγ hγ1 t)
        (circularFourierLinearVariation hγ hγ1 N p t)) t :=
  hasDerivAt_circularFourier_variational hγ hγ1 N
    (circularAmplitudeLinearFlow_normal_hasDerivAt N p t)
    (circularAmplitudeLinearFlow_tangential_hasDerivAt N p t)

theorem circularFourierLinearVariation_zero {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1) (N : ℕ) (p : CircularFourierAmplitudes) :
    circularFourierLinearVariation hγ hγ1 N p 0 =
      circularNormalModeLittle hγ hγ1.le N p.1 p.2 := by
  simp only [circularFourierLinearVariation, circularAmplitudeLinearFlow_zero, mul_zero]
  exact contourParameterShiftFamilyCLM_zero _

theorem circularFourierLinearVariation_period {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1) (N : ℕ) (p : CircularFourierAmplitudes) :
    circularFourierLinearVariation hγ hγ1 N p period =
      circularNormalModeLittle hγ hγ1.le N (circularNormalLinearFlow N p.1 period)
        (circularAmplitudeLinearFlow N p period).2 := by
  rw [circularFourierLinearVariation, contourParameterShiftFamily_circular_period,
    circularAmplitudeLinearFlow_normal N p (show 0 ≤ period by unfold period; positivity)]

set_option maxHeartbeats 800000 in
theorem circularPeriod_derivative_Fourier_block {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1) {ρ : ℝ} (hρ : 0 < ρ)
    {X : (Fin 2 → LittleContourSpace γ) → ℝ → Fin 2 → LittleContourSpace γ}
    (hX : IsBanachFlowOn (circularBanachField hγ hγ1) (circularBanachDomain hγ hγ1)
      (ball (littleCircularReference hγ hγ1) ρ) period X)
    (N : ℕ) (η τ : CircularFourierVector) :
    fderiv ℝ (fun W => X W period) (littleCircularReference hγ hγ1)
        (circularNormalModeLittle hγ hγ1.le N η τ) =
      circularNormalModeLittle hγ hγ1.le N (circularNormalLinearFlow N η period)
        (circularAmplitudeLinearFlow N (η, τ) period).2 := by
  have hU : IsOpen (circularBanachDomain hγ hγ1) :=
    isOpen_phaseAdmissibleLittleContourFamilies _ _
  have hf : ContDiffOn ℝ ∞ (circularBanachField hγ hγ1) (circularBanachDomain hγ hγ1) :=
    contDiffOn_finiteContourPhaseFieldTotal hγ hγ1 _ _ _ _ _ (⊤ : ℕ∞)
  have hX' : IsBanachFlowOn (circularBanachField hγ hγ1) (circularBanachDomain hγ hγ1)
      (ball (littleCircularMaterialContours hγ hγ1 0) ρ) period X := by
    rwa [littleCircularMaterialContours_zero]
  have hYc : Continuous (circularFourierLinearVariation hγ hγ1 N (η, τ)) :=
    continuous_iff_continuousAt.mpr
      (fun t => (circularFourierLinearVariation_hasDerivAt hγ hγ1 N (η, τ) t).continuousAt)
  have he := fderiv_banachFlow_eq_directional_variational_of_compact_reference hU hf
    (contDiff_littleCircularMaterialContours hγ hγ1).continuous
    (isCompact_range_littleCircularMaterialContours hγ hγ1)
    (phaseAdmissible_littleCircularMaterialContours hγ hγ1)
    (littleCircularMaterialContours_hasDerivAt hγ hγ1)
    (show 0 < period by unfold period; positivity) hρ hX' hYc.continuousOn
    (fun t _ => circularFourierLinearVariation_hasDerivAt hγ hγ1 N (η, τ) t)
  simpa only [littleCircularMaterialContours_zero, circularFourierLinearVariation_zero,
    circularFourierLinearVariation_period] using he

end Euler2D

end
