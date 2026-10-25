module

public import RequestProject.Euler.CircularAngularModeProjection
public import RequestProject.Euler.CircularFourierLinearFlow

/-! Actual bounded normal/tangential coordinates at every angular
mode identify the genuine period derivative on arbitrary perturbations. -/

@[expose] public section

set_option maxHeartbeats 1000000

noncomputable section

open Complex Set Filter Topology Metric
open scoped NNReal ContDiff ComplexConjugate

namespace Euler2D

local instance (priority := 2000) allModeLittle_group (γ : ℝ≥0) :
    NormedAddCommGroup (LittleContourSpace γ) := Submodule.normedAddCommGroup (LittleContourSpace γ)
local instance (priority := 2000) allModeLittle_space (γ : ℝ≥0) :
    NormedSpace ℝ (LittleContourSpace γ) := Submodule.normedSpace (LittleContourSpace γ)

def littleContourModeNormalCoefficientCLM (γ : ℝ≥0) (r : ℝ) (N : ℕ) :
    LittleContourSpace γ →L[ℝ] ℂ :=
  ((ContinuousLinearMap.mul ℝ ℂ) ((r : ℂ)⁻¹)).comp
    (littleContourFourierCoefficientCLM γ ((N + 3 : ℕ) : ℤ) +
      Complex.conjCLE.toContinuousLinearMap.comp
        (littleContourFourierCoefficientCLM γ (-((N + 1 : ℕ) : ℤ))))

def littleContourModeTangentCoefficientCLM (γ : ℝ≥0) (r : ℝ) (N : ℕ) :
    LittleContourSpace γ →L[ℝ] ℂ :=
  ((ContinuousLinearMap.mul ℝ ℂ) (-I / (r : ℂ))).comp
    (littleContourFourierCoefficientCLM γ ((N + 3 : ℕ) : ℤ) -
      Complex.conjCLE.toContinuousLinearMap.comp
        (littleContourFourierCoefficientCLM γ (-((N + 1 : ℕ) : ℤ))))

theorem littleContourModeNormalCoefficientCLM_apply {γ : ℝ≥0} (r : ℝ) (N : ℕ)
    (H : LittleContourSpace γ) :
    littleContourModeNormalCoefficientCLM γ r N H =
      (littleContourFourierCoefficient γ ((N + 3 : ℕ) : ℤ) H +
        conj (littleContourFourierCoefficient γ (-((N + 1 : ℕ) : ℤ)) H)) / (r : ℂ) := by
  change (r : ℂ)⁻¹ * (littleContourFourierCoefficient γ ((N + 3 : ℕ) : ℤ) H +
    conj (littleContourFourierCoefficient γ (-((N + 1 : ℕ) : ℤ)) H)) = _
  rw [div_eq_mul_inv, mul_comm]

theorem littleContourModeTangentCoefficientCLM_apply {γ : ℝ≥0} (r : ℝ) (N : ℕ)
    (H : LittleContourSpace γ) :
    littleContourModeTangentCoefficientCLM γ r N H =
      (-I / (r : ℂ)) * (littleContourFourierCoefficient γ ((N + 3 : ℕ) : ℤ) H -
        conj (littleContourFourierCoefficient γ (-((N + 1 : ℕ) : ℤ)) H)) := rfl

def circularModeNormalCoefficientCLM (γ : ℝ≥0) (N : ℕ) :
    (Fin 2 → LittleContourSpace γ) →L[ℝ] CircularFourierVector :=
  ContinuousLinearMap.pi fun i =>
    (littleContourModeNormalCoefficientCLM γ (circularContourRadii i) N).comp (ContinuousLinearMap.proj i)

def circularModeTangentCoefficientCLM (γ : ℝ≥0) (N : ℕ) :
    (Fin 2 → LittleContourSpace γ) →L[ℝ] CircularFourierVector :=
  ContinuousLinearMap.pi fun i =>
    (littleContourModeTangentCoefficientCLM γ (circularContourRadii i) N).comp (ContinuousLinearMap.proj i)

def circularModeAmplitudeCoefficientCLM (γ : ℝ≥0) (N : ℕ) :
    (Fin 2 → LittleContourSpace γ) →L[ℝ] CircularFourierAmplitudes :=
  (circularModeNormalCoefficientCLM γ N).prod (circularModeTangentCoefficientCLM γ N)

theorem circularAngularModeProjectionCLM_eq_normalMode {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : γ ≤ 1) (N : ℕ) (H : Fin 2 → LittleContourSpace γ) :
    circularAngularModeProjectionCLM hγ hγ1 ((N + 2 : ℕ) : ℤ) H =
      circularNormalModeLittle hγ hγ1 N
        (circularModeNormalCoefficientCLM γ N H) (circularModeTangentCoefficientCLM γ N H) := by
  funext i
  have hr : circularContourRadii i ≠ 0 := by
    fin_cases i <;> simp [circularContourRadii, cellA_pos.ne']
  change contourAngularModeProjectionCLM hγ hγ1 ((N + 2 : ℕ) : ℤ) (H i) = _
  rw [contourAngularModeProjectionCLM_apply]
  have hp : (1 : ℤ) + ((N + 2 : ℕ) : ℤ) = ((N + 3 : ℕ) : ℤ) := by omega
  have hn : (1 : ℤ) - ((N + 2 : ℕ) : ℤ) = -((N + 1 : ℕ) : ℤ) := by omega
  rw [hp, hn]
  change _ = littleContourFourierMode hγ hγ1 ((N + 3 : ℕ) : ℤ)
    (circularNormalModePlus (circularContourRadii i)
      (littleContourModeNormalCoefficientCLM γ (circularContourRadii i) N (H i))
      (littleContourModeTangentCoefficientCLM γ (circularContourRadii i) N (H i))) +
    littleContourFourierMode hγ hγ1 (-((N + 1 : ℕ) : ℤ))
    (circularNormalModeMinus (circularContourRadii i)
      (littleContourModeNormalCoefficientCLM γ (circularContourRadii i) N (H i))
      (littleContourModeTangentCoefficientCLM γ (circularContourRadii i) N (H i)))
  rw [littleContourModeNormalCoefficientCLM_apply, littleContourModeTangentCoefficientCLM_apply,
    circularFourthModePlus_reconstruct hr, circularFourthModeMinus_reconstruct hr]

theorem littleContourFourierCoefficient_circularNormalMode {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : γ ≤ 1) (N : ℕ) (η τ : CircularFourierVector) (i : Fin 2) (k : ℤ) :
    littleContourFourierCoefficient γ k (circularNormalModeLittle hγ hγ1 N η τ i) =
      (if ((N + 3 : ℕ) : ℤ) = k then circularNormalModePlus (circularContourRadii i) (η i) (τ i) else 0) +
      (if -((N + 1 : ℕ) : ℤ) = k then circularNormalModeMinus (circularContourRadii i) (η i) (τ i) else 0) := by
  change littleContourFourierCoefficientCLM γ k (_ + _) = _
  rw [map_add]
  simp only [littleContourFourierCoefficientCLM_apply, littleContourFourierCoefficient_fourierMode]

theorem circularModeNormalCoefficientCLM_normalMode {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : γ ≤ 1) (N : ℕ) (η τ : CircularFourierVector) :
    circularModeNormalCoefficientCLM γ N (circularNormalModeLittle hγ hγ1 N η τ) = η := by
  funext i
  have hr : (circularContourRadii i : ℂ) ≠ 0 := by
    apply Complex.ofReal_ne_zero.mpr
    fin_cases i <;> simp [circularContourRadii, cellA_pos.ne']
  change littleContourModeNormalCoefficientCLM γ (circularContourRadii i) N
    (circularNormalModeLittle hγ hγ1 N η τ i) = _
  rw [littleContourModeNormalCoefficientCLM_apply]
  have hne : ((N + 3 : ℕ) : ℤ) ≠ -((N + 1 : ℕ) : ℤ) := by omega
  simp only [littleContourFourierCoefficient_circularNormalMode, if_pos rfl, if_neg hne,
    if_neg (Ne.symm hne), ite_true, ite_false, add_zero, zero_add]
  simp only [circularNormalModePlus, circularNormalModeMinus, map_mul, map_add, map_div₀,
    conj_ofReal, conj_ofNat, conj_conj, conj_I]
  field_simp [hr]
  ring

theorem circularModeTangentCoefficientCLM_normalMode {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : γ ≤ 1) (N : ℕ) (η τ : CircularFourierVector) :
    circularModeTangentCoefficientCLM γ N (circularNormalModeLittle hγ hγ1 N η τ) = τ := by
  funext i
  have hr : (circularContourRadii i : ℂ) ≠ 0 := by
    apply Complex.ofReal_ne_zero.mpr
    fin_cases i <;> simp [circularContourRadii, cellA_pos.ne']
  change littleContourModeTangentCoefficientCLM γ (circularContourRadii i) N
    (circularNormalModeLittle hγ hγ1 N η τ i) = _
  rw [littleContourModeTangentCoefficientCLM_apply]
  have hne : ((N + 3 : ℕ) : ℤ) ≠ -((N + 1 : ℕ) : ℤ) := by omega
  simp only [littleContourFourierCoefficient_circularNormalMode, if_pos rfl, if_neg hne,
    if_neg (Ne.symm hne), ite_true, ite_false, add_zero, zero_add]
  simp only [circularNormalModePlus, circularNormalModeMinus, map_mul, map_add, map_div₀,
    conj_ofReal, conj_ofNat, conj_conj, conj_I]
  field_simp [hr]
  ring_nf
  simp only [I_sq]
  ring

theorem circularModeAmplitudeCoefficientCLM_normalMode {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : γ ≤ 1) (N : ℕ) (p : CircularFourierAmplitudes) :
    circularModeAmplitudeCoefficientCLM γ N (circularNormalModeLittle hγ hγ1 N p.1 p.2) = p := by
  apply Prod.ext
  · exact circularModeNormalCoefficientCLM_normalMode hγ hγ1 N p.1 p.2
  · exact circularModeTangentCoefficientCLM_normalMode hγ hγ1 N p.1 p.2

theorem circularModeAmplitudeCoefficientCLM_projection {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : γ ≤ 1) (N : ℕ) (H : Fin 2 → LittleContourSpace γ) :
    circularModeAmplitudeCoefficientCLM γ N
      (circularAngularModeProjectionCLM hγ hγ1 ((N + 2 : ℕ) : ℤ) H) =
        circularModeAmplitudeCoefficientCLM γ N H := by
  rw [circularAngularModeProjectionCLM_eq_normalMode]
  apply Prod.ext
  · exact circularModeNormalCoefficientCLM_normalMode hγ hγ1 N _ _
  · exact circularModeTangentCoefficientCLM_normalMode hγ hγ1 N _ _

theorem circularPeriod_derivative_all_mode_coordinates {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1) {ρ : ℝ} (hρ : 0 < ρ)
    {X : (Fin 2 → LittleContourSpace γ) → ℝ → Fin 2 → LittleContourSpace γ}
    (hX : IsBanachFlowOn (circularBanachField hγ hγ1) (circularBanachDomain hγ hγ1)
      (ball (littleCircularReference hγ hγ1) ρ) period X)
    (hd : DifferentiableAt ℝ (fun W => X W period) (littleCircularReference hγ hγ1))
    (N : ℕ) (H : Fin 2 → LittleContourSpace γ) :
    circularModeAmplitudeCoefficientCLM γ N
        (fderiv ℝ (fun W => X W period) (littleCircularReference hγ hγ1) H) =
      circularAmplitudeLinearFlow N (circularModeAmplitudeCoefficientCLM γ N H) period := by
  have hγle : γ ≤ 1 := by exact_mod_cast hγ1.le
  let D := fderiv ℝ (fun W => X W period) (littleCircularReference hγ hγ1)
  let P := circularAngularModeProjectionCLM hγ hγle ((N + 2 : ℕ) : ℤ)
  have he : D (P H) = P (D H) := congrArg (fun A => A H)
    (circularPeriod_derivative_angularProjection_commute hγ hγ1 hρ hX hd ((N + 2 : ℕ) : ℤ))
  change circularModeAmplitudeCoefficientCLM γ N (D H) = _
  rw [← circularModeAmplitudeCoefficientCLM_projection hγ hγle N (D H), ← he]
  dsimp only [D, P]
  rw [circularAngularModeProjectionCLM_eq_normalMode hγ hγle N H]
  have hblock := circularPeriod_derivative_Fourier_block hγ hγ1 hρ hX N
    (circularModeNormalCoefficientCLM γ N H) (circularModeTangentCoefficientCLM γ N H)
  change fderiv ℝ (fun W => X W period) (littleCircularReference hγ hγ1)
      (circularNormalModeLittle hγ hγle N
        (circularModeNormalCoefficientCLM γ N H) (circularModeTangentCoefficientCLM γ N H)) =
    circularNormalModeLittle hγ hγle N
      (circularNormalLinearFlow N (circularModeNormalCoefficientCLM γ N H) period)
      (circularAmplitudeLinearFlow N
        (circularModeNormalCoefficientCLM γ N H, circularModeTangentCoefficientCLM γ N H) period).2
    at hblock
  rw [hblock]
  apply Prod.ext
  · change circularModeNormalCoefficientCLM γ N (circularNormalModeLittle hγ hγle N _ _) = _
    rw [circularModeNormalCoefficientCLM_normalMode]
    exact (circularAmplitudeLinearFlow_normal N (circularModeAmplitudeCoefficientCLM γ N H)
      (show 0 ≤ period by unfold period; positivity)).symm
  · change circularModeTangentCoefficientCLM γ N (circularNormalModeLittle hγ hγle N _ _) = _
    rw [circularModeTangentCoefficientCLM_normalMode]
    rfl

end Euler2D

end
