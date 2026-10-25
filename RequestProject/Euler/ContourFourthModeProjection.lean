module

public import RequestProject.Euler.ContourFourierModeCalculus
public import RequestProject.Euler.CircularFourierConstraints

/-! Genuine normalized Fourier coefficient functionals and the bounded
fourth-mode projection on the original little contour Banach space. -/

@[expose] public section

noncomputable section

open Complex Set Filter Topology Metric MeasureTheory
open scoped NNReal ComplexConjugate ContDiff

namespace Euler2D

local instance (priority := 2000) fourthProjectionLittle_group (γ : ℝ≥0) :
    NormedAddCommGroup (LittleContourSpace γ) := Submodule.normedAddCommGroup (LittleContourSpace γ)
local instance (priority := 2000) fourthProjectionLittle_space (γ : ℝ≥0) :
    NormedSpace ℝ (LittleContourSpace γ) := Submodule.normedSpace (LittleContourSpace γ)

def littleContourFourierCoefficient (γ : ℝ≥0) (k : ℤ) (H : LittleContourSpace γ) : ℂ :=
  ((2 * Real.pi : ℝ) : ℂ)⁻¹ * ∫ θ in (0 : ℝ)..2 * Real.pi,
    LittleContourSpace.lift γ H θ * contourCircleCharacter (-k) θ

theorem intervalIntegrable_littleContour_fourier {γ : ℝ≥0}
    (H : LittleContourSpace γ) (k : ℤ) :
    IntervalIntegrable (fun θ => LittleContourSpace.lift γ H θ * contourCircleCharacter k θ)
      volume 0 (2 * Real.pi) :=
  ((LittleContourSpace.contDiff_lift H).continuous.mul
    (continuous_contourCircleCharacter k)).intervalIntegrable _ _

theorem norm_littleContourFourierCoefficient_le {γ : ℝ≥0}
    (k : ℤ) (H : LittleContourSpace γ) : ‖littleContourFourierCoefficient γ k H‖ ≤ ‖H‖ := by
  have hp : 0 < 2 * Real.pi := by positivity
  have hI : ‖∫ θ in (0 : ℝ)..2 * Real.pi,
      LittleContourSpace.lift γ H θ * contourCircleCharacter (-k) θ‖ ≤ ‖H‖ * (2 * Real.pi) := by
    have hb := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ))
      (b := 2 * Real.pi) (C := ‖H‖)
      (f := fun θ : ℝ => LittleContourSpace.lift γ H θ * contourCircleCharacter (-k) θ)
      (fun θ _ => by
        rw [norm_mul, norm_contourCircleCharacter, mul_one]
        exact LittleContourSpace.norm_eval_le H (θ : ContourCircle))
    simpa only [sub_zero, abs_of_pos hp] using hb
  unfold littleContourFourierCoefficient
  rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hp]
  calc
    (2 * Real.pi)⁻¹ * ‖∫ θ in (0 : ℝ)..2 * Real.pi,
        LittleContourSpace.lift γ H θ * contourCircleCharacter (-k) θ‖ ≤
        (2 * Real.pi)⁻¹ * (‖H‖ * (2 * Real.pi)) :=
      mul_le_mul_of_nonneg_left hI (inv_nonneg.mpr hp.le)
    _ = ‖H‖ := by field_simp

/-- The actual coefficient integral is a bounded real linear functional
in the original little C¹ Hölder norm, with operator norm at most one. -/
def littleContourFourierCoefficientCLM (γ : ℝ≥0) (k : ℤ) :
    LittleContourSpace γ →L[ℝ] ℂ :=
  LinearMap.mkContinuous
    { toFun := littleContourFourierCoefficient γ k
      map_add' := fun H G => by
        unfold littleContourFourierCoefficient
        simp only [LittleContourSpace.lift_add, Pi.add_apply, add_mul]
        rw [intervalIntegral.integral_add
          (intervalIntegrable_littleContour_fourier H (-k))
          (intervalIntegrable_littleContour_fourier G (-k))]
        ring
      map_smul' := fun c H => by
        unfold littleContourFourierCoefficient
        simp only [LittleContourSpace.lift_smul, Pi.smul_apply, Complex.real_smul,
          RingHom.id_apply]
        have he (θ : ℝ) : (c : ℂ) * LittleContourSpace.lift γ H θ * contourCircleCharacter (-k) θ =
            (c : ℂ) * (LittleContourSpace.lift γ H θ * contourCircleCharacter (-k) θ) := by ring
        simp_rw [he]
        rw [intervalIntegral.integral_const_mul]
        ring }
    1 (fun H => by
      change ‖littleContourFourierCoefficient γ k H‖ ≤ 1 * ‖H‖
      simpa only [one_mul] using norm_littleContourFourierCoefficient_le k H)

@[simp] theorem littleContourFourierCoefficientCLM_apply {γ : ℝ≥0}
    (k : ℤ) (H : LittleContourSpace γ) :
    littleContourFourierCoefficientCLM γ k H = littleContourFourierCoefficient γ k H := rfl

theorem norm_littleContourFourierCoefficientCLM_le (γ : ℝ≥0) (k : ℤ) :
    ‖littleContourFourierCoefficientCLM γ k‖ ≤ 1 := by
  apply (littleContourFourierCoefficientCLM γ k).opNorm_le_bound (by norm_num)
  intro H
  change ‖littleContourFourierCoefficient γ k H‖ ≤ 1 * ‖H‖
  rw [one_mul]
  exact norm_littleContourFourierCoefficient_le k H

theorem littleContourFourierCoefficient_fourierMode {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : γ ≤ 1) (k n : ℤ) (a : ℂ) :
    littleContourFourierCoefficient γ k (littleContourFourierMode hγ hγ1 n a) =
      if n = k then a else 0 := by
  unfold littleContourFourierCoefficient
  simp only [lift_littleContourFourierMode]
  have he (θ : ℝ) : (a * contourCircleCharacter n θ) * contourCircleCharacter (-k) θ =
      a * contourCircleCharacter (n - k) θ := by
    rw [mul_assoc, contourCircleCharacter_mul]
    congr 2
  simp_rw [he]
  rw [intervalIntegral.integral_const_mul, integral_contourCircleCharacter]
  by_cases hnk : n = k
  · subst n
    simp only [sub_self, if_pos rfl]
    have hp : ((2 * Real.pi : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.mpr (by positivity)
    push_cast at hp ⊢
    field_simp
  · rw [if_neg (sub_ne_zero.mpr hnk), if_neg hnk]
    ring

/-- The genuine fourth normal/tangential Fourier block consists exactly
of the two complex contour frequencies 5 and -3. -/
def contourFourthModeProjectionCLM {γ : ℝ≥0} (hγ : 0 < γ) (hγ1 : γ ≤ 1) :
    LittleContourSpace γ →L[ℝ] LittleContourSpace γ :=
  (littleContourFourierModeCLM hγ hγ1 5).comp (littleContourFourierCoefficientCLM γ 5) +
    (littleContourFourierModeCLM hγ hγ1 (-3)).comp (littleContourFourierCoefficientCLM γ (-3))

theorem contourFourthModeProjectionCLM_apply {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : γ ≤ 1) (H : LittleContourSpace γ) :
    contourFourthModeProjectionCLM hγ hγ1 H =
      littleContourFourierMode hγ hγ1 5 (littleContourFourierCoefficient γ 5 H) +
      littleContourFourierMode hγ hγ1 (-3) (littleContourFourierCoefficient γ (-3) H) := by
  simp only [contourFourthModeProjectionCLM, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.comp_apply, littleContourFourierModeCLM_apply,
    littleContourFourierCoefficientCLM_apply]

theorem contourFourthModeProjectionCLM_fourierMode_five {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : γ ≤ 1) (a : ℂ) :
    contourFourthModeProjectionCLM hγ hγ1 (littleContourFourierMode hγ hγ1 5 a) =
      littleContourFourierMode hγ hγ1 5 a := by
  rw [contourFourthModeProjectionCLM_apply]
  norm_num only [littleContourFourierCoefficient_fourierMode]
  simp only [ite_true, ite_false]
  rw [← littleContourFourierModeCLM_apply hγ hγ1 (-3) 0, map_zero, add_zero]

theorem contourFourthModeProjectionCLM_fourierMode_neg_three {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : γ ≤ 1) (a : ℂ) :
    contourFourthModeProjectionCLM hγ hγ1 (littleContourFourierMode hγ hγ1 (-3) a) =
      littleContourFourierMode hγ hγ1 (-3) a := by
  rw [contourFourthModeProjectionCLM_apply]
  norm_num only [littleContourFourierCoefficient_fourierMode]
  simp only [ite_true, ite_false]
  rw [← littleContourFourierModeCLM_apply hγ hγ1 5 0, map_zero, zero_add]

theorem contourFourthModeProjectionCLM_idempotent {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : γ ≤ 1) (H : LittleContourSpace γ) :
    contourFourthModeProjectionCLM hγ hγ1 (contourFourthModeProjectionCLM hγ hγ1 H) =
      contourFourthModeProjectionCLM hγ hγ1 H := by
  rw [contourFourthModeProjectionCLM_apply hγ hγ1 H, map_add,
    contourFourthModeProjectionCLM_fourierMode_five,
    contourFourthModeProjectionCLM_fourierMode_neg_three]

def littleContourFourthNormalCoefficientCLM (γ : ℝ≥0) (r : ℝ) :
    LittleContourSpace γ →L[ℝ] ℂ :=
  ((ContinuousLinearMap.mul ℝ ℂ) ((r : ℂ)⁻¹)).comp
    (littleContourFourierCoefficientCLM γ 5 +
      Complex.conjCLE.toContinuousLinearMap.comp (littleContourFourierCoefficientCLM γ (-3)))

def littleContourFourthTangentCoefficientCLM (γ : ℝ≥0) (r : ℝ) :
    LittleContourSpace γ →L[ℝ] ℂ :=
  ((ContinuousLinearMap.mul ℝ ℂ) (-I / (r : ℂ))).comp
    (littleContourFourierCoefficientCLM γ 5 -
      Complex.conjCLE.toContinuousLinearMap.comp (littleContourFourierCoefficientCLM γ (-3)))

theorem littleContourFourthNormalCoefficientCLM_apply {γ : ℝ≥0}
    (r : ℝ) (H : LittleContourSpace γ) :
    littleContourFourthNormalCoefficientCLM γ r H =
      (littleContourFourierCoefficient γ 5 H + conj (littleContourFourierCoefficient γ (-3) H)) /
        (r : ℂ) := by
  change (r : ℂ)⁻¹ *
    (littleContourFourierCoefficient γ 5 H + conj (littleContourFourierCoefficient γ (-3) H)) = _
  rw [div_eq_mul_inv, mul_comm]

theorem littleContourFourthTangentCoefficientCLM_apply {γ : ℝ≥0}
    (r : ℝ) (H : LittleContourSpace γ) :
    littleContourFourthTangentCoefficientCLM γ r H =
      (-I / (r : ℂ)) *
        (littleContourFourierCoefficient γ 5 H - conj (littleContourFourierCoefficient γ (-3) H)) := rfl

theorem circularFourthModePlus_reconstruct {r : ℝ} (hr : r ≠ 0) (a b : ℂ) :
    circularNormalModePlus r ((a + conj b) / (r : ℂ))
      ((-I / (r : ℂ)) * (a - conj b)) = a := by
  have hrC : (r : ℂ) ≠ 0 := ofReal_ne_zero.mpr hr
  unfold circularNormalModePlus
  field_simp
  ring_nf
  simp only [I_sq]
  ring

theorem circularFourthModeMinus_reconstruct {r : ℝ} (hr : r ≠ 0) (a b : ℂ) :
    circularNormalModeMinus r ((a + conj b) / (r : ℂ))
      ((-I / (r : ℂ)) * (a - conj b)) = b := by
  have hrC : (r : ℂ) ≠ 0 := ofReal_ne_zero.mpr hr
  unfold circularNormalModeMinus
  simp only [map_div₀, map_add, map_sub, map_mul, map_neg, conj_ofReal, conj_I, conj_conj]
  field_simp
  ring_nf
  simp only [I_sq]
  ring

def circularFourthNormalCoefficientCLM (γ : ℝ≥0) :
    (Fin 2 → LittleContourSpace γ) →L[ℝ] (Fin 2 → ℂ) :=
  ContinuousLinearMap.pi fun i =>
    (littleContourFourthNormalCoefficientCLM γ (circularContourRadii i)).comp
      (ContinuousLinearMap.proj i)

def circularFourthTangentCoefficientCLM (γ : ℝ≥0) :
    (Fin 2 → LittleContourSpace γ) →L[ℝ] (Fin 2 → ℂ) :=
  ContinuousLinearMap.pi fun i =>
    (littleContourFourthTangentCoefficientCLM γ (circularContourRadii i)).comp
      (ContinuousLinearMap.proj i)

def circularFourthModeProjectionCLM {γ : ℝ≥0} (hγ : 0 < γ) (hγ1 : γ ≤ 1) :
    (Fin 2 → LittleContourSpace γ) →L[ℝ] (Fin 2 → LittleContourSpace γ) :=
  ContinuousLinearMap.pi fun i =>
    (contourFourthModeProjectionCLM hγ hγ1).comp (ContinuousLinearMap.proj i)

theorem circularFourthModeProjectionCLM_eq_normalMode {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : γ ≤ 1) (H : Fin 2 → LittleContourSpace γ) :
    circularFourthModeProjectionCLM hγ hγ1 H =
      circularNormalModeLittle hγ hγ1 2
        (circularFourthNormalCoefficientCLM γ H) (circularFourthTangentCoefficientCLM γ H) := by
  funext i
  have hr : circularContourRadii i ≠ 0 := by
    fin_cases i <;> simp [circularContourRadii, cellA_pos.ne']
  change contourFourthModeProjectionCLM hγ hγ1 (H i) = _
  rw [contourFourthModeProjectionCLM_apply]
  change _ = littleContourFourierMode hγ hγ1 5
    (circularNormalModePlus (circularContourRadii i)
      (littleContourFourthNormalCoefficientCLM γ (circularContourRadii i) (H i))
      (littleContourFourthTangentCoefficientCLM γ (circularContourRadii i) (H i))) +
    littleContourFourierMode hγ hγ1 (-3)
    (circularNormalModeMinus (circularContourRadii i)
      (littleContourFourthNormalCoefficientCLM γ (circularContourRadii i) (H i))
      (littleContourFourthTangentCoefficientCLM γ (circularContourRadii i) (H i)))
  rw [littleContourFourthNormalCoefficientCLM_apply, littleContourFourthTangentCoefficientCLM_apply,
    circularFourthModePlus_reconstruct hr, circularFourthModeMinus_reconstruct hr]

theorem circularFourthModeProjectionCLM_normalMode {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : γ ≤ 1) (η τ : Fin 2 → ℂ) :
    circularFourthModeProjectionCLM hγ hγ1 (circularNormalModeLittle hγ hγ1 2 η τ) =
      circularNormalModeLittle hγ hγ1 2 η τ := by
  funext i
  change contourFourthModeProjectionCLM hγ hγ1
    (littleContourFourierMode hγ hγ1 5 _ + littleContourFourierMode hγ hγ1 (-3) _) = _
  rw [map_add, contourFourthModeProjectionCLM_fourierMode_five,
    contourFourthModeProjectionCLM_fourierMode_neg_three]
  rfl

theorem circularFourthModeProjectionCLM_idempotent {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : γ ≤ 1) (H : Fin 2 → LittleContourSpace γ) :
    circularFourthModeProjectionCLM hγ hγ1 (circularFourthModeProjectionCLM hγ hγ1 H) =
      circularFourthModeProjectionCLM hγ hγ1 H := by
  funext i
  exact contourFourthModeProjectionCLM_idempotent hγ hγ1 (H i)

theorem circularFourthModeProjectionCLM_mem_fourfold_area {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : γ ≤ 1) (H : Fin 2 → LittleContourSpace γ) (i : Fin 2) :
    circularFourthModeProjectionCLM hγ hγ1 H i ∈
      fourfoldLittleContourSubmodule γ ⊓ LittleContourAreaConstraint γ (circularContourRadii i) := by
  rw [circularFourthModeProjectionCLM_eq_normalMode]
  exact circularFourthModeLittle_mem_fourfold_area hγ hγ1 _ _ i

theorem isClosed_range_circularFourthModeProjectionCLM {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : γ ≤ 1) :
    IsClosed (Set.range (circularFourthModeProjectionCLM hγ hγ1)) := by
  have he : Set.range (circularFourthModeProjectionCLM hγ hγ1) =
      {H | circularFourthModeProjectionCLM hγ hγ1 H = H} := by
    ext H
    constructor
    · rintro ⟨G, rfl⟩
      exact circularFourthModeProjectionCLM_idempotent hγ hγ1 G
    · intro hH
      exact ⟨H, hH⟩
  rw [he]
  exact isClosed_eq (circularFourthModeProjectionCLM hγ hγ1).continuous continuous_id

theorem norm_contourFourthModeProjectionCLM_le {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : γ ≤ 1) :
    ‖contourFourthModeProjectionCLM hγ hγ1‖ ≤
      ‖littleContourFourierModeCLM hγ hγ1 5‖ + ‖littleContourFourierModeCLM hγ hγ1 (-3)‖ := by
  unfold contourFourthModeProjectionCLM
  calc
    ‖(littleContourFourierModeCLM hγ hγ1 5).comp (littleContourFourierCoefficientCLM γ 5) +
        (littleContourFourierModeCLM hγ hγ1 (-3)).comp (littleContourFourierCoefficientCLM γ (-3))‖ ≤
      ‖(littleContourFourierModeCLM hγ hγ1 5).comp (littleContourFourierCoefficientCLM γ 5)‖ +
        ‖(littleContourFourierModeCLM hγ hγ1 (-3)).comp (littleContourFourierCoefficientCLM γ (-3))‖ :=
      norm_add_le _ _
    _ ≤ ‖littleContourFourierModeCLM hγ hγ1 5‖ * ‖littleContourFourierCoefficientCLM γ 5‖ +
        ‖littleContourFourierModeCLM hγ hγ1 (-3)‖ * ‖littleContourFourierCoefficientCLM γ (-3)‖ :=
      add_le_add (ContinuousLinearMap.opNorm_comp_le _ _) (ContinuousLinearMap.opNorm_comp_le _ _)
    _ ≤ ‖littleContourFourierModeCLM hγ hγ1 5‖ * 1 +
        ‖littleContourFourierModeCLM hγ hγ1 (-3)‖ * 1 :=
      add_le_add
        (mul_le_mul_of_nonneg_left (norm_littleContourFourierCoefficientCLM_le γ 5) (norm_nonneg _))
        (mul_le_mul_of_nonneg_left (norm_littleContourFourierCoefficientCLM_le γ (-3)) (norm_nonneg _))
    _ = _ := by simp only [mul_one]

theorem isCompl_range_ker_circularFourthModeProjectionCLM {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : γ ≤ 1) :
    IsCompl (circularFourthModeProjectionCLM hγ hγ1).toLinearMap.range
      (circularFourthModeProjectionCLM hγ hγ1).ker := by
  have hp : IsIdempotentElem (circularFourthModeProjectionCLM hγ hγ1).toLinearMap := by
    apply LinearMap.ext
    intro H
    exact circularFourthModeProjectionCLM_idempotent hγ hγ1 H
  exact LinearMap.IsIdempotentElem.isCompl hp

theorem isClosed_ker_circularFourthModeProjectionCLM {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : γ ≤ 1) :
    IsClosed ((circularFourthModeProjectionCLM hγ hγ1).ker : Set (Fin 2 → LittleContourSpace γ)) :=
  (circularFourthModeProjectionCLM hγ hγ1).isClosed_ker

theorem littleContourFourierCoefficient_circularFourthMode {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : γ ≤ 1) (η τ : Fin 2 → ℂ) (i : Fin 2) (k : ℤ) :
    littleContourFourierCoefficient γ k (circularNormalModeLittle hγ hγ1 2 η τ i) =
      (if (5 : ℤ) = k then circularNormalModePlus (circularContourRadii i) (η i) (τ i) else 0) +
      (if (-3 : ℤ) = k then circularNormalModeMinus (circularContourRadii i) (η i) (τ i) else 0) := by
  change littleContourFourierCoefficientCLM γ k
    (littleContourFourierMode hγ hγ1 5 _ + littleContourFourierMode hγ hγ1 (-3) _) = _
  rw [map_add]
  simp only [littleContourFourierCoefficientCLM_apply, littleContourFourierCoefficient_fourierMode]

theorem circularFourthNormalCoefficientCLM_normalMode {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : γ ≤ 1) (η τ : Fin 2 → ℂ) :
    circularFourthNormalCoefficientCLM γ (circularNormalModeLittle hγ hγ1 2 η τ) = η := by
  funext i
  have hr : circularContourRadii i ≠ 0 := by
    fin_cases i <;> simp [circularContourRadii, cellA_pos.ne']
  have hrC : (circularContourRadii i : ℂ) ≠ 0 := ofReal_ne_zero.mpr hr
  change littleContourFourthNormalCoefficientCLM γ (circularContourRadii i)
    (circularNormalModeLittle hγ hγ1 2 η τ i) = η i
  rw [littleContourFourthNormalCoefficientCLM_apply]
  simp only [littleContourFourierCoefficient_circularFourthMode]
  norm_num
  simp only [circularNormalModePlus, circularNormalModeMinus,
    map_mul, map_add, map_div₀, map_ofNat, conj_ofReal, conj_I, conj_conj]
  field_simp
  ring

theorem circularFourthTangentCoefficientCLM_normalMode {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : γ ≤ 1) (η τ : Fin 2 → ℂ) :
    circularFourthTangentCoefficientCLM γ (circularNormalModeLittle hγ hγ1 2 η τ) = τ := by
  funext i
  have hr : circularContourRadii i ≠ 0 := by
    fin_cases i <;> simp [circularContourRadii, cellA_pos.ne']
  have hrC : (circularContourRadii i : ℂ) ≠ 0 := ofReal_ne_zero.mpr hr
  change littleContourFourthTangentCoefficientCLM γ (circularContourRadii i)
    (circularNormalModeLittle hγ hγ1 2 η τ i) = τ i
  rw [littleContourFourthTangentCoefficientCLM_apply]
  simp only [littleContourFourierCoefficient_circularFourthMode]
  norm_num
  simp only [circularNormalModePlus, circularNormalModeMinus,
    map_mul, map_add, map_div₀, map_ofNat, conj_ofReal, conj_I, conj_conj]
  field_simp
  ring_nf
  simp only [I_sq]
  ring

theorem contourFourthFrame_normal_pointwise (h : ℂ) (θ : ℝ) :
    ((contourCircleCharacter (-1) θ * h).re : ℂ) * contourCircleCharacter (-4) θ =
      (h * contourCircleCharacter (-5) θ + conj (h * contourCircleCharacter 3 θ)) / 2 := by
  rw [Complex.re_eq_add_conj]
  simp only [map_mul, conj_contourCircleCharacter]
  have h5 : contourCircleCharacter (-1) θ * contourCircleCharacter (-4) θ =
      contourCircleCharacter (-5) θ := contourCircleCharacter_mul (-1) (-4) θ
  have h3 : contourCircleCharacter 1 θ * contourCircleCharacter (-4) θ =
      contourCircleCharacter (-3) θ := contourCircleCharacter_mul 1 (-4) θ
  rw [← h5, ← h3]
  ring

theorem contourFourthFrame_tangent_pointwise (h : ℂ) (θ : ℝ) :
    ((contourCircleCharacter (-1) θ * h).im : ℂ) * contourCircleCharacter (-4) θ =
      (h * contourCircleCharacter (-5) θ - conj (h * contourCircleCharacter 3 θ)) / (2 * I) := by
  rw [Complex.im_eq_sub_conj]
  simp only [map_mul, conj_contourCircleCharacter]
  have h5 : contourCircleCharacter (-1) θ * contourCircleCharacter (-4) θ =
      contourCircleCharacter (-5) θ := contourCircleCharacter_mul (-1) (-4) θ
  have h3 : contourCircleCharacter 1 θ * contourCircleCharacter (-4) θ =
      contourCircleCharacter (-3) θ := contourCircleCharacter_mul 1 (-4) θ
  rw [← h5, ← h3]
  ring

/-- Normal amplitude extraction is exactly the physical moving-frame
real part followed by its actual fourth Fourier coefficient. -/
theorem littleContourFourthNormalCoefficientCLM_eq_frame_integral {γ : ℝ≥0}
    {r : ℝ} (hr : r ≠ 0) (H : LittleContourSpace γ) :
    littleContourFourthNormalCoefficientCLM γ r H =
      ((Real.pi * r : ℝ) : ℂ)⁻¹ * ∫ θ in (0 : ℝ)..2 * Real.pi,
        ((contourCircleCharacter (-1) θ * LittleContourSpace.lift γ H θ).re : ℂ) *
          contourCircleCharacter (-4) θ := by
  have hi5 := intervalIntegrable_littleContour_fourier H (-5)
  have hi3 := intervalIntegrable_littleContour_fourier H 3
  have hic : IntervalIntegrable
      (fun θ => conj (LittleContourSpace.lift γ H θ * contourCircleCharacter 3 θ))
      volume 0 (2 * Real.pi) :=
    (Complex.continuous_conj.comp ((LittleContourSpace.contDiff_lift H).continuous.mul
      (continuous_contourCircleCharacter 3))).intervalIntegrable _ _
  have hc := Complex.conjCLE.toContinuousLinearMap.intervalIntegral_comp_comm hi3
  change (∫ θ in (0 : ℝ)..2 * Real.pi,
    conj (LittleContourSpace.lift γ H θ * contourCircleCharacter 3 θ)) =
    conj (∫ θ in (0 : ℝ)..2 * Real.pi,
      LittleContourSpace.lift γ H θ * contourCircleCharacter 3 θ) at hc
  rw [littleContourFourthNormalCoefficientCLM_apply]
  simp_rw [contourFourthFrame_normal_pointwise]
  rw [intervalIntegral.integral_div, intervalIntegral.integral_add hi5 hic, hc]
  unfold littleContourFourierCoefficient
  simp only [neg_neg, map_mul, map_inv₀, conj_ofReal, Complex.ofReal_mul]
  have hrC : (r : ℂ) ≠ 0 := ofReal_ne_zero.mpr hr
  have hpC : (Real.pi : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  push_cast
  field_simp

/-- Tangential amplitude extraction uses the actual imaginary part in
the same moving circular frame, with the same Fourier normalization. -/
theorem littleContourFourthTangentCoefficientCLM_eq_frame_integral {γ : ℝ≥0}
    {r : ℝ} (hr : r ≠ 0) (H : LittleContourSpace γ) :
    littleContourFourthTangentCoefficientCLM γ r H =
      ((Real.pi * r : ℝ) : ℂ)⁻¹ * ∫ θ in (0 : ℝ)..2 * Real.pi,
        ((contourCircleCharacter (-1) θ * LittleContourSpace.lift γ H θ).im : ℂ) *
          contourCircleCharacter (-4) θ := by
  have hi5 := intervalIntegrable_littleContour_fourier H (-5)
  have hi3 := intervalIntegrable_littleContour_fourier H 3
  have hic : IntervalIntegrable
      (fun θ => conj (LittleContourSpace.lift γ H θ * contourCircleCharacter 3 θ))
      volume 0 (2 * Real.pi) :=
    (Complex.continuous_conj.comp ((LittleContourSpace.contDiff_lift H).continuous.mul
      (continuous_contourCircleCharacter 3))).intervalIntegrable _ _
  have hc := Complex.conjCLE.toContinuousLinearMap.intervalIntegral_comp_comm hi3
  change (∫ θ in (0 : ℝ)..2 * Real.pi,
    conj (LittleContourSpace.lift γ H θ * contourCircleCharacter 3 θ)) =
    conj (∫ θ in (0 : ℝ)..2 * Real.pi,
      LittleContourSpace.lift γ H θ * contourCircleCharacter 3 θ) at hc
  rw [littleContourFourthTangentCoefficientCLM_apply]
  simp_rw [contourFourthFrame_tangent_pointwise]
  rw [intervalIntegral.integral_div, intervalIntegral.integral_sub hi5 hic, hc]
  unfold littleContourFourierCoefficient
  simp only [neg_neg, map_mul, map_inv₀, conj_ofReal, Complex.ofReal_mul]
  have hrC : (r : ℂ) ≠ 0 := ofReal_ne_zero.mpr hr
  have hpC : (Real.pi : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  push_cast
  field_simp
  ring_nf
  simp only [I_sq]
  ring

end Euler2D

end
