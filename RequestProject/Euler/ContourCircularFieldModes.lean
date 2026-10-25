module

public import RequestProject.Euler.ContourCircularModeSelf
public import RequestProject.Euler.ContourCircularModeDerivative
public import RequestProject.Euler.FiniteContourFirstVariation
public import RequestProject.Euler.CircularBanachDynamics

/-! The actual finite contour field on Fourier perturbations, and the
actual little-space normal/tangential perturbations of the circular cell. -/

@[expose] public section

noncomputable section

open Complex Set
open scoped NNReal ContDiff BigOperators ComplexConjugate

namespace Euler2D

local instance (priority := 2000) circularFieldModeC1_group (γ : ℝ≥0) :
    NormedAddCommGroup (ContourC1Space γ) := Submodule.normedAddCommGroup (contourC1GraphSubmodule γ)
local instance (priority := 2000) circularFieldModeC1_space (γ : ℝ≥0) :
    NormedSpace ℝ (ContourC1Space γ) := Submodule.normedSpace (contourC1GraphSubmodule γ)
local instance (priority := 2000) circularFieldModeLittle_group (γ : ℝ≥0) :
    NormedAddCommGroup (LittleContourSpace γ) := Submodule.normedAddCommGroup (LittleContourSpace γ)
local instance (priority := 2000) circularFieldModeLittle_space (γ : ℝ≥0) :
    NormedSpace ℝ (LittleContourSpace γ) := Submodule.normedSpace (LittleContourSpace γ)

set_option maxHeartbeats 600000 in
theorem circularInteractionDerivative_reference_mode {γ : ℝ≥0} {ι : Type} [Fintype ι]
    (hγ : 0 < γ) (hγ1 : γ ≤ 1) (r : ι → ℝ) (hr : ∀ i, 0 < r i)
    (hinj : Function.Injective r) (n : ℤ) (a : ι → ℂ) (i j : ι) :
    contourC1InteractionDerivative i j 0 (fun k => circularReferenceContourC1 hγ hγ1 (r k))
      (fun k => circularFourierContourC1 hγ hγ1 n (a k)) =
        circularContourModeVariation (r i) (r j) n (a i) (a j) := by
  classical
  by_cases hij : i = j
  · subst j
    rw [contourC1InteractionDerivative, if_pos rfl]
    change fderiv ℝ (fun W : ContourC1Space γ => ContourC1Space.selfLogIntegral W 0)
      (circularReferenceContourC1 hγ hγ1 (r i)) (circularFourierContourC1 hγ hγ1 n (a i)) = _
    exact fderiv_selfLogIntegral_reference_mode_zero hγ hγ1 (hr i) n (a i)
  · rw [contourC1InteractionDerivative, if_neg hij]
    change fderiv ℝ (fun p : ContourC1Space γ × ContourC1Space γ => contourC1CrossLogIntegral p.1 p.2 0)
      (circularReferenceContourC1 hγ hγ1 (r i), circularReferenceContourC1 hγ hγ1 (r j))
      (circularFourierContourC1 hγ hγ1 n (a i), circularFourierContourC1 hγ hγ1 n (a j)) = _
    exact fderiv_crossLogIntegral_reference_mode_zero hγ hγ1 (hr i) (hr j)
      (fun h => hij (hinj h)) n (a i) (a j)

theorem circularBoundaryDerivative_reference_mode {γ : ℝ≥0} {ι : Type} [Fintype ι]
    (hγ : 0 < γ) (hγ1 : γ ≤ 1) (r : ι → ℝ) (hr : ∀ i, 0 < r i)
    (hinj : Function.Injective r) (g : ι → ℝ) (n : ℤ) (a : ι → ℂ) (i : ι) :
    contourC1BoundaryDerivative g (fun k => circularReferenceContourC1 hγ hγ1 (r k)) i 0
      (fun k => circularFourierContourC1 hγ hγ1 n (a k)) =
        (-1 / (2 * Real.pi) : ℝ) • ∑ j, g j • circularContourModeVariation (r i) (r j) n (a i) (a j) := by
  unfold contourC1BoundaryDerivative
  rw [ContinuousLinearMap.smul_apply, ContinuousLinearMap.sum_apply]
  simp only [ContinuousLinearMap.smul_apply,
    circularInteractionDerivative_reference_mode hγ hγ1 r hr hinj n a i]

def circularNormalModePlus (r : ℝ) (η τ : ℂ) : ℂ := (r : ℂ) / 2 * (η + I * τ)
def circularNormalModeMinus (r : ℝ) (η τ : ℂ) : ℂ := (r : ℂ) / 2 * (conj η + I * conj τ)

def circularNormalModeLittle {γ : ℝ≥0} (hγ : 0 < γ) (hγ1 : γ ≤ 1)
    (N : ℕ) (η τ : Fin 2 → ℂ) (i : Fin 2) : LittleContourSpace γ :=
  littleContourFourierMode hγ hγ1 ((N + 3 : ℕ) : ℤ)
    (circularNormalModePlus (circularContourRadii i) (η i) (τ i)) +
  littleContourFourierMode hγ hγ1 (-((N + 1 : ℕ) : ℤ))
    (circularNormalModeMinus (circularContourRadii i) (η i) (τ i))

def circularNormalModeC1 {γ : ℝ≥0} (hγ : 0 < γ) (hγ1 : γ ≤ 1)
    (N : ℕ) (η τ : Fin 2 → ℂ) (i : Fin 2) : ContourC1Space γ :=
  (circularNormalModeLittle hγ hγ1 N η τ i).val

theorem circularNormalModeC1_eq_add {γ : ℝ≥0} (hγ : 0 < γ) (hγ1 : γ ≤ 1)
    (N : ℕ) (η τ : Fin 2 → ℂ) :
    circularNormalModeC1 hγ hγ1 N η τ =
      (fun i => circularFourierContourC1 hγ hγ1 ((N + 3 : ℕ) : ℤ)
        (circularNormalModePlus (circularContourRadii i) (η i) (τ i))) +
      (fun i => circularFourierContourC1 hγ hγ1 (-((N + 1 : ℕ) : ℤ))
        (circularNormalModeMinus (circularContourRadii i) (η i) (τ i))) := rfl

theorem lift_circularNormalModeLittle {γ : ℝ≥0} (hγ : 0 < γ) (hγ1 : γ ≤ 1)
    (N : ℕ) (η τ : Fin 2 → ℂ) (i : Fin 2) (θ : ℝ) :
    LittleContourSpace.lift γ (circularNormalModeLittle hγ hγ1 N η τ i) θ =
      refCircle (circularContourRadii i) θ *
        (((η i * contourCircleCharacter ((N + 2 : ℕ) : ℤ) θ).re : ℂ) +
          I * ((τ i * contourCircleCharacter ((N + 2 : ℕ) : ℤ) θ).re : ℂ)) := by
  change circularNormalModePlus (circularContourRadii i) (η i) (τ i) *
      contourCircleCharacter ((N + 3 : ℕ) : ℤ) θ +
    circularNormalModeMinus (circularContourRadii i) (η i) (τ i) *
      contourCircleCharacter (-((N + 1 : ℕ) : ℤ)) θ = _
  have href : refCircle (circularContourRadii i) θ =
      (circularContourRadii i : ℂ) * contourCircleCharacter 1 θ := by
    simp only [refCircle, contourCircleCharacter, Int.cast_one, one_mul]
  rw [href, Complex.re_eq_add_conj, Complex.re_eq_add_conj,
    show ((N + 3 : ℕ) : ℤ) = 1 + ((N + 2 : ℕ) : ℤ) by omega,
    show -((N + 1 : ℕ) : ℤ) = 1 + -((N + 2 : ℕ) : ℤ) by omega,
    ← contourCircleCharacter_mul 1 ((N + 2 : ℕ) : ℤ) θ,
    ← contourCircleCharacter_mul 1 (-((N + 2 : ℕ) : ℤ)) θ]
  simp only [map_mul, conj_contourCircleCharacter, circularNormalModePlus, circularNormalModeMinus]
  ring

end Euler2D

end
