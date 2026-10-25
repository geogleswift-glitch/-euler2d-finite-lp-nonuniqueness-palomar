module

public import RequestProject.Euler.ContourCircularFieldModes

/-! Rotation covariance of the actual field derivative and of the
actual normal Fourier perturbations in the original contour norm. -/

@[expose] public section

noncomputable section

open Complex Set Filter Topology
open scoped NNReal ContDiff ComplexConjugate

namespace Euler2D

local instance (priority := 2000) rotationDerivativeC1_group (γ : ℝ≥0) :
    NormedAddCommGroup (ContourC1Space γ) := Submodule.normedAddCommGroup (contourC1GraphSubmodule γ)
local instance (priority := 2000) rotationDerivativeC1_space (γ : ℝ≥0) :
    NormedSpace ℝ (ContourC1Space γ) := Submodule.normedSpace (contourC1GraphSubmodule γ)

def contourRotationFamilyC1CLM {ι : Type} [Fintype ι] (γ : ℝ≥0) (b : ℝ) :
    (ι → ContourC1Space γ) →L[ℝ] (ι → ContourC1Space γ) :=
  ContinuousLinearMap.pi (fun i => (contourRotationC1CLM γ b).comp (ContinuousLinearMap.proj i))

theorem contourC1BoundaryField_rotation {γ : ℝ≥0} {ι : Type} [Fintype ι]
    (g : ι → ℝ) (W : ι → ContourC1Space γ) (b : ℝ) (i : ι) (θ : ℝ) :
    contourC1BoundaryField g (contourRotationFamilyC1CLM γ b W) i θ =
      exp ((b : ℂ) * I) * contourC1BoundaryField g W i (θ - b) := by
  change contourBoundaryField g (fun j => ContourC1Space.lift γ (contourRotationC1 b (W j))) i θ = _
  simp_rw [contourRotationC1_lift]
  exact contourBoundaryField_rotShift g (fun j => ContourC1Space.lift γ (W j))
    (fun j x => (ContourC1Space.hasDerivAt_lift (W j) x).differentiableAt)
    (fun j => ContourC1Space.periodic_lift (W j)) b i θ

set_option maxHeartbeats 800000 in
theorem circularBoundaryDerivative_rotation {γ : ℝ≥0} {ι : Type} [Fintype ι]
    (hγ : 0 < γ) (hγ1 : γ ≤ 1) (r : ι → ℝ) (hr : ∀ i, 0 < r i)
    (hinj : Function.Injective r) (g : ι → ℝ) (H : ι → ContourC1Space γ)
    (b : ℝ) (i : ι) (θ : ℝ) :
    contourC1BoundaryDerivative g (fun j => circularReferenceContourC1 hγ hγ1 (r j)) i θ
      (contourRotationFamilyC1CLM γ b H) =
      exp ((b : ℂ) * I) * contourC1BoundaryDerivative g
        (fun j => circularReferenceContourC1 hγ hγ1 (r j)) i (θ - b) H := by
  let Z : ι → ContourC1Space γ := fun j => circularReferenceContourC1 hγ hγ1 (r j)
  have hfix : contourRotationFamilyC1CLM γ b Z = Z := by
    funext j
    exact contourRotationC1_refCircle b (Z j) rfl
  have hpos (j : ι) : ContourC1Space.HasPositiveChordArc (Z j) :=
    hasPositiveChordArc_circularReferenceContourC1 hγ hγ1 (hr j)
  have hsep (j k : ι) (hjk : j ≠ k) : ∃ σ > 0, ContourCrossSeparated (Z j) (Z k) σ :=
    separated_circularReferenceContours hγ hγ1 (hr j) (hr k) (fun h => hjk (hinj h))
  have hleft0 : HasFDerivAt (fun W : ι → ContourC1Space γ => contourC1BoundaryField g W i θ)
      (contourC1BoundaryDerivative g Z i θ) (contourRotationFamilyC1CLM γ b Z) := by
    rw [hfix]
    exact hasFDerivAt_contourC1BoundaryField hγ hγ1 g Z hpos hsep i θ
  have hleft := hleft0.comp Z (contourRotationFamilyC1CLM (ι := ι) γ b).hasFDerivAt
  have hright := (hasFDerivAt_contourC1BoundaryField hγ hγ1 g Z hpos hsep i (θ - b)).const_smul
    (exp ((b : ℂ) * I))
  have he : (fun W : ι → ContourC1Space γ =>
      contourC1BoundaryField g (contourRotationFamilyC1CLM γ b W) i θ) =
      (fun W => exp ((b : ℂ) * I) • contourC1BoundaryField g W i (θ - b)) := by
    funext W
    exact contourC1BoundaryField_rotation g W b i θ
  change HasFDerivAt (fun W => contourC1BoundaryField g (contourRotationFamilyC1CLM γ b W) i θ)
    ((contourC1BoundaryDerivative g Z i θ).comp (contourRotationFamilyC1CLM γ b)) Z at hleft
  rw [he] at hleft
  have hd := congrArg (fun A : (ι → ContourC1Space γ) →L[ℝ] ℂ => A H) (hleft.unique hright)
  exact hd

theorem contourCircleCharacter_neg_arg (n : ℤ) (b : ℝ) :
    contourCircleCharacter n (-b) = contourCircleCharacter (-n) b := by
  unfold contourCircleCharacter
  congr 1
  push_cast
  ring

theorem contourRotationC1_fourier_mode {γ : ℝ≥0} (hγ : 0 < γ) (hγ1 : γ ≤ 1)
    (n : ℤ) (a : ℂ) (b : ℝ) :
    contourRotationC1 b (circularFourierContourC1 hγ hγ1 n a) =
      circularFourierContourC1 hγ hγ1 n (a * contourCircleCharacter (1 - n) b) := by
  apply ContourC1Space.ext
  intro x
  obtain ⟨θ, rfl⟩ := QuotientAddGroup.mk_surjective x
  change ContourC1Space.lift γ (contourRotationC1 b (circularFourierContourC1 hγ hγ1 n a)) θ =
    ContourC1Space.lift γ (circularFourierContourC1 hγ hγ1 n (a * contourCircleCharacter (1 - n) b)) θ
  rw [contourRotationC1_lift]
  simp only [rotShift, lift_circularFourierContourC1]
  rw [show θ - b = θ + -b by ring, contourCircleCharacter_add_arg, contourCircleCharacter_neg_arg,
    show 1 - n = 1 + -n by ring, ← contourCircleCharacter_mul 1 (-n) b]
  have hunit : exp ((b : ℂ) * I) = contourCircleCharacter 1 b := by
    simp only [contourCircleCharacter, Int.cast_one, one_mul]
  rw [hunit]
  ring

theorem contourRotationC1_normal_mode {γ : ℝ≥0} (hγ : 0 < γ) (hγ1 : γ ≤ 1)
    (N : ℕ) (η τ : Fin 2 → ℂ) (b : ℝ) (i : Fin 2) :
    contourRotationC1 b (circularNormalModeC1 hγ hγ1 N η τ i) =
      circularNormalModeC1 hγ hγ1 N
        (fun j => η j * contourCircleCharacter (-((N + 2 : ℕ) : ℤ)) b)
        (fun j => τ j * contourCircleCharacter (-((N + 2 : ℕ) : ℤ)) b) i := by
  change contourRotationC1CLM γ b
      (circularFourierContourC1 hγ hγ1 ((N + 3 : ℕ) : ℤ) (circularNormalModePlus (circularContourRadii i) (η i) (τ i)) +
        circularFourierContourC1 hγ hγ1 (-((N + 1 : ℕ) : ℤ)) (circularNormalModeMinus (circularContourRadii i) (η i) (τ i))) = _
  rw [map_add]
  change contourRotationC1 b (circularFourierContourC1 hγ hγ1 ((N + 3 : ℕ) : ℤ) _) +
    contourRotationC1 b (circularFourierContourC1 hγ hγ1 (-((N + 1 : ℕ) : ℤ)) _) = _
  rw [contourRotationC1_fourier_mode, contourRotationC1_fourier_mode,
    show 1 - ((N + 3 : ℕ) : ℤ) = -((N + 2 : ℕ) : ℤ) by omega,
    show 1 - -((N + 1 : ℕ) : ℤ) = ((N + 2 : ℕ) : ℤ) by omega]
  change circularFourierContourC1 hγ hγ1 ((N + 3 : ℕ) : ℤ) _ +
    circularFourierContourC1 hγ hγ1 (-((N + 1 : ℕ) : ℤ)) _ =
    circularFourierContourC1 hγ hγ1 ((N + 3 : ℕ) : ℤ) _ +
    circularFourierContourC1 hγ hγ1 (-((N + 1 : ℕ) : ℤ)) _
  apply congrArg₂ (fun x y : ContourC1Space γ => x + y)
  · congr 1
    unfold circularNormalModePlus
    ring
  · congr 1
    simp only [circularNormalModeMinus, map_mul, conj_contourCircleCharacter, neg_neg]
    ring

end Euler2D

end
