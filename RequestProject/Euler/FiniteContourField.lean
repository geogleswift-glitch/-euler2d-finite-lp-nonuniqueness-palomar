module

public import RequestProject.Euler.ContourLittleSelfLogLipschitz
public import RequestProject.Euler.ContourCrossBoundaryIntegralCoordinates
public import RequestProject.Euler.ContourBoundaryField
public import RequestProject.Euler.FiniteContourLipschitz

/-! The original finite-interface vector field in the actual little
Hölder Banach space, on its genuine open separated near-circle domain. -/

@[expose] public section

noncomputable section

open Set Filter Topology Metric
open scoped NNReal BigOperators

namespace Euler2D

local instance (priority := 2000) finiteFieldLittle_normedAddCommGroup (γ : ℝ≥0) :
    NormedAddCommGroup (LittleContourSpace γ) :=
  Submodule.normedAddCommGroup (LittleContourSpace γ)

local instance (priority := 2000) finiteFieldLittle_normedSpace (γ : ℝ≥0) :
    NormedSpace ℝ (LittleContourSpace γ) := Submodule.normedSpace (LittleContourSpace γ)

local instance (priority := 2000) finiteFieldC1_normedAddCommGroup (γ : ℝ≥0) :
    NormedAddCommGroup (ContourC1Space γ) :=
  Submodule.normedAddCommGroup (contourC1GraphSubmodule γ)

local instance (priority := 2000) finiteFieldC1_normedSpace (γ : ℝ≥0) :
    NormedSpace ℝ (ContourC1Space γ) := Submodule.normedSpace (contourC1GraphSubmodule γ)

def IsAdmissibleLittleContourFamily {γ : ℝ≥0} {ι : Type*}
    (Z₀ : ι → ContourC1Space γ) (r : ι → ℝ) (Z : ι → LittleContourSpace γ) : Prop :=
  (∀ i, ‖(Z i).val - Z₀ i‖ < 2 * r i / Real.pi) ∧
    ∀ i j, i ≠ j → ∃ σ > 0, ContourCrossSeparated (Z i).val (Z j).val σ

abbrev AdmissibleLittleContourFamily {γ : ℝ≥0} {ι : Type*}
    (Z₀ : ι → ContourC1Space γ) (r : ι → ℝ) :=
  {Z : ι → LittleContourSpace γ // IsAdmissibleLittleContourFamily Z₀ r Z}

theorem isOpen_admissibleLittleContourFamilies {γ : ℝ≥0} {ι : Type*} [Fintype ι]
    (Z₀ : ι → ContourC1Space γ) (r : ι → ℝ) :
    IsOpen {Z : ι → LittleContourSpace γ | IsAdmissibleLittleContourFamily Z₀ r Z} := by
  classical
  have hn (i : ι) : IsOpen {Z : ι → LittleContourSpace γ |
      ‖(Z i).val - Z₀ i‖ < 2 * r i / Real.pi} :=
    isOpen_lt ((((LittleContourSpace.inclusion γ).continuous.comp (continuous_apply i)).sub
      continuous_const).norm) continuous_const
  have hs (i j : ι) : IsOpen {Z : ι → LittleContourSpace γ |
      i ≠ j → ∃ σ > 0, ContourCrossSeparated (Z i).val (Z j).val σ} := by
    by_cases hij : i = j
    · simp only [hij, ne_eq, not_true_eq_false, IsEmpty.forall_iff, setOf_true]
      exact isOpen_univ
    · have hc : Continuous (fun Z : ι → LittleContourSpace γ => ((Z i).val, (Z j).val)) :=
        ((LittleContourSpace.inclusion γ).continuous.comp (continuous_apply i)).prodMk
          ((LittleContourSpace.inclusion γ).continuous.comp (continuous_apply j))
      simpa [hij] using (isOpen_positiveSeparatedContourPairs γ).preimage hc
  have hnear : IsOpen {Z : ι → LittleContourSpace γ |
      ∀ i, ‖(Z i).val - Z₀ i‖ < 2 * r i / Real.pi} := by
    simpa only [setOf_forall] using isOpen_iInter_of_finite hn
  have hsep : IsOpen {Z : ι → LittleContourSpace γ |
      ∀ i j, i ≠ j → ∃ σ > 0, ContourCrossSeparated (Z i).val (Z j).val σ} := by
    simpa only [setOf_forall] using isOpen_iInter_of_finite (fun i => isOpen_iInter_of_finite (hs i))
  exact hnear.inter hsep

def finiteFamilyNearCircleComponent {γ : ℝ≥0} {ι : Type*}
    (Z₀ : ι → ContourC1Space γ) (r : ι → ℝ) (i : ι)
    (Z : AdmissibleLittleContourFamily Z₀ r) : NearCircleLittleContour (Z₀ i) (r i) :=
  ⟨Z.val i, Z.property.1 i⟩

theorem lipschitzWith_finiteFamilyNearCircleComponent {γ : ℝ≥0} {ι : Type*} [Fintype ι]
    (Z₀ : ι → ContourC1Space γ) (r : ι → ℝ) (i : ι) :
    LipschitzWith 1 (finiteFamilyNearCircleComponent Z₀ r i) := by
  apply LipschitzWith.of_dist_le_mul
  intro Z W
  change dist (Z.val i) (W.val i) ≤ (1 : ℝ) * dist Z.val W.val
  rw [one_mul]
  exact dist_le_pi_dist Z.val W.val i

def finiteFamilySeparatedPair {γ : ℝ≥0} {ι : Type*}
    (Z₀ : ι → ContourC1Space γ) (r : ι → ℝ) (i j : ι) (hij : i ≠ j)
    (Z : AdmissibleLittleContourFamily Z₀ r) : PositiveSeparatedLittleContourPair γ :=
  ⟨(Z.val i, Z.val j), Z.property.2 i j hij⟩

theorem lipschitzWith_finiteFamilySeparatedPair {γ : ℝ≥0} {ι : Type*} [Fintype ι]
    (Z₀ : ι → ContourC1Space γ) (r : ι → ℝ) (i j : ι) (hij : i ≠ j) :
    LipschitzWith 1 (finiteFamilySeparatedPair Z₀ r i j hij) := by
  apply LipschitzWith.of_dist_le_mul
  intro Z W
  change dist (Z.val i, Z.val j) (W.val i, W.val j) ≤ (1 : ℝ) * dist Z.val W.val
  rw [one_mul, Prod.dist_eq]
  exact max_le (dist_le_pi_dist Z.val W.val i) (dist_le_pi_dist Z.val W.val j)

def finiteContourInteraction {γ : ℝ≥0} {ι : Type*}
    (hγ : 0 < (γ : ℝ)) (hγ1 : (γ : ℝ) < 1)
    (Z₀ : ι → ContourC1Space γ) (r : ι → ℝ) (hr : ∀ i, 0 < r i)
    (href : ∀ i, ContourC1Space.lift γ (Z₀ i) = refCircle (r i))
    (i j : ι) (Z : AdmissibleLittleContourFamily Z₀ r) : LittleContourSpace γ := by
  classical
  exact if hij : i = j then
    nearCircleSelfLogLittle hγ hγ1 (Z₀ i) (hr i) (href i) (finiteFamilyNearCircleComponent Z₀ r i Z)
  else contourCrossLogLittleOnLocus hγ1.le (finiteFamilySeparatedPair Z₀ r i j hij Z)

theorem locallyLipschitz_finiteContourInteraction {γ : ℝ≥0} {ι : Type*} [Fintype ι]
    (hγ : 0 < (γ : ℝ)) (hγ1 : (γ : ℝ) < 1)
    (Z₀ : ι → ContourC1Space γ) (r : ι → ℝ) (hr : ∀ i, 0 < r i)
    (href : ∀ i, ContourC1Space.lift γ (Z₀ i) = refCircle (r i)) (i j : ι) :
    LocallyLipschitz (finiteContourInteraction hγ hγ1 Z₀ r hr href i j) := by
  classical
  by_cases hij : i = j
  · have he : finiteContourInteraction hγ hγ1 Z₀ r hr href i j = fun Z =>
        nearCircleSelfLogLittle hγ hγ1 (Z₀ i) (hr i) (href i) (finiteFamilyNearCircleComponent Z₀ r i Z) :=
      funext (fun Z => by simp only [finiteContourInteraction, dif_pos hij])
    rw [he]
    exact (locallyLipschitz_nearCircleSelfLogLittle hγ hγ1 (Z₀ i) (hr i) (href i)).comp
      (lipschitzWith_finiteFamilyNearCircleComponent Z₀ r i).locallyLipschitz
  · have he : finiteContourInteraction hγ hγ1 Z₀ r hr href i j = fun Z =>
        contourCrossLogLittleOnLocus hγ1.le (finiteFamilySeparatedPair Z₀ r i j hij Z) :=
      funext (fun Z => by simp only [finiteContourInteraction, dif_neg hij])
    rw [he]
    exact (locallyLipschitz_contourCrossLogLittleOnLocus hγ1.le).comp
      (lipschitzWith_finiteFamilySeparatedPair Z₀ r i j hij).locallyLipschitz

theorem lift_finiteContourInteraction {γ : ℝ≥0} {ι : Type*}
    (hγ : 0 < (γ : ℝ)) (hγ1 : (γ : ℝ) < 1)
    (Z₀ : ι → ContourC1Space γ) (r : ι → ℝ) (hr : ∀ i, 0 < r i)
    (href : ∀ i, ContourC1Space.lift γ (Z₀ i) = refCircle (r i))
    (i j : ι) (Z : AdmissibleLittleContourFamily Z₀ r) (θ : ℝ) :
    LittleContourSpace.lift γ (finiteContourInteraction hγ hγ1 Z₀ r hr href i j Z) θ =
      contourLogBoundaryIntegral (LittleContourSpace.lift γ (Z.val j))
        (deriv (LittleContourSpace.lift γ (Z.val j))) (LittleContourSpace.lift γ (Z.val i) θ) := by
  classical
  by_cases hij : i = j
  · subst j
    rw [finiteContourInteraction, dif_pos rfl, lift_nearCircleSelfLogLittle]
    exact ContourC1Space.selfLogIntegral_eq_boundaryIntegral (Z.val i).val θ
  · rw [finiteContourInteraction, dif_neg hij]
    exact contourCrossLogLittleOnLocus_eq_boundaryIntegral hγ1.le
      (finiteFamilySeparatedPair Z₀ r i j hij Z) θ

def finiteContourMaterialField {γ : ℝ≥0} {ι : Type*} [Fintype ι]
    (hγ : 0 < (γ : ℝ)) (hγ1 : (γ : ℝ) < 1)
    (Z₀ : ι → ContourC1Space γ) (r : ι → ℝ) (hr : ∀ i, 0 < r i)
    (href : ∀ i, ContourC1Space.lift γ (Z₀ i) = refCircle (r i)) (g : ι → ℝ)
    (Z : AdmissibleLittleContourFamily Z₀ r) (i : ι) : LittleContourSpace γ :=
  (-1 / (2 * Real.pi) : ℝ) • ∑ j, g j • finiteContourInteraction hγ hγ1 Z₀ r hr href i j Z

theorem locallyLipschitz_finiteContourMaterialField {γ : ℝ≥0} {ι : Type*} [Fintype ι]
    (hγ : 0 < (γ : ℝ)) (hγ1 : (γ : ℝ) < 1)
    (Z₀ : ι → ContourC1Space γ) (r : ι → ℝ) (hr : ∀ i, 0 < r i)
    (href : ∀ i, ContourC1Space.lift γ (Z₀ i) = refCircle (r i)) (g : ι → ℝ) :
    LocallyLipschitz (finiteContourMaterialField hγ hγ1 Z₀ r hr href g) := by
  apply locallyLipschitz_finite_pi
  intro i
  have hs : LocallyLipschitz (fun W : LittleContourSpace γ => (-1 / (2 * Real.pi) : ℝ) • W) :=
    (lipschitzWith_smul (-1 / (2 * Real.pi) : ℝ)).locallyLipschitz
  exact hs.comp (locallyLipschitz_finite_weighted_sum g
    (fun j => finiteContourInteraction hγ hγ1 Z₀ r hr href i j)
    (fun j => locallyLipschitz_finiteContourInteraction hγ hγ1 Z₀ r hr href i j))

theorem lift_finiteContourMaterialField {γ : ℝ≥0} {ι : Type*} [Fintype ι]
    (hγ : 0 < (γ : ℝ)) (hγ1 : (γ : ℝ) < 1)
    (Z₀ : ι → ContourC1Space γ) (r : ι → ℝ) (hr : ∀ i, 0 < r i)
    (href : ∀ i, ContourC1Space.lift γ (Z₀ i) = refCircle (r i)) (g : ι → ℝ)
    (Z : AdmissibleLittleContourFamily Z₀ r) (i : ι) (θ : ℝ) :
    LittleContourSpace.lift γ (finiteContourMaterialField hγ hγ1 Z₀ r hr href g Z i) θ =
      contourBoundaryField g (fun j => LittleContourSpace.lift γ (Z.val j)) i θ := by
  change (LittleContourSpace.eval γ (θ : ContourCircle))
    ((-1 / (2 * Real.pi) : ℝ) • ∑ j, g j • finiteContourInteraction hγ hγ1 Z₀ r hr href i j Z) = _
  rw [map_smul, map_sum]
  simp_rw [map_smul]
  change (-1 / (2 * Real.pi) : ℝ) • ∑ j, g j •
    LittleContourSpace.lift γ (finiteContourInteraction hγ hγ1 Z₀ r hr href i j Z) θ = _
  simp_rw [lift_finiteContourInteraction, Complex.real_smul]
  unfold contourBoundaryField
  push_cast
  rfl

end Euler2D

end
