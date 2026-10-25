module

public import RequestProject.Euler.ExteriorContourForcing

/-! Genuine complex conjugation is bounded in the actual C¹ Hölder
norm and preserves the unchanged smooth-closure little contour space. -/

@[expose] public section

noncomputable section

open Complex ComplexConjugate Set Filter Topology
open scoped NNReal ContDiff

namespace Euler2D

def contourC1ConjugateCLM (γ : ℝ≥0) : ContourC1Space γ →L[ℝ] ContourC1Space γ :=
  ({ toFun := contourC1Conjugate
     map_add' := fun Z W => by
       apply ContourC1Space.ext
       intro x
       change conj (ContourC1Space.toBCF γ Z x + ContourC1Space.toBCF γ W x) =
         conj (ContourC1Space.toBCF γ Z x) + conj (ContourC1Space.toBCF γ W x)
       exact map_add _ _ _
     map_smul' := fun c Z => by
       apply ContourC1Space.ext
       intro x
       change conj (c • ContourC1Space.toBCF γ Z x) = c • conj (ContourC1Space.toBCF γ Z x)
       exact map_smul (Complex.conjCLE : ℂ →L[ℝ] ℂ) c _ } :
    ContourC1Space γ →ₗ[ℝ] ContourC1Space γ).mkContinuous 1
      (fun Z => by simpa only [one_mul] using norm_contourC1Conjugate_le Z)

@[simp] theorem contourC1ConjugateCLM_apply (γ : ℝ≥0) (Z : ContourC1Space γ) :
    contourC1ConjugateCLM γ Z = contourC1Conjugate Z := rfl

theorem contourC1Conjugate_mem_little {γ : ℝ≥0} (Z : LittleContourSpace γ) :
    contourC1Conjugate Z.val ∈ (LittleContourSpace γ : Set (ContourC1Space γ)) := by
  have hclosed : IsClosed ((contourC1ConjugateCLM γ) ⁻¹'
      (LittleContourSpace γ : Set (ContourC1Space γ))) :=
    (isClosed_littleContourSpace γ).preimage (contourC1ConjugateCLM γ).continuous
  have hs : (smoothContourSubmodule γ : Set (ContourC1Space γ)) ⊆
      (contourC1ConjugateCLM γ) ⁻¹' (LittleContourSpace γ : Set (ContourC1Space γ)) := by
    intro W hW
    apply (smoothContourSubmodule γ).le_topologicalClosure
    change ContDiff ℝ ∞ (ContourC1Space.lift γ (contourC1Conjugate W))
    have he : ContourC1Space.lift γ (contourC1Conjugate W) =
        fun θ => conj (ContourC1Space.lift γ W θ) := funext (lift_contourC1Conjugate W)
    rw [he]
    exact Complex.conjCLE.contDiff.comp hW
  exact closure_minimal hs hclosed Z.property

def contourLittleConjugate {γ : ℝ≥0} (Z : LittleContourSpace γ) : LittleContourSpace γ :=
  ⟨contourC1Conjugate Z.val, contourC1Conjugate_mem_little Z⟩

@[simp] theorem lift_contourLittleConjugate {γ : ℝ≥0} (Z : LittleContourSpace γ) (θ : ℝ) :
    LittleContourSpace.lift γ (contourLittleConjugate Z) θ = conj (LittleContourSpace.lift γ Z θ) := rfl

end Euler2D

end
