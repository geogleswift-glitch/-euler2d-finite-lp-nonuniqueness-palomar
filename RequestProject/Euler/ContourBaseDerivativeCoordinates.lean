module

public import RequestProject.Euler.ContourC1Space
public import RequestProject.Euler.ContourChordArc

/-! Evaluation at one base point and the genuine Hölder derivative give
faithful, quantitatively equivalent coordinates for the actual C¹ space. -/

@[expose] public section

noncomputable section

open Set Filter Topology
open scoped NNReal

namespace Euler2D

local instance (priority := 2000) baseCoordinates_normedAddCommGroup (γ : ℝ≥0) :
    NormedAddCommGroup (ContourC1Space γ) :=
  Submodule.normedAddCommGroup (contourC1GraphSubmodule γ)

local instance (priority := 2000) baseCoordinates_normedSpace (γ : ℝ≥0) :
    NormedSpace ℝ (ContourC1Space γ) :=
  Submodule.normedSpace (contourC1GraphSubmodule γ)

def contourBaseDerivativeMap (γ : ℝ≥0) : ContourC1Space γ →L[ℝ] ℂ × ContourHolderSpace γ :=
  (ContourC1Space.eval γ (0 : ContourCircle)).prod (ContourC1Space.derivative γ)

@[simp] theorem contourBaseDerivativeMap_apply {γ : ℝ≥0} (Z : ContourC1Space γ) :
    contourBaseDerivativeMap γ Z =
      (ContourC1Space.lift γ Z 0, ContourC1Space.derivative γ Z) := rfl

theorem norm_contourC1_value_sub_base_le {γ : ℝ≥0} (Z : ContourC1Space γ) (x : ContourCircle) :
    ‖ContourC1Space.toBCF γ Z x - ContourC1Space.lift γ Z 0‖ ≤
      Real.pi * ‖ContourC1Space.derivative γ Z‖ := by
  obtain ⟨θ, φ, hθ, hφ, hgap, _⟩ := exists_short_contour_representatives x (0 : ContourCircle)
  have hd (t : ℝ) : ‖deriv (ContourC1Space.lift γ Z) t‖ ≤ ‖ContourC1Space.derivative γ Z‖ := by
    rw [ContourC1Space.deriv_lift]
    exact HolderFunctionSpace.norm_eval_le _ _
  have hm := norm_sub_le_of_contDiff_deriv_bound (ContourC1Space.contDiff_lift Z)
    (norm_nonneg _) hd θ φ
  change ‖ContourC1Space.toBCF γ Z (θ : ContourCircle) -
    ContourC1Space.toBCF γ Z (φ : ContourCircle)‖ ≤ _ at hm
  rw [hθ, hφ] at hm
  exact hm.trans ((mul_le_mul_of_nonneg_left hgap (norm_nonneg _)).trans_eq (mul_comm _ _))

theorem norm_contourC1_le_base_add_derivative {γ : ℝ≥0} (Z : ContourC1Space γ) :
    ‖Z‖ ≤ ‖ContourC1Space.lift γ Z 0‖ + (Real.pi + 1) * ‖ContourC1Space.derivative γ Z‖ := by
  have hb : ‖ContourC1Space.toBCF γ Z‖ ≤
      ‖ContourC1Space.lift γ Z 0‖ + Real.pi * ‖ContourC1Space.derivative γ Z‖ := by
    apply (BoundedContinuousFunction.norm_le (by positivity)).mpr
    intro x
    exact (norm_le_norm_sub_add _ _).trans ((add_le_add
      (norm_contourC1_value_sub_base_le Z x) le_rfl).trans_eq (add_comm _ _))
  change max ‖ContourC1Space.toBCF γ Z‖ ‖ContourC1Space.derivative γ Z‖ ≤ _
  apply max_le
  · nlinarith [norm_nonneg (ContourC1Space.derivative γ Z)]
  · nlinarith [norm_nonneg (ContourC1Space.lift γ Z 0),
      mul_nonneg Real.pi_pos.le (norm_nonneg (ContourC1Space.derivative γ Z))]

theorem norm_contourC1_le_baseDerivativeMap {γ : ℝ≥0} (Z : ContourC1Space γ) :
    ‖Z‖ ≤ (Real.pi + 2) * ‖contourBaseDerivativeMap γ Z‖ := by
  have h0 : ‖ContourC1Space.lift γ Z 0‖ ≤ ‖contourBaseDerivativeMap γ Z‖ :=
    norm_fst_le (contourBaseDerivativeMap γ Z)
  have hd : ‖ContourC1Space.derivative γ Z‖ ≤ ‖contourBaseDerivativeMap γ Z‖ :=
    norm_snd_le (contourBaseDerivativeMap γ Z)
  have hm := mul_le_mul_of_nonneg_left hd (show 0 ≤ Real.pi + 1 by positivity)
  calc
    _ ≤ ‖ContourC1Space.lift γ Z 0‖ + (Real.pi + 1) * ‖ContourC1Space.derivative γ Z‖ :=
      norm_contourC1_le_base_add_derivative Z
    _ ≤ ‖contourBaseDerivativeMap γ Z‖ + (Real.pi + 1) * ‖contourBaseDerivativeMap γ Z‖ :=
      add_le_add h0 hm
    _ = _ := by ring

end Euler2D

end
