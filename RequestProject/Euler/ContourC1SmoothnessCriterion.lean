module

public import RequestProject.Euler.ContourBaseDerivativeCoordinates
public import RequestProject.Euler.BoundedBelowCalculus

/-! Smoothness in the genuine C¹ Hölder norm follows from smoothness
of the actual base value and the actual Hölder derivative. -/

@[expose] public section

noncomputable section

open Set
open scoped NNReal

namespace Euler2D

local instance (priority := 2000) c1Criterion_normedAddCommGroup (γ : ℝ≥0) :
    NormedAddCommGroup (ContourC1Space γ) :=
  Submodule.normedAddCommGroup (contourC1GraphSubmodule γ)

local instance (priority := 2000) c1Criterion_normedSpace (γ : ℝ≥0) :
    NormedSpace ℝ (ContourC1Space γ) :=
  Submodule.normedSpace (contourC1GraphSubmodule γ)

theorem contDiffOn_contourC1_iff_baseDerivative {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {γ : ℝ≥0} (n : ℕ∞) {s : Set P} (hs : IsOpen s) (f : P → ContourC1Space γ) :
    ContDiffOn ℝ n f s ↔
      ContDiffOn ℝ n (fun p => ContourC1Space.lift γ (f p) 0) s ∧
        ContDiffOn ℝ n (fun p => ContourC1Space.derivative γ (f p)) s := by
  constructor
  · intro hf
    exact ⟨(ContourC1Space.eval γ (0 : ContourCircle)).contDiff.comp_contDiffOn hf,
      (ContourC1Space.derivative γ).contDiff.comp_contDiffOn hf⟩
  · rintro ⟨h0, hd⟩
    apply (contDiffOn_boundedBelowLinearMap_iff (contourBaseDerivativeMap γ)
      (show 0 < Real.pi + 2 by positivity) norm_contourC1_le_baseDerivativeMap n hs f).mp
    exact h0.prodMk hd

end Euler2D

end
