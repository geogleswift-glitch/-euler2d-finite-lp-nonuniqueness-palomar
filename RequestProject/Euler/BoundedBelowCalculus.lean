module

public import RequestProject.Euler.ClosedSubspaceSmoothness

/-! # Reflection of smoothness by a bounded-below linear map

The inverse onto the genuine range is constructed with the given norm bound.
The codomain need not be complete or admit a complemented copy of the range.
-/

@[expose] public section

noncomputable section

open Set

namespace Euler2D

universe u

variable {P E F : Type u}
variable [NormedAddCommGroup P] [NormedSpace ℝ P]
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem boundedBelowLinearMap_antilipschitz (L : E →L[ℝ] F) {C : ℝ} (hC : 0 < C)
    (hL : ∀ x, ‖x‖ ≤ C * ‖L x‖) : AntilipschitzWith ⟨C, hC.le⟩ L :=
  L.antilipschitz_of_bound hL

theorem boundedBelowLinearMap_isClosed_range [CompleteSpace E]
    (L : E →L[ℝ] F) {C : ℝ} (hC : 0 < C)
    (hL : ∀ x, ‖x‖ ≤ C * ‖L x‖) : IsClosed (Set.range L) :=
  (boundedBelowLinearMap_antilipschitz L hC hL).isClosed_range L.uniformContinuous

def boundedBelowLinearEquivRange (L : E →L[ℝ] F) {C : ℝ} (hC : 0 < C)
    (hL : ∀ x, ‖x‖ ≤ C * ‖L x‖) : E ≃L[ℝ] L.range := by
  let e : E ≃ₗ[ℝ] L.range := LinearEquiv.ofInjective L.toLinearMap
    (boundedBelowLinearMap_antilipschitz L hC hL).injective
  exact e.toContinuousLinearEquivOfBounds ‖L‖ C
    (fun x => L.le_opNorm x) (fun y => by
      have he : L (e.symm y) = (y : F) :=
        congrArg Subtype.val (e.apply_symm_apply y)
      change ‖e.symm y‖ ≤ C * ‖(y : F)‖
      rw [← he]
      exact hL (e.symm y))

theorem boundedBelowLinearEquivRange_coe (L : E →L[ℝ] F) {C : ℝ} (hC : 0 < C)
    (hL : ∀ x, ‖x‖ ≤ C * ‖L x‖) (x : E) :
    (boundedBelowLinearEquivRange L hC hL x : F) = L x := rfl

theorem boundedBelowLinearEquivRange_symm_apply (L : E →L[ℝ] F) {C : ℝ} (hC : 0 < C)
    (hL : ∀ x, ‖x‖ ≤ C * ‖L x‖) (x : E) :
    (boundedBelowLinearEquivRange L hC hL).symm ⟨L x, L.mem_range_self x⟩ = x :=
  (boundedBelowLinearEquivRange L hC hL).symm_apply_apply x

theorem contDiffOn_boundedBelowLinearMap_iff [CompleteSpace E]
    (L : E →L[ℝ] F) {C : ℝ} (hC : 0 < C) (hL : ∀ x, ‖x‖ ≤ C * ‖L x‖)
    (n : ℕ∞) {s : Set P} (hs : IsOpen s) (f : P → E) :
    ContDiffOn ℝ n (fun y => L (f y)) s ↔ ContDiffOn ℝ n f s := by
  constructor
  · intro h
    let e : E ≃L[ℝ] L.range := boundedBelowLinearEquivRange L hC hL
    letI : CompleteSpace L.range :=
      (completeSpace_congr (e := e.toLinearEquiv.toEquiv) e.isUniformEmbedding).mp
        (inferInstance : CompleteSpace E)
    have hr : ContDiffOn ℝ n (fun y => e (f y)) s :=
      (contDiffOn_complete_linearIsometry_iff L.range.subtypeₗᵢ n hs
        (fun y => e (f y))).mp h
    simpa only [Function.comp_def, e.symm_apply_apply] using
      e.symm.contDiff.comp_contDiffOn hr
  · intro h
    exact L.contDiff.comp_contDiffOn h

theorem contDiff_boundedBelowLinearMap_iff [CompleteSpace E]
    (L : E →L[ℝ] F) {C : ℝ} (hC : 0 < C) (hL : ∀ x, ‖x‖ ≤ C * ‖L x‖)
    (n : ℕ∞) (f : P → E) :
    ContDiff ℝ n (fun y => L (f y)) ↔ ContDiff ℝ n f := by
  rw [← contDiffOn_univ, ← contDiffOn_univ]
  exact contDiffOn_boundedBelowLinearMap_iff L hC hL n isOpen_univ f

end Euler2D

end
