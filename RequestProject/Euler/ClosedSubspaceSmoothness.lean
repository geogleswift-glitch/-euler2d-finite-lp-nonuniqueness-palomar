module

public import RequestProject.Euler.ClosedSubspaceCalculus
public import Mathlib.Analysis.Calculus.ContDiff.Comp

/-! # Smoothness in the inherited norm of a closed Banach subspace

Postcomposition with a linear isometry is again a linear isometry on the
operator spaces.  Induction therefore reflects every finite differentiability
order, and hence smoothness, on an actual open domain.
-/

@[expose] public section

noncomputable section

open Set Filter
open scoped Topology

namespace Euler2D

universe u

variable {P F E : Type u}
variable [NormedAddCommGroup P] [NormedSpace ℝ P]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]
variable [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem contDiffOn_of_complete_linearIsometry_nat (n : ℕ) [CompleteSpace F]
    (i : F →ₗᵢ[ℝ] E) {s : Set P} (hs : IsOpen s) (f : P → F)
    (h : ContDiffOn ℝ n (fun y => i (f y)) s) : ContDiffOn ℝ n f s := by
  induction n generalizing F E with
  | zero =>
    exact contDiffOn_zero.mpr
      (i.isometry.comp_continuousOn_iff.mp h.continuousOn)
  | succ n ih =>
    have hi : IsClosed (Set.range i) := i.isometry.isClosedEmbedding.isClosed_range
    have hn : ((n + 1 : ℕ) : WithTop ℕ∞) = (n : WithTop ℕ∞) + 1 := by simp
    rw [hn, contDiffOn_succ_iff_fderiv_of_isOpen hs] at h ⊢
    refine ⟨?_, by simp, ?_⟩
    · intro x hx
      exact ((differentiableAt_linearIsometry_iff i hi f x).mp
        ((h.1 x hx).differentiableAt (hs.mem_nhds hx))).differentiableWithinAt
    · have hd : ContDiffOn ℝ n
          (fun x => (i.postcomp : (P →L[ℝ] F) →ₗᵢ[ℝ] (P →L[ℝ] E))
            (fderiv ℝ f x)) s := by
        exact h.2.2.congr fun x _ => linearIsometry_comp_fderiv i hi f x
      exact ih (F := P →L[ℝ] F) (E := P →L[ℝ] E)
        (i.postcomp : (P →L[ℝ] F) →ₗᵢ[ℝ] (P →L[ℝ] E)) (fderiv ℝ f) hd

theorem contDiffOn_complete_linearIsometry_iff_nat (n : ℕ) [CompleteSpace F]
    (i : F →ₗᵢ[ℝ] E) {s : Set P} (hs : IsOpen s) (f : P → F) :
    ContDiffOn ℝ n (fun y => i (f y)) s ↔ ContDiffOn ℝ n f s := by
  constructor
  · exact contDiffOn_of_complete_linearIsometry_nat n i hs f
  · intro h
    exact i.contDiff.comp_contDiffOn h

theorem contDiffOn_complete_linearIsometry_iff [CompleteSpace F]
    (i : F →ₗᵢ[ℝ] E) (n : ℕ∞) {s : Set P} (hs : IsOpen s) (f : P → F) :
    ContDiffOn ℝ n (fun y => i (f y)) s ↔ ContDiffOn ℝ n f s := by
  rw [contDiffOn_iff_forall_nat_le, contDiffOn_iff_forall_nat_le]
  exact forall_congr' fun m => imp_congr_right fun _ =>
    contDiffOn_complete_linearIsometry_iff_nat m i hs f

theorem contDiff_complete_linearIsometry_iff [CompleteSpace F]
    (i : F →ₗᵢ[ℝ] E) (n : ℕ∞) (f : P → F) :
    ContDiff ℝ n (fun y => i (f y)) ↔ ContDiff ℝ n f := by
  rw [← contDiffOn_univ, ← contDiffOn_univ]
  exact contDiffOn_complete_linearIsometry_iff i n isOpen_univ f

theorem contDiffOn_closedSubmodule_iff [CompleteSpace E]
    (S : Submodule ℝ E) (hS : IsClosed (S : Set E)) (n : ℕ∞)
    {s : Set P} (hs : IsOpen s) (f : P → S) :
    ContDiffOn ℝ n (fun y => (f y : E)) s ↔ ContDiffOn ℝ n f s := by
  letI : CompleteSpace S := hS.completeSpace_coe
  exact contDiffOn_complete_linearIsometry_iff S.subtypeₗᵢ n hs f

theorem contDiff_closedSubmodule_iff [CompleteSpace E]
    (S : Submodule ℝ E) (hS : IsClosed (S : Set E)) (n : ℕ∞) (f : P → S) :
    ContDiff ℝ n (fun y => (f y : E)) ↔ ContDiff ℝ n f := by
  letI : CompleteSpace S := hS.completeSpace_coe
  exact contDiff_complete_linearIsometry_iff S.subtypeₗᵢ n f

end Euler2D

end
