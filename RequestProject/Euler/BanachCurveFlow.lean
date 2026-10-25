module

public import RequestProject.Euler.BanachFlowDerivative

/-! Any actual integral curve on a finite interval gives the true
singleton-initial-data flow needed by the existing conservation and
symmetry theorems. -/

@[expose] public section

noncomputable section

open Set Filter Topology Metric

namespace Euler2D

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem isBanachFlowOn_of_curve_interval {f : E → E} {U : Set E} {Y : ℝ → E} {a b : ℝ}
    (hYd : ∀ s ∈ Icc a b, HasDerivAt Y (f (Y s)) s)
    (hYm : ∀ s ∈ Icc a b, Y s ∈ U) :
    IsBanachFlowOn f U {Y a} (b - a) (fun _ s => Y (s + a)) := by
  have hd (s : ℝ) (hs : s ∈ Icc (0 : ℝ) (b - a)) :
      HasDerivAt (fun u : ℝ => Y (u + a)) (f (Y (s + a))) s := by
    have hbound : s + a ∈ Icc a b := ⟨by linarith [hs.1], by linarith [hs.2]⟩
    have h := (hYd (s + a) hbound).scomp s ((hasDerivAt_id s).add_const a)
    simpa only [Function.comp_def, id_eq, one_smul] using h
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro z hz
    have he : z = Y a := mem_singleton_iff.mp hz
    simpa only [zero_add] using he.symm
  · intro z hz s hs
    exact (hd s hs).continuousAt.continuousWithinAt
  · intro z hz s hs
    exact hd s hs
  · intro z hz s hs
    exact hYm (s + a) ⟨by linarith [hs.1], by linarith [hs.2]⟩

end Euler2D

end
