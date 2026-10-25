module

public import RequestProject.Euler.ContourLittleSelfLog
public import RequestProject.Euler.ContourSelfLogShapeLipschitz

/-! Local Lipschitz regularity of the literal self-log operator in its
genuine little Hölder target, with the unchanged inherited norm. -/

@[expose] public section

noncomputable section

open Set Filter Topology
open scoped NNReal

namespace Euler2D

theorem locallyLipschitz_nearCircleSelfLogLittle {γ : ℝ≥0}
    (hγ : 0 < (γ : ℝ)) (hγ1 : (γ : ℝ) < 1) (Z₀ : ContourC1Space γ)
    {r : ℝ} (hr : 0 < r) (href : ContourC1Space.lift γ Z₀ = refCircle r) :
    LocallyLipschitz (nearCircleSelfLogLittle hγ hγ1 Z₀ hr href) := by
  intro Z
  obtain ⟨K, U, hU, hLip⟩ := locallyLipschitz_nearCircleSelfLogC1 hγ hγ1 Z₀ hr href Z
  refine ⟨K, U, hU, ?_⟩
  intro W hW V hV
  exact hLip hW hV

end Euler2D

end
