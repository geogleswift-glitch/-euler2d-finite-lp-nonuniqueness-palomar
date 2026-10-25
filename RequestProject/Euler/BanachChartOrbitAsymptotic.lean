module

public import RequestProject.Euler.BanachObservableAsymptotic
public import RequestProject.Euler.BanachDoubleFlow

/-! A genuine quadratic chart preserves the leading coefficient of
a sampled orbit. A continuous actual return has a genuine open set
of initial points for its two-period material flow. -/

@[expose] public section

noncomputable section

open Set Filter Topology Metric

namespace Euler2D

variable {E B : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup B] [NormedSpace ℝ B]

theorem exists_banachDoubleFlow_initial_ball {X : B → ℝ → B} {V : Set B} {T : ℝ} {c : B}
    (hV : V ∈ 𝓝 c) (hP : ContinuousAt (fun b => X b T) c) (hfix : X c T = c) :
    ∃ ρ > 0, ball c ρ ⊆ banachDoubleFlowDomain X V T := by
  have hn : banachDoubleFlowDomain X V T ∈ 𝓝 c :=
    Filter.inter_mem hV (hP (by change V ∈ 𝓝 (X c T); rw [hfix]; exact hV))
  exact Metric.mem_nhds_iff.mp hn

theorem quadratic_chart_backward_asymptotic
    (Φ : E → B) (c : B) (L : E →L[ℝ] B) (x : ℕ → E) (v : E)
    {κ J C D a b : ℝ} (hκ : 0 ≤ κ) (hJ : 0 ≤ J)
    (hquad : ∀ n, ‖Φ (x n) - c - L (x n)‖ ≤ κ * ‖x n‖ ^ 2)
    (hchart : ∀ n, ‖Φ (x n) - c‖ ≤ J * ‖x n‖)
    (hnorm : ∀ n, ‖x n‖ ≤ C * b ^ n)
    (herror : ∀ n, ‖x n - (a⁻¹) ^ n • v‖ ≤ D * (b ^ 2) ^ n) :
    (∀ n, ‖Φ (x n) - c‖ ≤ (J * C) * b ^ n) ∧
      ∀ n, ‖Φ (x n) - c - (a⁻¹) ^ n • L v‖ ≤
        (κ * C ^ 2 + ‖L‖ * D) * (b ^ 2) ^ n := by
  refine ⟨?_, ?_⟩
  · intro n
    calc
      _ ≤ J * ‖x n‖ := hchart n
      _ ≤ J * (C * b ^ n) := mul_le_mul_of_nonneg_left (hnorm n) hJ
      _ = _ := by ring
  · intro n
    exact observable_quadratic_backward_asymptotic (fun u => Φ u - c) L x v hκ hnorm herror hquad n

end Euler2D

end
