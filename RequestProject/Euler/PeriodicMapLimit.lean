module

public import RequestProject.Euler.PeriodicLogFlowCompactness

/-! A uniform limit on one compact coordinate region determines a global lifted map limit. -/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology Metric

namespace Euler2D

lemma exists_norm_torusWrap_le : ∃ R : ℝ, 0 ≤ R ∧ ∀ a : R2, ‖torusWrap a‖ ≤ R := by
  obtain ⟨R, hR⟩ := isCompact_closedBox.exists_bound_of_continuousOn
    (continuous_id : Continuous (fun x : R2 => x)).continuousOn
  refine ⟨max R 0, le_max_right _ _, fun a => ?_⟩
  exact (hR _ (torusBox_subset_closedBox (torusRep_mem _))).trans (le_max_left _ _)

theorem lift_uniform_periodic_map_limit {A : Type*} [TopologicalSpace A] {R : ℝ}
    (hR : ∀ a : R2, ‖torusWrap a‖ ≤ R)
    (X : ℕ → A → R2 → R2) (hXc : ∀ n, Continuous (Function.uncurry (X n)))
    (hlat : ∀ n t a k, X n t (a + torusLatticeShift k) = X n t a + torusLatticeShift k)
    (f : A × closedBall (0 : R2) R → R2)
    (hlim : TendstoUniformly (fun n (p : A × closedBall (0 : R2) R) => X n p.1 p.2) f atTop) :
    ∃ F : A × R2 → R2, Continuous F ∧
      (∀ t a k, F (t, a + torusLatticeShift k) = F (t, a) + torusLatticeShift k) ∧
      TendstoUniformly (fun n (p : A × R2) => X n p.1 p.2) F atTop := by
  let j : A × R2 → A × closedBall (0 : R2) R :=
    fun p => (p.1, ⟨torusWrap p.2, mem_closedBall_zero_iff.mpr (hR p.2)⟩)
  let F : A × R2 → R2 := fun p => p.2 + f (j p) - torusWrap p.2
  have hdecomp (n : ℕ) (t : A) (a : R2) :
      X n t a = a + X n t (torusWrap a) - torusWrap a := by
    have he := (isTorusPeriodic_flow_displacement (hlat n t)).eq_torusWrap a
    calc
      _ = (X n t a - a) + a := by abel
      _ = (X n t (torusWrap a) - torusWrap a) + a := congrArg (fun z => z + a) he.symm
      _ = _ := by abel
  have hglobal : TendstoUniformly (fun n (p : A × R2) => X n p.1 p.2) F atTop := by
    rw [Metric.tendstoUniformly_iff] at hlim ⊢
    intro ε hε
    filter_upwards [hlim ε hε] with n hn p
    have he : F p - X n p.1 p.2 = f (j p) - X n p.1 (torusWrap p.2) := by
      rw [hdecomp]
      dsimp only [F]
      abel
    rw [dist_eq_norm, he]
    simpa only [dist_eq_norm, j] using hn (j p)
  refine ⟨F, hglobal.continuous ((Eventually.of_forall hXc).frequently), ?_, hglobal⟩
  intro t a k
  have h1 := hglobal.tendsto_at (t, a + torusLatticeShift k)
  have h2 := (hglobal.tendsto_at (t, a)).add_const (torusLatticeShift k)
  simp only [hlat] at h1
  exact tendsto_nhds_unique h1 h2

end Euler2D

end
