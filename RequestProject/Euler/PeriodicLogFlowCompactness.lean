module

public import RequestProject.Euler.LogFlowCompactness
public import RequestProject.Euler.TorusFlowLimit
public import RequestProject.Euler.TorusPeriodization

/-!
# Global compactness of actual periodic particle flows

A compact set of initial points suffices: the displacement is periodic.
The resulting convergence is uniform on the whole covering plane, so
continuity of the limit is derived without treating wrapping as continuous.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology Metric Real

namespace Euler2D

lemma isTorusPeriodic_flow_displacement {X : R2 → R2}
    (hX : ∀ a k, X (a + torusLatticeShift k) = X a + torusLatticeShift k) :
    IsTorusPeriodic (fun a => X a - a) := by
  intro a i
  have he := hX a (Pi.single i (1 : ℤ))
  rw [torusLatticeShift_single] at he
  dsimp only
  rw [he]
  abel

theorem uniform_subseq_periodic_logFlow_family {T C M : ℝ}
    (hT : 0 ≤ T) (hC : 0 ≤ C) (hM0 : 0 ≤ M)
    (v X : ℕ → ℝ → R2 → R2)
    (hXc : ∀ n, Continuous (Function.uncurry (X n)))
    (hX : ∀ n t, t ∈ Icc 0 T → ∀ a,
      HasDerivAt (fun s => X n s a) (v n t (X n t a)) t)
    (hinit : ∀ n a, X n 0 a = a)
    (hM : ∀ n t, t ∈ Icc 0 T → ∀ x, ‖v n t x‖ ≤ M)
    (hlip : ∀ n t, t ∈ Icc 0 T → ∀ x y, ‖x - y‖ ≤ 1 / 2 →
      ‖v n t x - v n t y‖ ≤ C * logFlowModulus ‖x - y‖)
    (hlat : ∀ n t a k, X n t (a + torusLatticeShift k) = X n t a + torusLatticeShift k)
    (hMP : ∀ n t, t ∈ Icc 0 T → TorusAreaPreserving (X n t)) :
    ∃ F : Icc (0 : ℝ) T × R2 → R2, Continuous F ∧
      (∀ t : Icc (0 : ℝ) T, TorusAreaPreserving (fun a => F (t, a))) ∧
      (∀ a, F (⟨0, le_rfl, hT⟩, a) = a) ∧
      (∀ (t : Icc (0 : ℝ) T) a k,
        F (t, a + torusLatticeShift k) = F (t, a) + torusLatticeShift k) ∧
      ∃ φ : ℕ → ℕ, StrictMono φ ∧
        TendstoUniformly (fun n (p : Icc (0 : ℝ) T × R2) => X (φ n) p.1 p.2) F atTop := by
  obtain ⟨R, hR⟩ := isCompact_closedBox.exists_bound_of_continuousOn
    (continuous_id : Continuous (fun x : R2 => x)).continuousOn
  have hwrap (a : R2) : torusWrap a ∈ closedBall (0 : R2) R :=
    mem_closedBall_zero_iff.mpr (hR _ (torusBox_subset_closedBox (torusRep_mem _)))
  obtain ⟨f, hfc, φ, hφ, hlim⟩ := uniform_subseq_logFlow_family (R := R)
    hT hC hM0 v X hXc hX hinit hM hlip
  let j : Icc (0 : ℝ) T × R2 → Icc (0 : ℝ) T × closedBall (0 : R2) R :=
    fun p => (p.1, ⟨torusWrap p.2, hwrap p.2⟩)
  let F : Icc (0 : ℝ) T × R2 → R2 := fun p => p.2 + f (j p) - torusWrap p.2
  have hdecomp (n : ℕ) (t : ℝ) (a : R2) :
      X n t a = a + X n t (torusWrap a) - torusWrap a := by
    have he := (isTorusPeriodic_flow_displacement (hlat n t)).eq_torusWrap a
    calc
      _ = (X n t a - a) + a := by abel
      _ = (X n t (torusWrap a) - torusWrap a) + a := congrArg (fun z => z + a) he.symm
      _ = _ := by abel
  have hglobal : TendstoUniformly
      (fun n (p : Icc (0 : ℝ) T × R2) => X (φ n) p.1 p.2) F atTop := by
    rw [Metric.tendstoUniformly_iff] at hlim ⊢
    intro ε hε
    filter_upwards [hlim ε hε] with n hn p
    have he : F p - X (φ n) p.1 p.2 = f (j p) - X (φ n) p.1 (torusWrap p.2) := by
      rw [hdecomp]
      dsimp only [F]
      abel
    rw [dist_eq_norm, he]
    simpa only [dist_eq_norm, j] using hn (j p)
  have hFc : Continuous F := by
    apply hglobal.continuous
    apply Eventually.frequently
    exact Eventually.of_forall fun n => (hXc (φ n)).comp
      ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
  refine ⟨F, hFc, ?_, ?_, ?_, φ, hφ, hglobal⟩
  · intro t
    apply torusAreaPreserving_of_ae_tendsto (fun n => hMP (φ n) t t.property)
      (hFc.comp (continuous_const.prodMk continuous_id)).measurable
    exact Eventually.of_forall fun a => hglobal.tendsto_at (t, a)
  · intro a
    have hi := hglobal.tendsto_at (⟨0, le_rfl, hT⟩, a)
    simp only [hinit] at hi
    exact tendsto_nhds_unique hi tendsto_const_nhds
  · intro t a k
    have h1 := hglobal.tendsto_at (t, a + torusLatticeShift k)
    have h2 := (hglobal.tendsto_at (t, a)).add_const (torusLatticeShift k)
    simp only [hlat] at h1
    exact tendsto_nhds_unique h1 h2

end Euler2D

end
