module

public import RequestProject.Euler.PeriodicLogFlowCompactness
public import RequestProject.Euler.InverseLogFlowCompactness
public import RequestProject.Euler.PeriodicMapLimit
public import Mathlib.Topology.UniformSpace.UniformApproximation

/-!
# Simultaneous limits of the actual forward and inverse particle maps

Compactness first extracts the forward flow and then its inverse family.
Global uniform convergence and continuity preserve the genuine two-sided
inverse identities.  Measure preservation passes through the continuous
quotient map.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology Metric Real

namespace Euler2D

theorem inverse_pair_of_uniform_particle_limits {T : ℝ}
    {X Y : ℕ → ℝ → R2 → R2} {F G : Icc (0 : ℝ) T × R2 → R2}
    (hFc : Continuous F) (hGc : Continuous G)
    (hF : TendstoUniformly (fun n (p : Icc (0 : ℝ) T × R2) => X n p.1 p.2) F atTop)
    (hG : TendstoUniformly (fun n (p : Icc (0 : ℝ) T × R2) => Y n p.1 p.2) G atTop)
    (hright : ∀ n t, t ∈ Icc (0 : ℝ) T → ∀ a, X n t (Y n t a) = a)
    (hleft : ∀ n t, t ∈ Icc (0 : ℝ) T → ∀ a, Y n t (X n t a) = a) :
    (∀ (t : Icc (0 : ℝ) T) a, F (t, G (t, a)) = a) ∧
      ∀ (t : Icc (0 : ℝ) T) a, G (t, F (t, a)) = a := by
  constructor
  · intro t a
    have hin : Tendsto (fun n => (t, Y n t a)) atTop (𝓝 (t, G (t, a))) :=
      tendsto_const_nhds.prodMk_nhds (hG.tendsto_at (t, a))
    have hc := hF.tendsto_comp hFc.continuousAt hin
    simp only [hright _ _ t.property] at hc
    exact tendsto_nhds_unique hc tendsto_const_nhds
  · intro t a
    have hin : Tendsto (fun n => (t, X n t a)) atTop (𝓝 (t, F (t, a))) :=
      tendsto_const_nhds.prodMk_nhds (hF.tendsto_at (t, a))
    have hc := hG.tendsto_comp hGc.continuousAt hin
    simp only [hleft _ _ t.property] at hc
    exact tendsto_nhds_unique hc tendsto_const_nhds

/-- Actual periodic forward trajectories with common bounded speed and
logarithmic spatial modulus have a common subsequence on which both the
forward and the genuine inverse maps converge uniformly on the whole
covering plane.  The limiting pair remains inverse and area preserving. -/
theorem uniform_subseq_periodic_particle_pair {T C M : ℝ}
    (hT : 0 ≤ T) (hC : 0 ≤ C) (hM0 : 0 ≤ M)
    (v X Y : ℕ → ℝ → R2 → R2)
    (hXc : ∀ n, Continuous (Function.uncurry (X n)))
    (hYc : ∀ n, Continuous (Function.uncurry (Y n)))
    (hX : ∀ n t, t ∈ Icc 0 T → ∀ a,
      HasDerivAt (fun s => X n s a) (v n t (X n t a)) t)
    (hinit : ∀ n a, X n 0 a = a)
    (hright : ∀ n t, t ∈ Icc 0 T → ∀ a, X n t (Y n t a) = a)
    (hleft : ∀ n t, t ∈ Icc 0 T → ∀ a, Y n t (X n t a) = a)
    (hM : ∀ n t, t ∈ Icc 0 T → ∀ x, ‖v n t x‖ ≤ M)
    (hlip : ∀ n t, t ∈ Icc 0 T → ∀ x y, ‖x - y‖ ≤ 1 / 2 →
      ‖v n t x - v n t y‖ ≤ C * logFlowModulus ‖x - y‖)
    (hXlat : ∀ n t a k, X n t (a + torusLatticeShift k) = X n t a + torusLatticeShift k)
    (hYlat : ∀ n t a k, Y n t (a + torusLatticeShift k) = Y n t a + torusLatticeShift k)
    (hXMP : ∀ n t, t ∈ Icc 0 T → TorusAreaPreserving (X n t))
    (hYMP : ∀ n t, t ∈ Icc 0 T → TorusAreaPreserving (Y n t)) :
    ∃ F G : Icc (0 : ℝ) T × R2 → R2, Continuous F ∧ Continuous G ∧
      (∀ t : Icc (0 : ℝ) T, TorusAreaPreserving (fun a => F (t, a))) ∧
      (∀ t : Icc (0 : ℝ) T, TorusAreaPreserving (fun a => G (t, a))) ∧
      (∀ a, F (⟨0, le_rfl, hT⟩, a) = a) ∧
      (∀ a, G (⟨0, le_rfl, hT⟩, a) = a) ∧
      (∀ (t : Icc (0 : ℝ) T) a k,
        F (t, a + torusLatticeShift k) = F (t, a) + torusLatticeShift k) ∧
      (∀ (t : Icc (0 : ℝ) T) a k,
        G (t, a + torusLatticeShift k) = G (t, a) + torusLatticeShift k) ∧
      (∀ (t : Icc (0 : ℝ) T) a, F (t, G (t, a)) = a) ∧
      (∀ (t : Icc (0 : ℝ) T) a, G (t, F (t, a)) = a) ∧
      ∃ φ : ℕ → ℕ, StrictMono φ ∧
        TendstoUniformly (fun n (p : Icc (0 : ℝ) T × R2) => X (φ n) p.1 p.2) F atTop ∧
        TendstoUniformly (fun n (p : Icc (0 : ℝ) T × R2) => Y (φ n) p.1 p.2) G atTop := by
  obtain ⟨F, hFc, hFMP, hFinit, hFlat, φ, hφ, hFlim⟩ :=
    uniform_subseq_periodic_logFlow_family hT hC hM0 v X hXc hX hinit hM hlip hXlat hXMP
  obtain ⟨R, _hR0, hR⟩ := exists_norm_torusWrap_le
  obtain ⟨g, _hgc, ψ, hψ, hψlim⟩ := uniform_subseq_inverse_logFlow_family (E := R2) (R := R)
    hT hC hM0 (fun n => v (φ n)) (fun n => X (φ n)) (fun n => Y (φ n))
    (fun n => hXc (φ n)) (fun n => hX (φ n)) (fun n => hinit (φ n))
    (fun n => hright (φ n)) (fun n => hleft (φ n))
    (fun n => hM (φ n)) (fun n => hlip (φ n))
  let Z : ℕ → Icc (0 : ℝ) T → R2 → R2 := fun n t a => Y (φ (ψ n)) t a
  have hZc (n : ℕ) : Continuous (Function.uncurry (Z n)) :=
    (hYc (φ (ψ n))).comp
      ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
  have hZlat (n : ℕ) (t : Icc (0 : ℝ) T) (a : R2) (k : Fin 2 → ℤ) :
      Z n t (a + torusLatticeShift k) = Z n t a + torusLatticeShift k :=
    hYlat (φ (ψ n)) t a k
  obtain ⟨G, hGc, hGlat, hGlim⟩ := lift_uniform_periodic_map_limit hR Z hZc hZlat g hψlim
  have hFlim' : TendstoUniformly
      (fun n (p : Icc (0 : ℝ) T × R2) => X (φ (ψ n)) p.1 p.2) F atTop := by
    rw [Metric.tendstoUniformly_iff] at hFlim ⊢
    intro ε hε
    exact hψ.tendsto_atTop.eventually (hFlim ε hε)
  obtain ⟨hFG, hGF⟩ := inverse_pair_of_uniform_particle_limits hFc hGc hFlim' hGlim
    (fun n => hright (φ (ψ n))) (fun n => hleft (φ (ψ n)))
  refine ⟨F, G, hFc, hGc, hFMP, ?_, hFinit, ?_, hFlat, hGlat, hFG, hGF,
    φ ∘ ψ, hφ.comp hψ, hFlim', hGlim⟩
  · intro t
    apply torusAreaPreserving_of_ae_tendsto (fun n => hYMP (φ (ψ n)) t t.property)
      (hGc.comp (continuous_const.prodMk continuous_id)).measurable
    exact Eventually.of_forall fun a => hGlim.tendsto_at (t, a)
  · intro a
    have he := hGF (⟨0, le_rfl, hT⟩ : Icc (0 : ℝ) T) a
    rw [hFinit a] at he
    exact he

end Euler2D

end
