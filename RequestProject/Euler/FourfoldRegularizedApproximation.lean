module

public import RequestProject.Euler.FourfoldRegularizedParticleSystem
public import RequestProject.Euler.PeriodicParticleLimit

/-!
# Common bounds and simultaneous limits for actual fourfold-kernel systems

The genuine smooth systems are explicit parameters.  This lets the
construction retain additional properties of the chosen witnesses,
including rotation equivariance, through the common subsequence.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology Metric
open scoped NNReal ENNReal

namespace Euler2D

theorem exists_uniform_bounds_fourfoldRegularizedFamily
    {w : R2 → ℝ} {T B : ℝ}
    (ε : ℕ → ℝ) (hε : ∀ n, 0 < ε n) (hε1 : ∀ n, ε n ≤ 1) {L M : ℕ → ℝ≥0}
    (S : ∀ n, SmoothRegularizedParticleSystem (fourfoldRegularizedTorusKernel (ε n) (hε n))
      w T (L n) (M n))
    (hw : AEStronglyMeasurable w μT) (hB0 : 0 ≤ B) (hB : ∀ᵐ y ∂μT, ‖w y‖ ≤ B) :
    ∃ C V : ℝ, 0 ≤ C ∧ 0 ≤ V ∧
      (∀ n t, t ∈ Icc (0 : ℝ) T → ∀ x, ‖(S n).velocity t x‖ ≤ V) ∧
      ∀ n t, t ∈ Icc (0 : ℝ) T → ∀ x z, ‖x - z‖ ≤ 1 / 2 →
        ‖(S n).velocity t x - (S n).velocity t z‖ ≤ C * logFlowModulus ‖x - z‖ := by
  obtain ⟨C, hC, hbound⟩ := exists_uniform_logLip_fourfoldRegularizedParticleVelocity
  refine ⟨B * C, B * ∫ y in torusBox, ‖torusBiotSavartKernel y‖,
    mul_nonneg hB0 hC, mul_nonneg hB0 (integral_nonneg fun _ => norm_nonneg _), ?_, ?_⟩
  · intro n t ht x
    exact norm_fourfoldRegularizedParticleVelocity_le (hε n) (hε1 n) (S n) hB0 hB ht x
  · intro n t ht x z hxz
    exact hbound (ε n) (hε n) (hε1 n) w T _ _ (S n) B hw hB0 hB t ht x z hxz

theorem uniform_subseq_fourfoldRegularizedParticleSystem_pair
    {w : R2 → ℝ} {T B : ℝ} (hT : 0 ≤ T)
    (ε : ℕ → ℝ) (hε : ∀ n, 0 < ε n) (hε1 : ∀ n, ε n ≤ 1) {L M : ℕ → ℝ≥0}
    (S : ∀ n, SmoothRegularizedParticleSystem (fourfoldRegularizedTorusKernel (ε n) (hε n))
      w T (L n) (M n))
    (hw : AEStronglyMeasurable w μT) (hB0 : 0 ≤ B) (hB : ∀ᵐ y ∂μT, ‖w y‖ ≤ B) :
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
        TendstoUniformly
          (fun n (p : Icc (0 : ℝ) T × R2) => (S (φ n)).forward p.1 p.2) F atTop ∧
        TendstoUniformly
          (fun n (p : Icc (0 : ℝ) T × R2) => (S (φ n)).backward p.1 p.2) G atTop := by
  obtain ⟨C, V, hC, hV0, hV, hlip⟩ :=
    exists_uniform_bounds_fourfoldRegularizedFamily ε hε hε1 S hw hB0 hB
  exact uniform_subseq_periodic_particle_pair hT hC hV0
    (fun n => (S n).velocity) (fun n => (S n).forward) (fun n => (S n).backward)
    (fun n => (S n).forward_continuous) (fun n => (S n).backward_continuous)
    (fun n => (S n).derivative) (fun n => (S n).initial)
    (fun n => (S n).forward_backward) (fun n => (S n).backward_forward)
    hV hlip (fun n => (S n).forward_lattice) (fun n => (S n).backward_lattice)
    (fun n => (S n).forward_area) (fun n t _ => (S n).backward_area t)

end Euler2D

end
