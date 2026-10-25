module

public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Analysis.Normed.Module.WeakDual

/-!
# Weak subsequences in a separable real Hilbert space

Sequential Banach–Alaoglu, transported through the Fréchet–Riesz isometry,
provides bounded weakly convergent subsequences. The topology is exposed as
convergence of scalar inner products so downstream applications do not need
to handle either of the dual-space type synonyms.
-/

@[expose] public section

open Filter Topology

namespace Euler2D

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A weak limit retains every eventual uniform norm bound. -/
theorem norm_le_of_inner_tendsto {U : ℕ → E} {v : E} {M : ℝ}
    (hU : ∀ᶠ n in atTop, ‖U n‖ ≤ M)
    (hweak : ∀ g : E,
      Tendsto (fun n => inner ℝ (U n) g) atTop (𝓝 (inner ℝ v g))) :
    ‖v‖ ≤ M := by
  have hM : 0 ≤ M := by
    obtain ⟨n, hn⟩ := hU.exists
    exact (norm_nonneg _).trans hn
  have hsq : ‖v‖ ^ 2 ≤ M * ‖v‖ := by
    have hi : ∀ᶠ n in atTop, inner ℝ (U n) v ≤ M * ‖v‖ := by
      filter_upwards [hU] with n hn
      exact (real_inner_le_norm (U n) v).trans
        (mul_le_mul_of_nonneg_right hn (norm_nonneg v))
    simpa only [real_inner_self_eq_norm_sq] using
      le_of_tendsto (hweak v) hi
  nlinarith [norm_nonneg v]

/-- Inner-product weak convergence implies convergence under every continuous
real linear functional. -/
theorem tendsto_apply_of_inner_tendsto [CompleteSpace E]
    {U : ℕ → E} {v : E}
    (hweak : ∀ g : E,
      Tendsto (fun n => inner ℝ (U n) g) atTop (𝓝 (inner ℝ v g)))
    (ℓ : E →L[ℝ] ℝ) : Tendsto (fun n => ℓ (U n)) atTop (𝓝 (ℓ v)) := by
  have h := hweak ((InnerProductSpace.toDual ℝ E).symm ℓ)
  have hrepr (x : E) : inner ℝ x ((InnerProductSpace.toDual ℝ E).symm ℓ) = ℓ x := by
    rw [real_inner_comm]
    exact InnerProductSpace.toDual_symm_apply
  simpa only [hrepr] using h

/-- Every bounded sequence in a separable real Hilbert space has a weakly
convergent subsequence, and its limit lies in the same closed norm ball. -/
theorem exists_weakly_convergent_subsequence [CompleteSpace E]
    [TopologicalSpace.SeparableSpace E]
    (U : ℕ → E) (M : ℝ) (hU : ∀ n, ‖U n‖ ≤ M) :
    ∃ v : E, ‖v‖ ≤ M ∧ ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∀ g : E, Tendsto (fun n => inner ℝ (U (φ n)) g) atTop (𝓝 (inner ℝ v g)) := by
  let W : ℕ → WeakDual ℝ E :=
    fun n => StrongDual.toWeakDual (InnerProductSpace.toDual ℝ E (U n))
  have hW : ∀ n, W n ∈
      WeakDual.toStrongDual ⁻¹' Metric.closedBall (0 : StrongDual ℝ E) M := by
    intro n
    rw [Set.mem_preimage, mem_closedBall_zero_iff]
    simpa [W] using hU n
  obtain ⟨w, hw, φ, hφ, hlim⟩ :=
    WeakDual.isSeqCompact_closedBall ℝ E (0 : StrongDual ℝ E) M hW
  let v : E := (InnerProductSpace.toDual ℝ E).symm (WeakDual.toStrongDual w)
  refine ⟨v, ?_, φ, hφ, ?_⟩
  · rw [Set.mem_preimage, mem_closedBall_zero_iff] at hw
    simpa [v] using hw
  · intro g
    have h := ((WeakDual.eval_continuous g).tendsto w).comp hlim
    simpa [W, v, Function.comp_def, InnerProductSpace.toDual_symm_apply] using h

end Euler2D

end

