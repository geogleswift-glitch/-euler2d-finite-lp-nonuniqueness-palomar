module

public import Mathlib

/-! Actual compact-open subsequences on an entire locally compact
sigma-compact domain. Equicontinuity and pointwise compact range bounds
are proved inputs; no global compact spatial domain is imposed. -/

@[expose] public section

set_option maxHeartbeats 1500000

noncomputable section

open Set Filter Topology
open scoped UniformConvergence

namespace Euler2D

theorem exists_compactOpen_subseq_of_equicontinuous
    {X Y : Type*} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X] [SigmaCompactSpace X]
    [MetricSpace Y] [CompleteSpace Y]
    (U : ℕ → X → Y) (hU : Equicontinuous U)
    (hvalues : ∀ x : X, ∃ Q : Set Y, IsCompact Q ∧ ∀ n, U n x ∈ Q) :
    ∃ f : C(X, Y), ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Tendsto (fun n => (⟨U (φ n), hU.continuous (φ n)⟩ : C(X, Y))) atTop (𝓝 f) := by
  let F : ℕ → C(X, Y) := fun n => ⟨U n, hU.continuous n⟩
  letI : T2Space (X →ᵤ[{K | IsCompact K}] Y) :=
    UniformOnFun.t2Space_of_covering (by
      ext x
      simp only [mem_sUnion, mem_setOf_eq, mem_univ, iff_true]
      exact ⟨{x}, isCompact_singleton, mem_singleton x⟩)
  have hrange : Equicontinuous (fun f : range F => (f.val : X → Y)) := by
    intro x V hV
    filter_upwards [hU x V hV] with y hy f
    obtain ⟨n, hn⟩ := f.property
    change ((f.val : X → Y) x, (f.val : X → Y) y) ∈ V
    rw [← hn]
    exact hy n
  have hcompact : IsCompact (closure (range F)) := by
    apply ArzelaAscoli.isCompact_closure_of_isClosedEmbedding
      (F := fun f : C(X, Y) => (f : X → Y)) (𝔖 := {K | IsCompact K})
      (fun K hK => hK) ContinuousMap.isUniformEmbedding_toUniformOnFunIsCompact.isClosedEmbedding
      (fun K hK => hrange.equicontinuousOn K)
    intro K hK x hx
    obtain ⟨Q, hQ, hQvalues⟩ := hvalues x
    refine ⟨Q, hQ, ?_⟩
    intro f hf
    obtain ⟨n, rfl⟩ := hf
    exact hQvalues n
  obtain ⟨f, hf, φ, hφ, hlim⟩ := hcompact.isSeqCompact (fun n => subset_closure (mem_range_self n))
  exact ⟨f, φ, hφ, hlim⟩

end Euler2D

end
