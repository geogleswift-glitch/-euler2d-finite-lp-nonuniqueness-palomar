module

public import RequestProject.Euler.Compactness

/-!
# Compactness from separating weak tests

On a compact set of states, a continuous separating family of real tests
determines the original uniform topology.  Equicontinuity of every tested
path therefore implies equicontinuity of the state-valued paths.  An
Arzelà--Ascoli theorem then gives a subsequence converging uniformly in the
original state-space metric, without a common state-space Lipschitz bound.
-/

@[expose] public section

noncomputable section

open Set Filter Topology
open scoped BoundedContinuousFunction UniformConvergence

namespace Euler2D

/-- A continuous injection from a compact uniform space into a Hausdorff
uniform space preserves and reflects the uniform structure. -/
theorem compact_continuous_injective_isUniformEmbedding
    {X Y : Type*} [UniformSpace X] [CompactSpace X] [UniformSpace Y] [T2Space Y]
    {g : X → Y} (hg : Continuous g) (hinj : Function.Injective g) :
    IsUniformEmbedding g := by
  let e : X ≃ₜ range g := (hg.isClosedEmbedding hinj).isEmbedding.toHomeomorph
  letI : CompactSpace (range g) := isCompact_iff_compactSpace.mp (isCompact_range hg)
  let eu : X ≃ᵤ range g :=
    { e.toEquiv with
      uniformContinuous_toFun := CompactSpace.uniformContinuous_of_continuous e.continuous
      uniformContinuous_invFun := CompactSpace.uniformContinuous_of_continuous e.symm.continuous }
  exact isUniformEmbedding_subtype_val.comp eu.isUniformEmbedding

/-- Coordinatewise equicontinuity is equicontinuity into the product
uniformity.  The index set of tests need not be countable. -/
theorem equicontinuous_pi_of_coordinates
    {κ A ι : Type*} [TopologicalSpace A] {F : κ → A → ι → ℝ}
    (hF : ∀ i, Equicontinuous (fun n a => F n a i)) : Equicontinuous F := by
  apply equicontinuous_iff_continuous.mpr
  let e : (κ →ᵤ (ι → ℝ)) ≃ᵤ (ι → κ →ᵤ ℝ) :=
    UniformFun.uniformEquivPiComm κ (fun _ : ι => ℝ)
  have hpi : Continuous (fun a : A => fun i : ι =>
      UniformFun.ofFun (fun n : κ => F n a i)) :=
    continuous_pi fun i => equicontinuous_iff_continuous.mp (hF i)
  exact e.symm.uniformContinuous.continuous.comp hpi

/-- On a compact state set, separating continuous tests recover strong
equicontinuity from the equicontinuity of every scalar tested path. -/
theorem equicontinuous_of_compact_tests
    {κ A E ι : Type*} [TopologicalSpace A] [MetricSpace E]
    {K : Set E} (hK : IsCompact K) (T : E → ι → ℝ)
    (hT : ContinuousOn T K) (hinj : Set.InjOn T K)
    (U : κ → A → E) (hvalues : ∀ n a, U n a ∈ K)
    (htests : ∀ i, Equicontinuous (fun n a => T (U n a) i)) :
    Equicontinuous U := by
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let V : κ → A → K := fun n a => ⟨U n a, hvalues n a⟩
  let g : K → ι → ℝ := fun x => T x
  have hg : Continuous g := continuousOn_iff_continuous_restrict.mp hT
  have hginj : Function.Injective g := by
    intro x y hxy
    exact Subtype.ext (hinj x.property y.property hxy)
  have hgu := compact_continuous_injective_isUniformEmbedding hg hginj
  have htested : Equicontinuous (fun n a => g (V n a)) :=
    equicontinuous_pi_of_coordinates htests
  have hV : Equicontinuous V := hgu.isUniformInducing.equicontinuous_iff.mpr htested
  exact isUniformEmbedding_subtype_val.isUniformInducing.equicontinuous_iff.mp hV

/-- In particular, on a compact time domain the strong equicontinuity is
uniform in time. -/
theorem uniformEquicontinuous_of_compact_tests
    {κ A E ι : Type*} [UniformSpace A] [CompactSpace A] [MetricSpace E]
    {K : Set E} (hK : IsCompact K) (T : E → ι → ℝ)
    (hT : ContinuousOn T K) (hinj : Set.InjOn T K)
    (U : κ → A → E) (hvalues : ∀ n a, U n a ∈ K)
    (htests : ∀ i, Equicontinuous (fun n a => T (U n a) i)) :
    UniformEquicontinuous U :=
  CompactSpace.uniformEquicontinuous_of_equicontinuous
    (equicontinuous_of_compact_tests hK T hT hinj U hvalues htests)

/-- Arzelà--Ascoli for an equicontinuous sequence valued in an actual
compact set.  The ambient metric space need not be complete. -/
theorem uniform_subseq_of_equicontinuous_compact
    {A E : Type*} [TopologicalSpace A] [CompactSpace A] [MetricSpace E]
    (U : ℕ → A → E) (hU : Equicontinuous U)
    {K : Set E} (hK : IsCompact K) (hvalues : ∀ n a, U n a ∈ K) :
    ∃ u : A → E, Continuous u ∧ (∀ a, u a ∈ K) ∧ ∃ φ : ℕ → ℕ,
      StrictMono φ ∧ TendstoUniformly (fun n => U (φ n)) u atTop := by
  let F : ℕ → A →ᵇ E := fun n =>
    BoundedContinuousFunction.mkOfCompact ⟨U n, hU.continuous n⟩
  have hrange : Equicontinuous ((↑) : range F → A → E) := by
    intro x V hV
    filter_upwards [hU x V hV] with y hy f
    obtain ⟨n, hn⟩ := f.property
    change ((f : A →ᵇ E) x, (f : A →ᵇ E) y) ∈ V
    rw [← hn]
    exact hy n
  have hcompact : IsCompact (closure (range F)) :=
    BoundedContinuousFunction.arzela_ascoli K hK (range F)
      (fun f a hf => by
        obtain ⟨n, rfl⟩ := hf
        exact hvalues n a) hrange
  obtain ⟨f, _, φ, hφ, hlim⟩ := hcompact.isSeqCompact
    (fun n => subset_closure (mem_range_self n))
  have hlimU : TendstoUniformly (fun n => U (φ n)) f atTop :=
    BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mp hlim
  refine ⟨f, f.continuous, ?_, φ, hφ, hlimU⟩
  intro a
  exact hK.isClosed.mem_of_tendsto (hlimU.tendsto_at a)
    (Filter.Eventually.of_forall fun n => hvalues (φ n) a)

/-- Continuous separating tests on a compact state set give strong
uniform sequential compactness of paths from scalar equicontinuity alone. -/
theorem uniform_subseq_of_compact_tests
    {A E ι : Type*} [TopologicalSpace A] [CompactSpace A] [MetricSpace E]
    {K : Set E} (hK : IsCompact K) (T : E → ι → ℝ)
    (hT : ContinuousOn T K) (hinj : Set.InjOn T K)
    (U : ℕ → A → E) (hvalues : ∀ n a, U n a ∈ K)
    (htests : ∀ i, Equicontinuous (fun n a => T (U n a) i)) :
    ∃ u : A → E, Continuous u ∧ (∀ a, u a ∈ K) ∧ ∃ φ : ℕ → ℕ,
      StrictMono φ ∧ TendstoUniformly (fun n => U (φ n)) u atTop :=
  uniform_subseq_of_equicontinuous_compact U
    (equicontinuous_of_compact_tests hK T hT hinj U hvalues htests) hK hvalues

end Euler2D

end
