module

public import RequestProject.Euler.WeakAux

/-!
# Weak closure of bounds on higher Lebesgue norms

An `Lᵖ` norm ball, viewed as a subset of scalar `L²`, is strongly closed
by Fatou's lemma and convex by Minkowski's inequality. A closed convex
subset of a real Hilbert space contains the weak limit of its elements.
These facts pass the vorticity bound to a weak `L²` limit.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace Euler2D

/-- A closed convex subset of a real Hilbert space contains every weak
limit of a sequence in that subset. -/
theorem mem_closed_convex_of_inner_tendsto
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {s : Set E} (hs : IsClosed s) (hc : Convex ℝ s)
    {f : ℕ → E} {v : E} (hf : ∀ n, f n ∈ s)
    (hlim : ∀ g : E, Tendsto (fun n => inner ℝ (f n) g) atTop (𝓝 (inner ℝ v g))) :
    v ∈ s := by
  obtain ⟨w, hw, hmin⟩ := exists_norm_eq_iInf_of_complete_convex
    ⟨f 0, hf 0⟩ hs.isComplete hc v
  have hproj := (norm_eq_iInf_iff_real_inner_le_zero hc hw).mp hmin
  have ht : Tendsto (fun n => inner ℝ (v - w) (f n - w)) atTop
      (𝓝 (inner ℝ (v - w) (v - w))) := by
    simpa only [inner_sub_right, real_inner_comm] using
      (hlim (v - w)).sub_const (inner ℝ w (v - w))
  have hnonpos : inner ℝ (v - w) (v - w) ≤ 0 :=
    le_of_tendsto ht (Eventually.of_forall fun n => hproj (f n) (hf n))
  have heq : v = w := by
    apply sub_eq_zero.mp
    apply (inner_self_eq_zero (𝕜 := ℝ)).mp
    exact le_antisymm hnonpos (real_inner_self_nonneg)
  rwa [heq]

/-- A bound on any Lebesgue exponent is closed for strong `L²`
convergence, even when the exponent is larger than two. -/
theorem isClosed_eLpNorm_ball
    {α F : Type*} [MeasurableSpace α] [NormedAddCommGroup F]
    (μ : Measure α) (q : ENNReal) (C : ENNReal) :
    IsClosed {f : Lp F 2 μ | eLpNorm f q μ ≤ C} := by
  apply IsSeqClosed.isClosed
  intro f v hf hv
  exact eLpNorm_le_of_tendstoInMeasure (Eventually.of_forall hf)
    (tendstoInMeasure_of_tendsto_Lp hv) (fun n => Lp.aestronglyMeasurable (f n))

/-- The higher Lebesgue norm ball is convex as a subset of scalar `L²`. -/
theorem convex_eLpNorm_ball
    {α : Type*} [MeasurableSpace α] (μ : Measure α)
    {q : ENNReal} (hq : 1 ≤ q) (M : ℝ) :
    Convex ℝ {f : Lp ℝ 2 μ | eLpNorm f q μ ≤ ENNReal.ofReal M} := by
  intro f hf g hg a b ha hb hab
  change eLpNorm f q μ ≤ ENNReal.ofReal M at hf
  change eLpNorm g q μ ≤ ENNReal.ofReal M at hg
  change eLpNorm (a • f + b • g : Lp ℝ 2 μ) q μ ≤ ENNReal.ofReal M
  have heq : (a • f + b • g : Lp ℝ 2 μ) =ᵐ[μ]
      (fun x => a • f x + b • g x) := by
    filter_upwards [Lp.coeFn_add (a • f) (b • g), Lp.coeFn_smul a f,
      Lp.coeFn_smul b g] with x hadd ha' hb'
    rw [hadd]
    change (a • f : Lp ℝ 2 μ) x + (b • g : Lp ℝ 2 μ) x = _
    rw [ha', hb']
    rfl
  rw [eLpNorm_congr_ae heq]
  calc
    eLpNorm (fun x => a • f x + b • g x) q μ ≤
        eLpNorm (a • (f : α → ℝ)) q μ + eLpNorm (b • (g : α → ℝ)) q μ :=
      eLpNorm_add_le hq
    _ = ENNReal.ofReal a * eLpNorm f q μ + ENNReal.ofReal b * eLpNorm g q μ := by
      rw [eLpNorm_const_smul, eLpNorm_const_smul]
      rw [← ofReal_norm a, ← ofReal_norm b, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg ha, abs_of_nonneg hb]
    _ ≤ ENNReal.ofReal a * ENNReal.ofReal M +
        ENNReal.ofReal b * ENNReal.ofReal M := by gcongr
    _ = ENNReal.ofReal M := by
      rw [← add_mul, ← ENNReal.ofReal_add ha hb, hab]
      simp

/-- Higher Lebesgue bounds are retained by weak scalar `L²` limits. -/
theorem eLpNorm_le_of_inner_tendsto
    {α : Type*} [MeasurableSpace α] (μ : Measure α)
    {q : ENNReal} (hq : 1 ≤ q) {M : ℝ}
    {f : ℕ → Lp ℝ 2 μ} {v : Lp ℝ 2 μ}
    (hf : ∀ n, eLpNorm (f n) q μ ≤ ENNReal.ofReal M)
    (hlim : ∀ g : Lp ℝ 2 μ,
      Tendsto (fun n => inner ℝ (f n) g) atTop (𝓝 (inner ℝ v g))) :
    eLpNorm v q μ ≤ ENNReal.ofReal M :=
  mem_closed_convex_of_inner_tendsto (isClosed_eLpNorm_ball μ q (ENNReal.ofReal M))
    (convex_eLpNorm_ball μ hq M) hf hlim

end Euler2D

end
