module

public import Mathlib.Analysis.ODE.PicardLindelof
public import Mathlib.Analysis.ODE.ExistUnique

/-! Actual local integral curves for locally Lipschitz vector fields on
open subsets of a real Banach space. No differentiability of the vector
field is assumed merely to obtain the local solution. -/

@[expose] public section

noncomputable section

open Set Filter Topology Metric
open scoped NNReal

namespace Euler2D

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem exists_local_curve_of_lipschitzOn_nhds (F : E → E) (x : E)
    {K : ℝ≥0} {U : Set E} (hU : U ∈ 𝓝 x) (hLip : LipschitzOnWith K F U) :
    ∃ T > 0, ∃ α : ℝ → E, α 0 = x ∧
      ∀ t ∈ Ioo (-T) T, HasDerivAt α (F (α t)) t := by
  obtain ⟨a, ha, hball⟩ := Metric.mem_nhds_iff.mp hU
  let L : ℝ := (K : ℝ) * a + ‖F x‖ + 1
  have hL : 0 < L := by dsimp only [L]; positivity
  have hb (y : E) (hy : y ∈ closedBall x (a / 2)) : ‖F y‖ ≤ L := by
    have hyU : y ∈ U := hball (closedBall_subset_ball (half_lt_self ha) hy)
    have hxU : x ∈ U := mem_of_mem_nhds hU
    have hd := hLip.dist_le_mul y hyU x hxU
    have hdist : dist y x ≤ a := (mem_closedBall.mp hy).trans (half_le_self ha.le)
    calc
      ‖F y‖ ≤ ‖F y - F x‖ + ‖F x‖ := norm_le_norm_sub_add _ _
      _ ≤ (K : ℝ) * a + ‖F x‖ := by
        rw [← dist_eq_norm]
        exact add_le_add (hd.trans (mul_le_mul_of_nonneg_left hdist K.coe_nonneg)) le_rfl
      _ ≤ L := le_add_of_nonneg_right zero_le_one
  let T := a / (2 * L)
  have hT : 0 < T := div_pos ha (mul_pos (by norm_num) hL)
  let t₀ : Icc (-T) T := ⟨0, by constructor <;> linarith⟩
  have hpl : IsPicardLindelof (fun _ : ℝ => F) t₀ x
      (⟨a / 2, (half_pos ha).le⟩ : ℝ≥0) 0 ⟨L, hL.le⟩ K := by
    apply IsPicardLindelof.of_time_independent hb
      (hLip.mono ((closedBall_subset_ball (half_lt_self ha)).trans hball))
    change L * max (T - 0) (0 - -T) ≤ a / 2 - 0
    simp only [sub_zero, zero_sub, neg_neg, max_self]
    dsimp only [T]
    field_simp
    ring_nf
    exact le_rfl
  obtain ⟨α, hα0, hd⟩ := hpl.exists_eq_forall_mem_Icc_hasDerivWithinAt₀
  refine ⟨T, hT, α, hα0, ?_⟩
  intro t ht
  exact (hd t ⟨ht.1.le, ht.2.le⟩).hasDerivAt (Icc_mem_nhds ht.1 ht.2)

def openSubtypeFieldExtension (U : Set E) (F : U → E) (y : E) : E := by
  classical
  exact if hy : y ∈ U then F ⟨y, hy⟩ else 0

@[simp] theorem openSubtypeFieldExtension_of_mem {U : Set E} (F : U → E)
    (y : U) : openSubtypeFieldExtension U F y.val = F y := by
  classical
  simp only [openSubtypeFieldExtension, dif_pos y.property]

theorem exists_local_curve_on_open_subtype {U : Set E} (hU : IsOpen U)
    (F : U → E) (hF : LocallyLipschitz F) (x : U) :
    ∃ T > 0, ∃ α : ℝ → E, α 0 = x.val ∧
      ∀ t ∈ Ioo (-T) T, ∃ ht : α t ∈ U, HasDerivAt α (F ⟨α t, ht⟩) t := by
  classical
  obtain ⟨K, V, hV, hLip⟩ := hF x
  have himage : (Subtype.val '' V : Set E) ∈ 𝓝 x.val := by
    rw [← map_nhds_subtype_coe_eq_nhds x.property (hU.mem_nhds x.property)]
    exact image_mem_map hV
  let G := openSubtypeFieldExtension U F
  have hG : LipschitzOnWith K G (Subtype.val '' V) := by
    rintro y ⟨v, hv, rfl⟩ z ⟨w, hw, rfl⟩
    simpa only [G, openSubtypeFieldExtension_of_mem, Subtype.edist_eq] using hLip hv hw
  obtain ⟨T, hT, α, hα0, hd⟩ := exists_local_curve_of_lipschitzOn_nhds G x.val himage hG
  have hαc : ContinuousAt α 0 := (hd 0 (by constructor <;> linarith)).continuousAt
  have hn : ∀ᶠ t in 𝓝 (0 : ℝ), α t ∈ U :=
    hαc (hU.mem_nhds (by rw [hα0]; exact x.property))
  obtain ⟨σ, hσ, hσU⟩ := Metric.mem_nhds_iff.mp hn
  refine ⟨min T σ, lt_min hT hσ, α, hα0, ?_⟩
  intro t ht
  have htT : t ∈ Ioo (-T) T :=
    ⟨(neg_le_neg (min_le_left T σ)).trans_lt ht.1, ht.2.trans_le (min_le_left T σ)⟩
  have htσ : t ∈ ball (0 : ℝ) σ := by
    rw [mem_ball, Real.dist_eq, sub_zero, abs_lt]
    exact ⟨(neg_le_neg (min_le_right T σ)).trans_lt ht.1, ht.2.trans_le (min_le_right T σ)⟩
  have htU : α t ∈ U := hσU htσ
  refine ⟨htU, ?_⟩
  simpa only [G, openSubtypeFieldExtension, dif_pos htU] using hd t htT

end Euler2D

end
