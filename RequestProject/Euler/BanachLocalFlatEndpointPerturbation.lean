module

public import Mathlib

@[expose] public section

set_option maxHeartbeats 1800000

noncomputable section

namespace Euler2D

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem local_flattened_bounds_of_endpoint_perturbation
    (F : E → E) (L P : E →L[ℝ] E) (g U : E → E)
    {lam C s d B : ℝ} (hLam : 0 ≤ lam) (hC : 0 < C) (hs : 0 < s)
    (hd : 0 < d) (hB : 0 < B) (hU : ∀ α, ‖U α‖ = lam * ‖α‖)
    (hLip : ∀ u v, ‖P u‖ ≤ d → ‖P v‖ ≤ d →
      ‖(v - P v - g (P v)) - (u - P u - g (P u))‖ ≤ B * ‖v - u‖)
    (hflat : ∀ α w, P α = α → P w = 0 → ‖α‖ + ‖w‖ ≤ s →
      let z := α + g α + w
      ‖P (F z) - U α‖ ≤ C * (‖α‖ + ‖w‖) ^ 2 ∧
      ‖(F z - P (F z)) - g (P (F z)) - L w‖ ≤ C * (‖α‖ + ‖w‖) * ‖w‖) :
    ∃ t > 0, t ≤ s ∧ ∃ η₀ > 0, ∀ α w, P α = α → P w = 0 → ‖α‖ + ‖w‖ ≤ t →
      let z := α + g α + w
      ∀ v {η : ℝ}, 0 ≤ η → η ≤ η₀ → ‖v - F z‖ ≤ η →
        ‖P v - U α‖ ≤ C * (‖α‖ + ‖w‖) ^ 2 + ‖P‖ * η ∧
        ‖(v - P v) - g (P v) - L w‖ ≤ C * (‖α‖ + ‖w‖) * ‖w‖ + B * η := by
  let D : ℝ := lam + C + 1
  have hD : 0 < D := by dsimp only [D]; positivity
  let t : ℝ := min s (min 1 (d / (4 * D)))
  have ht : 0 < t := by dsimp only [t]; positivity
  let η₀ : ℝ := d / (4 * (‖P‖ + 1))
  have hη₀ : 0 < η₀ := by dsimp only [η₀]; positivity
  refine ⟨t, ht, min_le_left _ _, η₀, hη₀, ?_⟩
  intro α w hα hw hsize
  let size := ‖α‖ + ‖w‖
  let z := α + g α + w
  have hsize0 : 0 ≤ size := by dsimp only [size]; positivity
  have hsizes : size ≤ s := hsize.trans (min_le_left _ _)
  have hsize1 : size ≤ 1 := hsize.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hsizeSquare : size ^ 2 ≤ size := by
    have hh := mul_nonneg hsize0 (sub_nonneg.mpr hsize1)
    nlinarith only [hh]
  have hsizeD : size ≤ d / (4 * D) := hsize.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hDbound : D * size ≤ d / 4 := by
    have hh := (le_div_iff₀ (by positivity : 0 < 4 * D)).mp hsizeD
    linarith only [hh]
  have hαsize : ‖α‖ ≤ size := le_add_of_nonneg_right (norm_nonneg w)
  have hbase := hflat α w hα hw hsizes
  have hPu : ‖P (F z)‖ ≤ d / 4 := by
    calc
      _ ≤ ‖P (F z) - U α‖ + ‖U α‖ := norm_le_norm_sub_add _ _
      _ ≤ C * size ^ 2 + lam * ‖α‖ := by rw [hU]; exact add_le_add hbase.1 le_rfl
      _ ≤ C * size + lam * size := add_le_add
        (mul_le_mul_of_nonneg_left hsizeSquare hC.le) (mul_le_mul_of_nonneg_left hαsize hLam)
      _ ≤ D * size := by dsimp only [D]; nlinarith only [hsize0]
      _ ≤ d / 4 := hDbound
  dsimp only
  intro v η hη hηcap herror
  have hPη : ‖P‖ * η ≤ d / 4 := by
    have hh := (le_div_iff₀ (by positivity : 0 < 4 * (‖P‖ + 1))).mp hηcap
    nlinarith only [hh, hη]
  have hPerror : ‖P v - P (F z)‖ ≤ ‖P‖ * η := by
    rw [← P.map_sub]
    exact (P.le_opNorm _).trans (mul_le_mul_of_nonneg_left herror (norm_nonneg P))
  have hPv : ‖P v‖ ≤ d := by
    have hh := norm_le_norm_sub_add (P v) (P (F z))
    linarith only [hh, hPerror, hPη, hPu, hd]
  have hPu' : ‖P (F z)‖ ≤ d := hPu.trans (by linarith)
  have hfd : ‖(v - P v - g (P v)) - (F z - P (F z) - g (P (F z)))‖ ≤ B * η :=
    (hLip (F z) v hPu' hPv).trans (mul_le_mul_of_nonneg_left herror hB.le)
  constructor
  · exact ((norm_sub_le_norm_sub_add_norm_sub (P v) (P (F z)) (U α)).trans_eq
      (add_comm _ _)).trans (add_le_add hbase.1 hPerror)
  · exact ((norm_sub_le_norm_sub_add_norm_sub (v - P v - g (P v))
      (F z - P (F z) - g (P (F z))) (L w)).trans_eq (add_comm _ _)).trans
        (add_le_add hbase.2 hfd)

end Euler2D

end
