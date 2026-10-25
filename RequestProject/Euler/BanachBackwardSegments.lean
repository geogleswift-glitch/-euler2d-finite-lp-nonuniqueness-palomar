module

public import RequestProject.Euler.BanachFlowDerivative
public import RequestProject.Euler.BanachFlowGlobalVariational

/-! A true return sequence gives compatible finite ancient material
segments. The ODE is verified at every joining time using both actual
one-sided derivatives. -/

@[expose] public section

set_option maxHeartbeats 1500000

noncomputable section

open Set Filter Topology Metric

namespace Euler2D

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def banachBackwardSegment (X : E → ℝ → E) (T : ℝ) (z : ℕ → E) : ℕ → ℝ → E
  | 0 => X (z 0)
  | n + 1 => fun t => if t ≤ -(n : ℝ) * T then X (z (n + 1)) (t + (n + 1 : ℕ) * T)
      else banachBackwardSegment X T z n t

section ActualFlow

variable {f : E → E} {U V : Set E} {T : ℝ} {X : E → ℝ → E} {z : ℕ → E}
variable (hT : 0 < T) (hX : IsBanachFlowOn f U V T X) (hz : ∀ n, z n ∈ V)
variable (hreturn : ∀ n, X (z (n + 1)) T = z n)

include hT hX hz

theorem banachBackwardSegment_left (n : ℕ) :
    banachBackwardSegment X T z n (-(n : ℝ) * T) = z n := by
  cases n with
  | zero => simpa only [banachBackwardSegment, Nat.cast_zero, neg_zero, zero_mul] using hX.initial _ (hz 0)
  | succ n =>
    have hle : -((n + 1 : ℕ) : ℝ) * T ≤ -(n : ℝ) * T := by push_cast; nlinarith [hT]
    rw [banachBackwardSegment]
    dsimp only
    rw [if_pos hle]
    have he : -((n + 1 : ℕ) : ℝ) * T + (n + 1 : ℕ) * T = 0 := by ring
    rw [he, hX.initial _ (hz (n + 1))]

include hreturn

theorem banachBackwardSegment_succ_agrees (n : ℕ) {t : ℝ} (ht : -(n : ℝ) * T ≤ t) :
    banachBackwardSegment X T z (n + 1) t = banachBackwardSegment X T z n t := by
  rw [banachBackwardSegment]
  dsimp only
  by_cases hc : t ≤ -(n : ℝ) * T
  · have he : t = -(n : ℝ) * T := le_antisymm hc ht
    subst t
    rw [if_pos le_rfl, banachBackwardSegment_left hT hX hz]
    have hs : -(n : ℝ) * T + (n + 1 : ℕ) * T = T := by push_cast; ring
    rw [hs, hreturn]
  · rw [if_neg hc]

theorem banachBackwardSegment_zero (n : ℕ) : banachBackwardSegment X T z n 0 = z 0 := by
  induction n with
  | zero => exact hX.initial _ (hz 0)
  | succ n ih =>
    rw [banachBackwardSegment_succ_agrees hT hX hz hreturn n (by
      nlinarith [show (0 : ℝ) ≤ (n : ℝ) from Nat.cast_nonneg n, hT]), ih]

theorem banachBackwardSegment_agrees {m n : ℕ} (hmn : m ≤ n) {t : ℝ}
    (ht : -(m : ℝ) * T ≤ t) :
    banachBackwardSegment X T z n t = banachBackwardSegment X T z m t := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
  clear hmn
  induction k with
  | zero => simp only [add_zero]
  | succ k ih =>
    rw [show m + (k + 1) = (m + k) + 1 by omega]
    rw [banachBackwardSegment_succ_agrees hT hX hz hreturn (m + k) (by
      have hk : (m : ℝ) ≤ (m + k : ℕ) := by exact_mod_cast Nat.le_add_right m k
      nlinarith [hT]), ih]

theorem banachBackwardSegment_mem (n : ℕ) {t : ℝ} (ht : t ∈ Icc (-(n : ℝ) * T) 0) :
    banachBackwardSegment X T z n t ∈ U := by
  induction n with
  | zero =>
    have he : t = 0 := by
      have ht' : 0 ≤ t ∧ t ≤ 0 := by simpa only [Nat.cast_zero, neg_zero, zero_mul, mem_Icc] using ht
      exact le_antisymm ht'.2 ht'.1
    subst t
    exact hX.mem _ (hz 0) 0 ⟨le_rfl, hT.le⟩
  | succ n ih =>
    rw [banachBackwardSegment]
    dsimp only
    split_ifs with hc
    · apply hX.mem _ (hz (n + 1))
      constructor <;> push_cast at * <;> nlinarith [ht.1, ht.2]
    · exact ih ⟨(not_le.mp hc).le, ht.2⟩

theorem banachBackwardSegment_hasDerivAt (n : ℕ) {t : ℝ} (ht : t ∈ Icc (-(n : ℝ) * T) 0) :
    HasDerivAt (banachBackwardSegment X T z n)
      (f (banachBackwardSegment X T z n t)) t := by
  induction n generalizing t with
  | zero =>
    have he : t = 0 := by
      have ht' : 0 ≤ t ∧ t ≤ 0 := by simpa only [Nat.cast_zero, neg_zero, zero_mul, mem_Icc] using ht
      exact le_antisymm ht'.2 ht'.1
    subst t
    exact hX.hasDerivAt _ (hz 0) 0 ⟨le_rfl, hT.le⟩
  | succ n ih =>
    let c : ℝ := -(n : ℝ) * T
    let Y : ℝ → E := fun s => X (z (n + 1)) (s + (n + 1 : ℕ) * T)
    have hc0 : c ≤ 0 := by
      dsimp only [c]
      nlinarith [show (0 : ℝ) ≤ (n : ℝ) from Nat.cast_nonneg n, hT]
    have hYd (s : ℝ) (hs : s + (n + 1 : ℕ) * T ∈ Icc (0 : ℝ) T) :
        HasDerivAt Y (f (Y s)) s := by
      have h := (hX.hasDerivAt _ (hz (n + 1)) _ hs).scomp s
        ((hasDerivAt_id s).add_const ((n + 1 : ℕ) * T))
      simpa only [Y, Function.comp_def, id_eq, one_smul] using h
    have hjoin : Y c = banachBackwardSegment X T z n c := by
      dsimp only [Y, c]
      rw [show -(n : ℝ) * T + (n + 1 : ℕ) * T = T by push_cast; ring,
        hreturn, banachBackwardSegment_left hT hX hz]
    rcases lt_trichotomy t c with htc | rfl | hct
    · have he : banachBackwardSegment X T z (n + 1) =ᶠ[𝓝 t] Y := by
        filter_upwards [Iio_mem_nhds htc] with s hs
        exact if_pos hs.le
      have hd := hYd t (by constructor <;> dsimp only [c] at * <;>
        push_cast at * <;> nlinarith [ht.1, ht.2])
      have hp : banachBackwardSegment X T z (n + 1) t = Y t := if_pos htc.le
      rw [hp]
      exact hd.congr_of_eventuallyEq he
    · have hdY := hYd c (by
        rw [show c + (n + 1 : ℕ) * T = T by dsimp only [c]; push_cast; ring]
        exact ⟨hT.le, le_rfl⟩)
      have hdN := ih ⟨le_rfl, hc0⟩
      rw [← hjoin] at hdN
      have hd := hasDerivAt_banachVariational_glue hdY hdN hjoin
      change HasDerivAt (fun s => if s ≤ c then Y s else banachBackwardSegment X T z n s)
        (f (if c ≤ c then Y c else banachBackwardSegment X T z n c)) c
      simpa only [if_pos le_rfl] using hd
    · have he : banachBackwardSegment X T z (n + 1) =ᶠ[𝓝 t]
          banachBackwardSegment X T z n := by
        filter_upwards [Ioi_mem_nhds hct] with s hs
        exact if_neg (not_le.mpr hs)
      have hd := ih ⟨hct.le, ht.2⟩
      have hp : banachBackwardSegment X T z (n + 1) t = banachBackwardSegment X T z n t :=
        if_neg (not_le.mpr hct)
      rw [hp]
      exact hd.congr_of_eventuallyEq he

end ActualFlow

end Euler2D

end
