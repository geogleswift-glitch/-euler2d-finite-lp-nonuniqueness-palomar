module

public import RequestProject.Euler.BanachOpenODEUniqueness

/-! Commutation with a fixed linear field symmetry at a shifted time.
The two flows may have different initial neighborhoods and horizons;
every comparison is proved from their actual ODEs on the given domain. -/

@[expose] public section

noncomputable section

open Set Filter Topology Metric
open scoped NNReal ContDiff

namespace Euler2D

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem IsBanachFlowOn.shift_symmetry_commute
    {f : E → E} {U V W : Set E} {T H : ℝ} {X Y : E → ℝ → E}
    (hX : IsBanachFlowOn f U V T X) (hY : IsBanachFlowOn f U W H Y)
    (hU : IsOpen U) (hf : ContDiffOn ℝ 1 f U) (hT : 0 ≤ T)
    (L : E →L[ℝ] E) (hLU : ∀ z ∈ U, L z ∈ U)
    (hLf : ∀ z ∈ U, f (L z) = L (f z))
    {b : E} (hbV : b ∈ V) (hbW : b ∈ W) {t : ℝ} (ht : 0 ≤ t)
    (hH : t + T ≤ H) (hreturn : X b T ∈ W) (hshift : L (Y b t) ∈ V) :
    X (L (Y b t)) T = L (Y (X b T) t) := by
  have hTH : T ≤ H := by linarith
  have htH : t ≤ H := by linarith
  have hXY : EqOn (X b) (Y b) (Icc (0 : ℝ) T) := by
    apply eqOn_of_banachODE_open hU hf (hX.continuous b hbV)
      ((hY.continuous b hbW).mono (Icc_subset_Icc_right hTH))
      (hX.mem b hbV) (fun s hs => hY.mem b hbW s ⟨hs.1, hs.2.trans hTH⟩)
      (fun s hs => hX.hasDerivAt b hbV s ⟨hs.1, hs.2.le⟩)
      (fun s hs => hY.hasDerivAt b hbW s ⟨hs.1, hs.2.le.trans hTH⟩)
    rw [hX.initial b hbV, hY.initial b hbW]
  have htime₁ (s : ℝ) (hs : s ∈ Icc (0 : ℝ) T) : t + s ∈ Icc (0 : ℝ) H := by
    constructor <;> linarith [hs.1, hs.2]
  have hc₁ : ContinuousOn (fun s => Y b (t + s)) (Icc (0 : ℝ) T) :=
    (hY.continuous b hbW).comp (continuous_const.add continuous_id).continuousOn htime₁
  have hd₁ (s : ℝ) (hs : s ∈ Icc (0 : ℝ) T) :
      HasDerivAt (fun u => L (Y b (t + u))) (f (L (Y b (t + s)))) s := by
    have hd := (hY.hasDerivAt b hbW (t + s) (htime₁ s hs)).scomp s
      ((hasDerivAt_const s t).add (hasDerivAt_id s))
    have he : HasDerivAt (fun u => Y b (t + u)) (f (Y b (t + s))) s := by
      simpa only [Function.comp_def, Pi.add_apply, id_eq, zero_add, one_smul] using hd
    have hh := L.hasFDerivAt.comp_hasDerivAt s he
    change HasDerivAt (fun u => L (Y b (t + u))) (L (f (Y b (t + s)))) s at hh
    rw [← hLf _ (hY.mem b hbW _ (htime₁ s hs))] at hh
    exact hh
  have he₁ : EqOn (X (L (Y b t))) (fun s => L (Y b (t + s))) (Icc (0 : ℝ) T) := by
    apply eqOn_of_banachODE_open hU hf (hX.continuous _ hshift)
      (L.continuous.comp_continuousOn hc₁) (hX.mem _ hshift)
      (fun s hs => hLU _ (hY.mem b hbW _ (htime₁ s hs)))
      (fun s hs => hX.hasDerivAt _ hshift s ⟨hs.1, hs.2.le⟩)
      (fun s hs => hd₁ s ⟨hs.1, hs.2.le⟩)
    change X (L (Y b t)) 0 = L (Y b (t + 0))
    rw [hX.initial _ hshift, add_zero]
  have htime₂ (s : ℝ) (hs : s ∈ Icc (0 : ℝ) t) : T + s ∈ Icc (0 : ℝ) H := by
    constructor <;> linarith [hs.1, hs.2]
  have hc₂ : ContinuousOn (fun s => Y b (T + s)) (Icc (0 : ℝ) t) :=
    (hY.continuous b hbW).comp (continuous_const.add continuous_id).continuousOn htime₂
  have hd₂ (s : ℝ) (hs : s ∈ Icc (0 : ℝ) t) :
      HasDerivAt (fun u => Y b (T + u)) (f (Y b (T + s))) s := by
    have hd := (hY.hasDerivAt b hbW (T + s) (htime₂ s hs)).scomp s
      ((hasDerivAt_const s T).add (hasDerivAt_id s))
    simpa only [Function.comp_def, Pi.add_apply, id_eq, zero_add, one_smul] using hd
  have he₂ : EqOn (Y (X b T)) (fun s => Y b (T + s)) (Icc (0 : ℝ) t) := by
    apply eqOn_of_banachODE_open hU hf
      ((hY.continuous _ hreturn).mono (Icc_subset_Icc_right htH)) hc₂
      (fun s hs => hY.mem _ hreturn s ⟨hs.1, hs.2.trans htH⟩)
      (fun s hs => hY.mem b hbW _ (htime₂ s hs))
      (fun s hs => hY.hasDerivAt _ hreturn s ⟨hs.1, hs.2.le.trans htH⟩)
      (fun s hs => hd₂ s ⟨hs.1, hs.2.le⟩)
    change Y (X b T) 0 = Y b (T + 0)
    rw [hY.initial _ hreturn, add_zero]
    exact hXY ⟨hT, le_rfl⟩
  calc
    X (L (Y b t)) T = L (Y b (t + T)) := he₁ ⟨hT, le_rfl⟩
    _ = L (Y b (T + t)) := by rw [add_comm t T]
    _ = L (Y (X b T) t) := congrArg L (he₂ ⟨ht, le_rfl⟩).symm

end Euler2D

end
