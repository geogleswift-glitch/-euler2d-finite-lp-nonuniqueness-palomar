module

public import Mathlib

/-! A genuine first continuous section on the existing finite path.
It may lie inside a return block; no extension beyond the proven
finite horizon is used. -/

@[expose] public section

set_option maxHeartbeats 2500000

noncomputable section

open Set Metric

namespace Euler2D

theorem exists_first_continuous_norm_section
    {E : Type*} [NormedAddCommGroup E] {D δ : ℝ} (hD : 0 ≤ D)
    (y : ℝ → E) (hy : ContinuousOn y (Icc (0 : ℝ) D))
    (hstart : ‖y 0‖ < δ) (hend : δ ≤ ‖y D‖) :
    ∃ t ∈ Ioc (0 : ℝ) D, ‖y t‖ = δ ∧ ∀ s ∈ Ico (0 : ℝ) t, ‖y s‖ < δ := by
  let J := Icc (0 : ℝ) D
  letI : CompactSpace J := isCompact_iff_compactSpace.mp isCompact_Icc
  let q : J → ℝ := fun t => ‖y t.val‖
  have hqc : Continuous q := hy.norm.restrict
  have hclosed : IsClosed {t : J | δ ≤ q t} := isClosed_le continuous_const hqc
  have hne : ({t : J | δ ≤ q t} : Set J).Nonempty := ⟨⟨D, hD, le_rfl⟩, hend⟩
  obtain ⟨t₀, ht₀, hmin⟩ := hclosed.isCompact.exists_isMinOn hne
    (continuous_subtype_val.continuousOn : ContinuousOn (fun t : J => (t : ℝ)) {t : J | δ ≤ q t})
  have htpos : 0 < (t₀ : ℝ) := by
    by_contra hn
    have hz : (t₀ : ℝ) = 0 := le_antisymm (not_lt.mp hn) t₀.property.1
    have hh : δ ≤ ‖y 0‖ := by
      change δ ≤ ‖y (t₀ : ℝ)‖ at ht₀
      simpa only [hz] using ht₀
    exact (not_le.mpr hstart) hh
  have hvalue : ‖y t₀‖ = δ := by
    apply le_antisymm ?_ ht₀
    by_contra hn
    have hgt : δ < ‖y t₀‖ := lt_of_not_ge hn
    have hsub : Icc (0 : ℝ) (t₀ : ℝ) ⊆ Icc (0 : ℝ) D :=
      fun _ hs => ⟨hs.1, hs.2.trans t₀.property.2⟩
    obtain ⟨s, hs, heq⟩ := intermediate_value_Icc t₀.property.1 (hy.norm.mono hsub) ⟨hstart.le, hgt.le⟩
    have hmem : (⟨s, hs.1, hs.2.trans t₀.property.2⟩ : J) ∈ {t : J | δ ≤ q t} := by
      change δ ≤ ‖y s‖
      exact heq.ge
    have hsmin : (t₀ : ℝ) ≤ s := hmin hmem
    have hst : s = (t₀ : ℝ) := le_antisymm hs.2 hsmin
    rw [hst] at heq
    exact hgt.ne' heq
  refine ⟨t₀, ⟨htpos, t₀.property.2⟩, hvalue, ?_⟩
  intro s hs
  by_contra hn
  have hmem : (⟨s, hs.1, hs.2.le.trans t₀.property.2⟩ : J) ∈ {t : J | δ ≤ q t} :=
    not_lt.mp hn
  exact (not_le.mpr hs.2) (hmin hmem)

end Euler2D

end
