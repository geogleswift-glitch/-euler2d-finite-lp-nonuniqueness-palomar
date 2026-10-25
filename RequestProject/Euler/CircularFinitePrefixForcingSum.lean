module

public import RequestProject.Euler.CircularFinitePrefixPlanarRows

/-! Exact agreement of the finite row indexing with the physical
off-self decomposition. No velocity estimate enters this identity. -/

@[expose] public section

set_option maxHeartbeats 6000000
set_option maxRecDepth 4000

noncomputable section

open Complex Set MeasureTheory Metric
open scoped NNReal ENNReal

namespace Euler2D

theorem sum_finite_rows_omit_self {j k : ℕ} (hjk : j ≤ k) (A B : ℕ → ℂ) :
    (∑ l : Fin (k + 1), if (l : ℕ) < j then A l else if j < (l : ℕ) then B l else 0) =
      (∑ l : Fin j, A l) + ∑ l ∈ Finset.Ico (j + 1) (k + 1), B l := by
  classical
  change (∑ l : Fin (k + 1), (fun n : ℕ => if n < j then A n else if j < n then B n else 0) l) = _
  rw [Fin.sum_univ_eq_sum_range (fun n : ℕ => if n < j then A n else if j < n then B n else 0)]
  rw [Fin.sum_univ_eq_sum_range A]
  have hlow : (∑ l ∈ Finset.range (k + 1), if l < j then A l else 0) =
      ∑ l ∈ Finset.range j, A l := by
    calc
      _ = ∑ l ∈ Finset.range j, if l < j then A l else 0 := by
        symm
        apply Finset.sum_subset (Finset.range_mono (by omega : j ≤ k + 1))
        intro l hl hn
        have hn' : ¬l < j := by simpa only [Finset.mem_range] using hn
        simp [hn']
      _ = _ := Finset.sum_congr rfl (fun l hl => by simp [Finset.mem_range.mp hl])
  have hupp : (∑ l ∈ Finset.range (k + 1), if j < l then B l else 0) =
      ∑ l ∈ Finset.Ico (j + 1) (k + 1), B l := by
    calc
      _ = ∑ l ∈ Finset.Ico (j + 1) (k + 1), if j < l then B l else 0 := by
        symm
        apply Finset.sum_subset
          (fun l hl => Finset.mem_range.mpr (Finset.mem_Ico.mp hl).2)
        intro l hl hn
        have hn' : ¬j < l := by
          have hl' := Finset.mem_range.mp hl
          simp only [Finset.mem_Ico, not_and] at hn
          omega
        simp [hn']
      _ = _ := Finset.sum_congr rfl (fun l hl => by
        have h := (Finset.mem_Ico.mp hl).1
        simp [show j < l by omega])
  calc
    _ = (∑ l ∈ Finset.range (k + 1), if l < j then A l else 0) +
        ∑ l ∈ Finset.range (k + 1), if j < l then B l else 0 := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro l hl
      by_cases hlj : l < j
      · simp [hlj, show ¬j < l by omega]
      · simp [hlj]
    _ = _ := by rw [hlow, hupp]

namespace CircularMaterialTransferProfile

variable {γ : ℝ≥0} {hγ : 0 < γ} {hγ1 : (γ : ℝ) < 1}
    (P : CircularMaterialTransferProfile hγ hγ1)

theorem finitePrefixPlanarRowField_eq_split
    {s A₀ b R ρ : ℝ} (N k j : ℕ) (hkN : k ≤ N) (hjk : j ≤ k)
    {f : Lp ℝ 2 μT} {T : ℝ} (S : BoundedEulerParticleSystem f T) (t : ℝ) (x : ℂ) :
    P.finitePrefixPlanarRowField s A₀ b R ρ N k j hkN S t x =
      (∑ l : Fin j, velocityC (P.finiteOuterLabelComplexPerturbation s A₀ b R ρ N
        (⟨l, l.isLt.trans_le (Nat.le_succ_of_le (hjk.trans hkN))⟩ : Fin (N + 1)) S t) x) +
      ∑ l ∈ Finset.Ico (j + 1) (k + 1), velocityC (boxedComplexDensity
        (S.transportedScalar (P.finitePeriodicLabel s A₀ b R ρ N l) t)) x := by
  classical
  let A : ℕ → ℂ := fun l => if hl : l < N + 1 then
    velocityC (P.finiteOuterLabelComplexPerturbation s A₀ b R ρ N ⟨l, hl⟩ S t) x else 0
  let B : ℕ → ℂ := fun l => velocityC (boxedComplexDensity
    (S.transportedScalar (P.finitePeriodicLabel s A₀ b R ρ N l) t)) x
  have hsum := sum_finite_rows_omit_self hjk A B
  have hleft : P.finitePrefixPlanarRowField s A₀ b R ρ N k j hkN S t x =
      ∑ l : Fin (k + 1), if (l : ℕ) < j then A l else if j < (l : ℕ) then B l else 0 := by
    apply Finset.sum_congr rfl
    intro l hl
    have hlN : (l : ℕ) < N + 1 := l.isLt.trans_le (Nat.succ_le_succ hkN)
    simp only [A, B, hlN, dif_pos]
    rfl
  rw [hleft, hsum]
  congr 1
  apply Finset.sum_congr rfl
  intro l hl
  have hlN : (l : ℕ) < N + 1 := l.isLt.trans_le (Nat.le_succ_of_le (hjk.trans hkN))
  simp only [A, hlN, dif_pos]

end CircularMaterialTransferProfile
end Euler2D

end
