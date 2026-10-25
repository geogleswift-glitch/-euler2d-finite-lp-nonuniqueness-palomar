module

public import RequestProject.Euler.CircularFourierLinearFlow
public import RequestProject.Euler.BanachPerturbedExponential

/-! The actual uncoupled full amplitude evolution has an explicit
uniformly bounded formula, including its tangential forcing. -/

@[expose] public section

noncomputable section

open Complex Set NormedSpace
open scoped NNReal ContDiff

namespace Euler2D

def circularDiagonalNormalFrequency (N : ℕ) : Fin 2 → ℝ :=
  ![5 / 4 - (N + 2 : ℕ) / 2, -3 / 4]

def circularDiagonalTangentFrequency (N : ℕ) : Fin 2 → ℝ := ![-(N + 2 : ℕ) / 2, 0]

def circularDiagonalTangentForcing : Fin 2 → ℝ := ![-5 / 4, -3 / 4]

def circularDiagonalResponse : Fin 2 → ℂ := ![I, -I]

def circularUncoupledAmplitudeGeneratorComplex (N : ℕ) :
    CircularFourierAmplitudes →L[ℂ] CircularFourierAmplitudes :=
  (((Matrix.diagonal (fun i => I * (circularDiagonalNormalFrequency N i : ℂ))).mulVecLin.comp
      (LinearMap.fst ℂ CircularFourierVector CircularFourierVector)).prod
    (((Matrix.diagonal (fun i => (circularDiagonalTangentForcing i : ℂ))).mulVecLin.comp
      (LinearMap.fst ℂ CircularFourierVector CircularFourierVector)) +
      ((Matrix.diagonal (fun i => I * (circularDiagonalTangentFrequency N i : ℂ))).mulVecLin.comp
        (LinearMap.snd ℂ CircularFourierVector CircularFourierVector)))).toContinuousLinearMap

def circularUncoupledAmplitudeGenerator (N : ℕ) :
    CircularFourierAmplitudes →L[ℝ] CircularFourierAmplitudes :=
  (circularUncoupledAmplitudeGeneratorComplex N).restrictScalars ℝ

theorem circularUncoupledAmplitudeGenerator_apply (N : ℕ) (p : CircularFourierAmplitudes) :
    circularUncoupledAmplitudeGenerator N p =
      ((fun i => I * (circularDiagonalNormalFrequency N i : ℂ) * p.1 i),
        (fun i => (circularDiagonalTangentForcing i : ℂ) * p.1 i +
          I * (circularDiagonalTangentFrequency N i : ℂ) * p.2 i)) := by
  apply Prod.ext <;> funext i <;> fin_cases i <;>
    simp [circularUncoupledAmplitudeGenerator, circularUncoupledAmplitudeGeneratorComplex,
      Matrix.mulVecLin_apply, Matrix.mulVec_diagonal]

def circularUnitPhase (freq t : ℝ) : ℂ := Complex.exp ((t : ℂ) * (freq : ℂ) * I)

theorem norm_circularUnitPhase (freq t : ℝ) : ‖circularUnitPhase freq t‖ = 1 := by
  simpa only [circularUnitPhase, Complex.ofReal_mul] using Complex.norm_exp_ofReal_mul_I (t * freq)

theorem hasDerivAt_circularUnitPhase (freq t : ℝ) :
    HasDerivAt (circularUnitPhase freq) (I * (freq : ℂ) * circularUnitPhase freq t) t := by
  change HasDerivAt (fun s : ℝ => Complex.exp ((s : ℂ) * (freq : ℂ) * I))
    (I * (freq : ℂ) * Complex.exp ((t : ℂ) * (freq : ℂ) * I)) t
  convert ((((hasDerivAt_id t).ofReal_comp).mul_const (freq : ℂ)).mul_const I).cexp using 1 <;>
    simp only [circularUnitPhase, id_eq, Complex.ofReal_one, one_mul] <;> ring

def circularUncoupledAmplitudeCurve (N : ℕ) (p : CircularFourierAmplitudes) (t : ℝ) :
    CircularFourierAmplitudes :=
  ((fun i => circularUnitPhase (circularDiagonalNormalFrequency N i) t * p.1 i),
    (fun i => circularUnitPhase (circularDiagonalTangentFrequency N i) t * p.2 i +
      circularDiagonalResponse i *
        (circularUnitPhase (circularDiagonalNormalFrequency N i) t -
          circularUnitPhase (circularDiagonalTangentFrequency N i) t) * p.1 i))

set_option maxHeartbeats 600000 in
theorem circularUncoupledAmplitudeCurve_hasDerivAt (N : ℕ) (p : CircularFourierAmplitudes) (t : ℝ) :
    HasDerivAt (circularUncoupledAmplitudeCurve N p)
      (circularUncoupledAmplitudeGenerator N (circularUncoupledAmplitudeCurve N p t)) t := by
  have hη := hasDerivAt_pi.mpr (fun i : Fin 2 =>
    (hasDerivAt_circularUnitPhase (circularDiagonalNormalFrequency N i) t).mul_const (p.1 i))
  have hτ := hasDerivAt_pi.mpr (fun i : Fin 2 =>
    ((hasDerivAt_circularUnitPhase (circularDiagonalTangentFrequency N i) t).mul_const (p.2 i)).add
      ((((hasDerivAt_circularUnitPhase (circularDiagonalNormalFrequency N i) t).sub
        (hasDerivAt_circularUnitPhase (circularDiagonalTangentFrequency N i) t)).const_mul
          (circularDiagonalResponse i)).mul_const (p.1 i)))
  convert hη.prodMk hτ using 1
  · funext s
    apply Prod.ext <;> funext i <;>
      simp only [circularUncoupledAmplitudeCurve, Pi.add_apply, Pi.sub_apply]
  rw [circularUncoupledAmplitudeGenerator_apply]
  apply Prod.ext
  · funext i
    simp only [circularUncoupledAmplitudeCurve]
    ring
  · funext i
    fin_cases i <;>
      norm_num [circularUncoupledAmplitudeCurve, circularDiagonalNormalFrequency,
        circularDiagonalTangentFrequency, circularDiagonalTangentForcing, circularDiagonalResponse]
    <;> push_cast <;> ring_nf <;> simp only [Complex.I_sq] <;> ring

theorem circularUncoupledAmplitudeCurve_zero (N : ℕ) (p : CircularFourierAmplitudes) :
    circularUncoupledAmplitudeCurve N p 0 = p := by
  apply Prod.ext <;> funext i <;>
    simp [circularUncoupledAmplitudeCurve, circularUnitPhase, Complex.exp_zero]

theorem exp_circularUncoupledAmplitudeGenerator_apply (N : ℕ) (p : CircularFourierAmplitudes) (t : ℝ) :
    exp (t • circularUncoupledAmplitudeGenerator N) p = circularUncoupledAmplitudeCurve N p t := by
  have hd (s : ℝ) : HasDerivAt (fun s => exp (s • circularUncoupledAmplitudeGenerator N) p)
      (circularUncoupledAmplitudeGenerator N (exp (s • circularUncoupledAmplitudeGenerator N) p)) s := by
    have h := (hasDerivAt_exp_smul_const' (circularUncoupledAmplitudeGenerator N) s).clm_apply
      (hasDerivAt_const s p)
    simpa only [ContinuousLinearMap.mul_apply, map_zero, add_zero] using h
  have he := ODE_solution_unique_univ
    (v := fun _ z => circularUncoupledAmplitudeGenerator N z)
    (s := fun _ => (univ : Set CircularFourierAmplitudes))
    (fun _ => (circularUncoupledAmplitudeGenerator N).lipschitz.lipschitzOnWith)
    (fun s => ⟨hd s, mem_univ _⟩)
    (fun s => ⟨circularUncoupledAmplitudeCurve_hasDerivAt N p s, mem_univ _⟩)
    (t₀ := (0 : ℝ)) (by
      rw [circularUncoupledAmplitudeCurve_zero]
      have hzero : (0 : ℝ) • circularUncoupledAmplitudeGenerator N = 0 :=
        _root_.zero_smul ℝ (circularUncoupledAmplitudeGenerator N)
      rw [hzero, NormedSpace.exp_zero, ContinuousLinearMap.one_apply])
  exact congrFun he t

theorem norm_circularUncoupledAmplitudeCurve_le (N : ℕ) (p : CircularFourierAmplitudes) (t : ℝ) :
    ‖circularUncoupledAmplitudeCurve N p t‖ ≤ 3 * ‖p‖ := by
  have hp1 (i : Fin 2) : ‖p.1 i‖ ≤ ‖p‖ :=
    (norm_le_pi_norm p.1 i).trans (le_max_left _ _)
  have hp2 (i : Fin 2) : ‖p.2 i‖ ≤ ‖p‖ :=
    (norm_le_pi_norm p.2 i).trans (le_max_right _ _)
  have hd (i : Fin 2) : ‖circularDiagonalResponse i‖ = 1 := by
    fin_cases i <;> simp [circularDiagonalResponse]
  apply max_le
  · apply (pi_norm_le_iff_of_nonneg (by positivity : (0 : ℝ) ≤ 3 * ‖p‖)).mpr
    intro i
    change ‖circularUnitPhase _ t * p.1 i‖ ≤ _
    rw [norm_mul, norm_circularUnitPhase, one_mul]
    linarith [hp1 i, norm_nonneg p]
  · apply (pi_norm_le_iff_of_nonneg (by positivity : (0 : ℝ) ≤ 3 * ‖p‖)).mpr
    intro i
    change ‖circularUnitPhase _ t * p.2 i + circularDiagonalResponse i *
      (circularUnitPhase _ t - circularUnitPhase _ t) * p.1 i‖ ≤ _
    calc
      _ ≤ ‖circularUnitPhase _ t * p.2 i‖ + ‖circularDiagonalResponse i *
          (circularUnitPhase _ t - circularUnitPhase _ t) * p.1 i‖ := norm_add_le _ _
      _ ≤ ‖p.2 i‖ + 2 * ‖p.1 i‖ := by
        simp only [norm_mul, norm_circularUnitPhase, hd, one_mul]
        gcongr
        exact (norm_sub_le _ _).trans (by rw [norm_circularUnitPhase, norm_circularUnitPhase]; norm_num)
      _ ≤ _ := by linarith [hp1 i, hp2 i]

theorem norm_exp_circularUncoupledAmplitudeGenerator_le (N : ℕ) (t : ℝ) :
    ‖exp (t • circularUncoupledAmplitudeGenerator N)‖ ≤ 3 := by
  apply (exp (t • circularUncoupledAmplitudeGenerator N)).opNorm_le_bound (by norm_num)
  intro p
  rw [exp_circularUncoupledAmplitudeGenerator_apply]
  exact norm_circularUncoupledAmplitudeCurve_le N p t

theorem circularUnitPhase_eq_one_of_turns (freq t : ℝ) (k : ℤ)
    (h : t * freq = (k : ℝ) * (2 * Real.pi)) : circularUnitPhase freq t = 1 := by
  unfold circularUnitPhase
  have he : (t : ℂ) * (freq : ℂ) * I = (k : ℂ) * (2 * Real.pi * I) := by
    rw [← Complex.ofReal_mul, h]
    push_cast
    ring
  rw [he, Complex.exp_int_mul_two_pi_mul_I]

theorem circularUncoupledAmplitudeCurve_double_period (N : ℕ) (p : CircularFourierAmplitudes) :
    circularUncoupledAmplitudeCurve N p (2 * period) = p := by
  have hn (i : Fin 2) : circularUnitPhase (circularDiagonalNormalFrequency N i) (2 * period) = 1 := by
    fin_cases i
    · apply circularUnitPhase_eq_one_of_turns _ _ (1 - 2 * (N : ℤ))
      norm_num [circularDiagonalNormalFrequency, period]
      ring
    · apply circularUnitPhase_eq_one_of_turns _ _ (-3)
      norm_num [circularDiagonalNormalFrequency, period]
      ring
  have ht (i : Fin 2) : circularUnitPhase (circularDiagonalTangentFrequency N i) (2 * period) = 1 := by
    fin_cases i
    · apply circularUnitPhase_eq_one_of_turns _ _ (-2 * ((N + 2 : ℕ) : ℤ))
      norm_num [circularDiagonalTangentFrequency, period]
      ring
    · apply circularUnitPhase_eq_one_of_turns _ _ 0
      norm_num [circularDiagonalTangentFrequency, period]
  apply Prod.ext <;> funext i <;> simp only [circularUncoupledAmplitudeCurve, hn, ht,
    one_mul, sub_self, mul_zero, zero_mul, add_zero]

theorem exp_circularUncoupledAmplitudeGenerator_double_period (N : ℕ) :
    exp ((2 * period) • circularUncoupledAmplitudeGenerator N) =
      ContinuousLinearMap.id ℝ CircularFourierAmplitudes := by
  apply ContinuousLinearMap.ext
  intro p
  rw [exp_circularUncoupledAmplitudeGenerator_apply,
    circularUncoupledAmplitudeCurve_double_period, ContinuousLinearMap.id_apply]

end Euler2D

end
