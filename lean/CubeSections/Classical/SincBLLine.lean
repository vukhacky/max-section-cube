import CubeSections.Classical.FiniteHolder
import CubeSections.Classical.BallTwo

/-! The complete rank-one instance of specialized sinc Brascamp--Lieb.
It follows from finite weighted Hölder and unconditional scalar integrability.
Neither Ball's sharp scalar bound nor functional BL is assumed.
-/
noncomputable section
open MeasureTheory
open scoped BigOperators

namespace CubeSections

theorem lineFrame_sinc_eq_sqrt_leverage (W : Frame n 1) (x : E 1) (i : Fin n) :
    Real.sinc (Real.pi*(W x) i) =
      Real.sinc (Real.pi*Real.sqrt (leverage W i)*x 0) := by
  have hs : frameMatrix W i 0 ^ 2 = Real.sqrt (leverage W i)^2 := by
    rw [Real.sq_sqrt (leverage_nonneg W i)]
    simpa only [Fin.sum_univ_one] using (leverage_eq_sum_sq W i).symm
  have h := sinc_mul_eq_of_sq_eq (frameMatrix W i 0) (Real.sqrt (leverage W i))
    (Real.pi*x 0) hs
  rw [lineFrame_coordinate]
  convert h using 1 <;> congr 1 <;> ring

/-- Zero weights use an integrable auxiliary zero function. Its zero power
still contributes 1, exactly as the corresponding zero row's sinc factor. -/
def lineSincPower (W : Frame n 1) (i : Fin n) (t : ℝ) : ℝ :=
  if leverage W i=0 then 0
  else ballSincIntegrand (1/leverage W i) (Real.sqrt (leverage W i)*t)

theorem lineSincPower_nonneg (W : Frame n 1) (i : Fin n) (t : ℝ) :
    0 ≤ lineSincPower W i t := by
  unfold lineSincPower
  split_ifs
  · exact le_rfl
  · exact ballSincIntegrand_nonneg _ _

theorem continuous_lineSincPower (W : Frame n 1) (i : Fin n) :
    Continuous (lineSincPower W i) := by
  change Continuous (fun t : ℝ => lineSincPower W i t)
  by_cases hi : leverage W i=0
  · simp only [lineSincPower, hi, ite_true]
    exact continuous_const
  · simp only [lineSincPower, hi, ite_false]
    exact (continuous_ballSincIntegrand _
      (div_nonneg zero_le_one (leverage_nonneg W i))).comp
      (continuous_const.mul continuous_id)

theorem integrable_lineSincPower (W : Frame n 1)
    (hW : ∀ i, leverage W i ≤ 1/2) (i : Fin n) : Integrable (lineSincPower W i) := by
  change Integrable (fun t : ℝ => lineSincPower W i t)
  by_cases hi : leverage W i=0
  · simp only [lineSincPower, hi, ite_true]
    exact integrable_zero ℝ ℝ volume
  · have hpos : 0 < leverage W i := lt_of_le_of_ne (leverage_nonneg W i) (Ne.symm hi)
    simp only [lineSincPower, hi, ite_false]
    exact (integrable_ballSincIntegrand _
      (reciprocal_ge_two_of_le_half _ hpos (hW i))).comp_mul_left'
        (ne_of_gt (Real.sqrt_pos.2 hpos))

theorem lineSincPower_rpow (W : Frame n 1) (i : Fin n) (t : ℝ) :
    (lineSincPower W i t) ^ leverage W i =
      |Real.sinc (Real.pi*Real.sqrt (leverage W i)*t)| := by
  by_cases hi : leverage W i=0
  · simp [lineSincPower, hi]
  · simp only [lineSincPower, hi, ite_false, ballSincIntegrand, mul_assoc]
    rw [← Real.rpow_mul (abs_nonneg _), one_div_mul_cancel hi, Real.rpow_one]

theorem lineSincPower_integral_factor (W : Frame n 1) (i : Fin n) :
    (∫ t : ℝ, lineSincPower W i t) ^ leverage W i =
      scaledSincIntegral (leverage W i) ^ leverage W i := by
  by_cases hi : leverage W i=0
  · simp [hi]
  · simp only [lineSincPower, hi, ite_false, scaledSincIntegral,
      ballSincIntegrand, mul_assoc]

theorem sincBrascampLieb_line (n : ℕ) (W : Frame n 1)
    (hW : ∀ i, leverage W i ≤ 1/2) :
    Integrable (cubeAbsSincKernel W) ∧
      (∫ x : E 1, cubeAbsSincKernel W x) ≤ sincProduct (leverage W) := by
  let g : ℝ → ℝ := fun t => ∏ i, (lineSincPower W i t) ^ leverage W i
  have hprod (x : E 1) : g (lineCoordinateIsometry x) = cubeAbsSincKernel W x := by
    simp only [g, cubeAbsSincKernel]
    apply Finset.prod_congr rfl
    intro i _
    rw [lineSincPower_rpow, lineFrame_sinc_eq_sqrt_leverage]
    rfl
  obtain ⟨hgint, hgle⟩ := finiteHolder_nonnegative volume (lineSincPower W) (leverage W)
    (fun i => (continuous_lineSincPower W i).measurable) (lineSincPower_nonneg W)
    (integrable_lineSincPower W hW) (leverage_nonneg W)
    (by simpa using sum_leverage W)
  have hcompose := lineCoordinateIsometry.measurePreserving.integrable_comp_emb
    lineCoordinateIsometry.toHomeomorph.measurableEmbedding (g := g)
  have hkernel : Integrable (cubeAbsSincKernel W) :=
    (hcompose.2 hgint).congr (ae_of_all _ hprod)
  have hlintegral := lineCoordinateIsometry.measurePreserving.integral_comp
    lineCoordinateIsometry.toHomeomorph.measurableEmbedding g
  refine ⟨hkernel, ?_⟩
  calc
    (∫ x : E 1, cubeAbsSincKernel W x) = ∫ t : ℝ, g t := by
      rw [← hlintegral]
      exact integral_congr_ae (ae_of_all _ (fun x => (hprod x).symm))
    _ ≤ ∏ i, (∫ t : ℝ, lineSincPower W i t) ^ leverage W i := hgle
    _ = sincProduct (leverage W) := by
      simp only [lineSincPower_integral_factor, sincProduct]

#print axioms sincBrascampLieb_line
end CubeSections
