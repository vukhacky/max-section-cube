import CubeSections.Semantics
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.LinearAlgebra.Pi
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-! An actual volume-preserving coordinate splitting E_(n+1) ≃ E_n × R.
The product has its ordinary product topology and product measure; no claim
identifies its max norm with the Euclidean norm. The norm-square formula is
proved separately and used for Gaussian domination. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace CubeSections

def euclideanSuccJoin (n : ℕ) : (E n × ℝ) ≃ₗ[ℝ] E (n+1) :=
  (((WithLp.linearEquiv 2 ℝ (Fin n → ℝ)).prodCongr (LinearEquiv.refl ℝ ℝ)).trans
    (LinearEquiv.prodComm ℝ (Fin n → ℝ) ℝ)).trans
    ((Fin.consLinearEquiv ℝ (fun _ : Fin (n+1) => ℝ)).trans
      (WithLp.linearEquiv 2 ℝ (Fin (n+1) → ℝ)).symm)

@[simp] theorem euclideanSuccJoin_zero (n : ℕ) (x : E n) (s : ℝ) :
    euclideanSuccJoin n (x,s) 0 = s := rfl

@[simp] theorem euclideanSuccJoin_succ (n : ℕ) (x : E n) (s : ℝ) (i : Fin n) :
    euclideanSuccJoin n (x,s) i.succ = x i := rfl

theorem continuous_euclideanSuccJoin (n : ℕ) : Continuous (euclideanSuccJoin n) :=
  (euclideanSuccJoin n).toContinuousLinearEquiv.continuous

theorem euclideanSuccJoin_norm_sq (n : ℕ) (x : E n) (s : ℝ) :
    ‖euclideanSuccJoin n (x,s)‖^2 = ‖x‖^2+s^2 := by
  simp only [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_succ,
    euclideanSuccJoin_zero, euclideanSuccJoin_succ]
  ring

theorem euclideanSuccJoin_measurePreserving (n : ℕ) :
    MeasurePreserving (euclideanSuccJoin n) ((volume : Measure (E n)).prod volume) volume := by
  have h0 := (PiLp.volume_preserving_toLp (Fin (n+1))).comp
    (((volume_preserving_piFinSuccAbove (fun _ : Fin (n+1) => ℝ) 0).symm).comp
      (Measure.measurePreserving_swap.comp
        ((PiLp.volume_preserving_ofLp (Fin n)).prod (MeasurePreserving.id (volume : Measure ℝ)))))
  convert h0 using 1
  funext p
  ext i
  simp only [Function.comp_apply, Prod.map_apply, Prod.swap_prod_mk,
    MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv, Fin.insertNth_zero]
  rfl

theorem euclideanSuccJoin_integrable {n : ℕ} (f : E (n+1) → ℝ) (hf : Integrable f) :
    Integrable (fun p : E n × ℝ => f (euclideanSuccJoin n p))
      ((volume : Measure (E n)).prod volume) :=
  ((euclideanSuccJoin_measurePreserving n).integrable_comp_emb
    (euclideanSuccJoin n).toContinuousLinearEquiv.toHomeomorph.measurableEmbedding).2 hf

theorem integral_euclideanSuccJoin {n : ℕ} (f : E (n+1) → ℝ) (hf : Integrable f) :
    (∫ x : E n, ∫ s : ℝ, f (euclideanSuccJoin n (x,s))) = ∫ z : E (n+1), f z := by
  have hg := euclideanSuccJoin_integrable f hf
  rw [← integral_prod _ hg]
  exact (euclideanSuccJoin_measurePreserving n).integral_comp
    (euclideanSuccJoin n).toContinuousLinearEquiv.toHomeomorph.measurableEmbedding f

#print axioms euclideanSuccJoin_measurePreserving
#print axioms integral_euclideanSuccJoin
end CubeSections
