import CubeSections.Classical.BallTwo

/-! Reduction of the full scalar sinc bound to strictness for real `p > 2`.
Integrability, positivity and the exact `p = 2` value supply the endpoint.
The strict-interior statement is proved in `Classical.BallProved`.
-/
noncomputable section
namespace CubeSections

def BallSincStrictInteriorStatement : Prop :=
  ∀ p : ℝ, 2 < p → ballSincIntegral p < Real.sqrt (2/p)

theorem strictBallSincBound_of_interior (h : BallSincStrictInteriorStatement) :
    StrictBallSincBound := by
  intro p hp
  by_cases htwo : p=2
  · subst p
    refine ⟨integrable_ballSincIntegrand 2 (by norm_num), ?_, ?_⟩ <;>
      norm_num [ballSincIntegral_two]
  · have hs := h p (lt_of_le_of_ne hp (Ne.symm htwo))
    refine ⟨integrable_ballSincIntegrand p hp, hs.le, ?_⟩
    constructor
    · intro heq
      exact ((ne_of_lt hs) heq).elim
    · intro heq
      exact (htwo heq).elim

theorem classical_codimension_bound_of_interior_and_sincBL
    (hBall : BallSincStrictInteriorStatement) (hBL : SincBrascampLiebStatement)
    (n k : ℕ) (hk : 1 ≤ k) (hkn : k ≤ n) (hn : n ≤ 2*k) (U : Frame n k) :
    sectionVolume U ≤ sharpValue n k :=
  classical_codimension_bound_of_sinc_inputs (strictBallSincBound_of_interior hBall)
    hBL n k hk hkn hn U

#print axioms strictBallSincBound_of_interior
#print axioms classical_codimension_bound_of_interior_and_sincBL
end CubeSections
