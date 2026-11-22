import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.NormNum

/-!
# Exact rational certificate checker for the small-quotient comparison

The formulas are from Appendix A of the locked geometric manuscript.
Acceptance certifies rational arithmetic and a complete rectangle tree. The
real-variable interpretation is established separately, not assumed here.
-/
namespace CubeSections.Certificates

structure Parameters where
  q : ℕ
  m : ℕ
  l : ℕ
  deriving DecidableEq, Repr

structure Rectangle where
  lowerC : ℚ
  upperC : ℚ
  lowerD : ℚ
  upperD : ℚ
  deriving DecidableEq, Repr

inductive Leaf where
  | projection
  | strip (threshold : ℚ)
  deriving DecidableEq, Repr

inductive Tree where
  | leaf (data : Leaf)
  | splitC (midpoint : ℚ) (left right : Tree)
  | splitD (midpoint : ℚ) (left right : Tree)
  deriving Repr

def Parameters.Valid (p : Parameters) : Prop :=
  (p.q = 2 ∨ p.q = 3 ∨ p.q = 4) ∧
  1 ≤ p.m ∧ p.m ≤ p.l ∧ p.l ≤ p.q

instance (p : Parameters) : Decidable p.Valid := inferInstanceAs (Decidable
  ((p.q = 2 ∨ p.q = 3 ∨ p.q = 4) ∧ 1 ≤ p.m ∧ p.m ≤ p.l ∧ p.l ≤ p.q))

def rootRectangle (q : ℕ) : Rectangle :=
  ⟨1 / (q + 1 : ℚ), 1 / (q : ℚ), 1 / (q + 1 : ℚ), 1 / (q : ℚ)⟩

def Rectangle.InWindow (r : Rectangle) (q : ℕ) : Prop :=
  1 / (q + 1 : ℚ) ≤ r.lowerC ∧ r.lowerC < r.upperC ∧
  r.upperC ≤ 1 / (q : ℚ) ∧
  1 / (q + 1 : ℚ) ≤ r.lowerD ∧ r.lowerD < r.upperD ∧
  r.upperD ≤ 1 / (q : ℚ)

instance (r : Rectangle) (q : ℕ) : Decidable (r.InWindow q) :=
  inferInstanceAs (Decidable
    (1 / (q + 1 : ℚ) ≤ r.lowerC ∧ r.lowerC < r.upperC ∧
     r.upperC ≤ 1 / (q : ℚ) ∧ 1 / (q + 1 : ℚ) ≤ r.lowerD ∧
     r.lowerD < r.upperD ∧ r.upperD ≤ 1 / (q : ℚ)))

def Rectangle.leftC (r : Rectangle) (z : ℚ) : Rectangle := { r with upperC := z }
def Rectangle.rightC (r : Rectangle) (z : ℚ) : Rectangle := { r with lowerC := z }
def Rectangle.leftD (r : Rectangle) (z : ℚ) : Rectangle := { r with upperD := z }
def Rectangle.rightD (r : Rectangle) (z : ℚ) : Rectangle := { r with lowerD := z }

/-- The rational curvature envelope, with q kept as a natural-number parameter. -/
def curvatureEnvelope (q : ℕ) (z : ℚ) : ℚ :=
  let a : ℚ := 1 / (q + 1 : ℚ)
  a / 2 * (1 + (a + z) / 3 + (a ^ 2 + a * z + z ^ 2) / (6 * (1 - a)))

/-- The continuous extension at m=q is encoded by the exact ratio one. -/
def chargeUpper (q j : ℕ) (x X : ℚ) : ℚ :=
  1 / 2 * curvatureEnvelope q (1 - (q : ℚ) * x) *
    (if j = q then 1 else (1 - (q : ℚ) * x) / (1 - (j : ℚ) * x)) *
    ((q + 1 : ℚ) - 1 / X)

def surplus : ℚ := 1 / 4000

def chargeSum (p : Parameters) (r : Rectangle) : ℚ :=
  chargeUpper p.q p.m r.lowerC r.upperC +
  chargeUpper p.q p.l r.lowerD r.upperD + surplus

def angularDenominator (p : Parameters) (r : Rectangle) : ℚ :=
  2 / 9 + (1 / 4 : ℚ) * (2 - (p.m : ℚ) * r.lowerC - (p.l : ℚ) * r.lowerD)

def AngleTest (S K v : ℚ) : Prop :=
  3 * v ^ 2 > 5 * (S * K * (15 + v)) ^ 2

instance (S K v : ℚ) : Decidable (AngleTest S K v) :=
  inferInstanceAs (Decidable (3 * v ^ 2 > 5 * (S * K * (15 + v)) ^ 2))

def projectionLower (p : Parameters) (r : Rectangle) : ℚ :=
  max 0 (1 - ((1 - (p.m : ℚ) * r.lowerC) * (1 - (p.l : ℚ) * r.lowerD)) /
    ((p.m : ℚ) * p.l * r.lowerC * r.lowerD))

/-- Rational half-angle parametrization of sine. -/
def sine (t : ℚ) : ℚ := 2 * t / (1 + t ^ 2)

/-- Rational half-angle parametrization of cosine. -/
def cosine (t : ℚ) : ℚ := (1 - t ^ 2) / (1 + t ^ 2)

/-- Exact upper bound for the possibly half-integer power in R. -/
def radiusUpper (p : Parameters) : ℚ :=
  let b : ℚ := 1 / (p.q : ℚ)
  let d := 2 * p.q - p.m - p.l
  b * (1 + b) ^ (d / 2) * (1 + b / 2) ^ (d % 2)

def gramLower (r : Rectangle) : ℚ := min r.lowerC r.lowerD

def determinantLower (r : Rectangle) (T : ℚ) : ℚ :=
  (r.lowerC + r.lowerD) / 2 + gramLower r * cosine T -
    r.upperC * r.upperD * sine T ^ 2

def eta (p : Parameters) (r : Rectangle) (T : ℚ) : ℚ :=
  determinantLower r T * gramLower r / (2 * radiusUpper p)

def StripTest (p : Parameters) (r : Rectangle) (T : ℚ) : Prop :=
  determinantLower r T ^ 2 >
    2 * radiusUpper p * T * (1 + r.upperC * r.upperD * sine T ^ 2 / 4) *
      (1 - eta p r T * sine T) ^ 2

instance (p : Parameters) (r : Rectangle) (T : ℚ) : Decidable (StripTest p r T) :=
  inferInstanceAs (Decidable (determinantLower r T ^ 2 >
    2 * radiusUpper p * T * (1 + r.upperC * r.upperD * sine T ^ 2 / 4) *
      (1 - eta p r T * sine T) ^ 2))

def Leaf.Accepts (p : Parameters) (r : Rectangle) (a : Leaf) : Prop :=
  p.Valid ∧ r.InWindow p.q ∧ 0 < chargeSum p r ∧ 0 < angularDenominator p r ∧
  match a with
  | .projection => AngleTest (chargeSum p r) (angularDenominator p r) (projectionLower p r)
  | .strip T => 0 ≤ T ∧ T ≤ 1 ∧
      (T = 1 ∨ AngleTest (chargeSum p r) (angularDenominator p r) (sine T ^ 2)) ∧
      0 < radiusUpper p ∧ 0 < determinantLower r T ∧
      0 ≤ eta p r T ∧ eta p r T ≤ 1 / 2 ∧ StripTest p r T

instance (p : Parameters) (r : Rectangle) (a : Leaf) : Decidable (a.Accepts p r) := by
  unfold Leaf.Accepts
  cases a <;> infer_instance

def SplitCValid (r : Rectangle) (z : ℚ) : Prop :=
  z = (r.lowerC + r.upperC) / 2 ∧ r.lowerC < z ∧ z < r.upperC ∧
    r.upperD - r.lowerD ≤ r.upperC - r.lowerC

def SplitDValid (r : Rectangle) (z : ℚ) : Prop :=
  z = (r.lowerD + r.upperD) / 2 ∧ r.lowerD < z ∧ z < r.upperD ∧
    r.upperC - r.lowerC < r.upperD - r.lowerD

instance (r : Rectangle) (z : ℚ) : Decidable (SplitCValid r z) :=
  inferInstanceAs (Decidable (z = (r.lowerC + r.upperC) / 2 ∧ r.lowerC < z ∧
    z < r.upperC ∧ r.upperD - r.lowerD ≤ r.upperC - r.lowerC))
instance (r : Rectangle) (z : ℚ) : Decidable (SplitDValid r z) :=
  inferInstanceAs (Decidable (z = (r.lowerD + r.upperD) / 2 ∧ r.lowerD < z ∧
    z < r.upperD ∧ r.upperC - r.lowerC < r.upperD - r.lowerD))

/-- A pure terminating checker. No external success flag enters this definition. -/
def Tree.check (p : Parameters) (r : Rectangle) : Tree → Bool
  | .leaf a => decide (a.Accepts p r)
  | .splitC z left right => decide (SplitCValid r z) &&
      left.check p (r.leftC z) && right.check p (r.rightC z)
  | .splitD z left right => decide (SplitDValid r z) &&
      left.check p (r.leftD z) && right.check p (r.rightD z)

/-- Propositional form of the checker, useful for short kernel proof terms. -/
def Tree.Accepts (p : Parameters) (r : Rectangle) : Tree → Prop
  | .leaf a => a.Accepts p r
  | .splitC z left right => SplitCValid r z ∧
      left.Accepts p (r.leftC z) ∧ right.Accepts p (r.rightC z)
  | .splitD z left right => SplitDValid r z ∧
      left.Accepts p (r.leftD z) ∧ right.Accepts p (r.rightD z)

theorem Tree.check_eq_true_iff (p : Parameters) (r : Rectangle) (t : Tree) :
    t.check p r = true ↔ t.Accepts p r := by
  induction t generalizing r with
  | leaf a => simp [Tree.check, Tree.Accepts]
  | splitC z left right ihl ihr =>
      simp only [Tree.check, Bool.and_eq_true, decide_eq_true_eq, ihl, ihr, Tree.Accepts]
      exact and_assoc
  | splitD z left right ihl ihr =>
      simp only [Tree.check, Bool.and_eq_true, decide_eq_true_eq, ihl, ihr, Tree.Accepts]
      exact and_assoc

end CubeSections.Certificates
