import CubeSections.Certificates.Data.Q2M1L1
import CubeSections.Certificates.Data.Q2M1L2
import CubeSections.Certificates.Data.Q2M2L2
import CubeSections.Certificates.Data.Q3M1L1
import CubeSections.Certificates.Data.Q3M1L2
import CubeSections.Certificates.Data.Q3M1L3
import CubeSections.Certificates.Data.Q3M2L2
import CubeSections.Certificates.Data.Q3M2L3
import CubeSections.Certificates.Data.Q3M3L3
import CubeSections.Certificates.Data.Q4M1L1
import CubeSections.Certificates.Data.Q4M1L2
import CubeSections.Certificates.Data.Q4M1L3
import CubeSections.Certificates.Data.Q4M1L4
import CubeSections.Certificates.Data.Q4M2L2
import CubeSections.Certificates.Data.Q4M2L3
import CubeSections.Certificates.Data.Q4M2L4
import CubeSections.Certificates.Data.Q4M3L3
import CubeSections.Certificates.Data.Q4M3L4
import CubeSections.Certificates.Data.Q4M4L4
import Mathlib.Tactic.IntervalCases

namespace CubeSections.Certificates

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

/-- Exact complete tree selected by the three integer multiplicities. -/
def certificate (p : Parameters) : Tree :=
  match p.q, p.m, p.l with
  | 2, 1, 1 => Data.Q2M1L1.tree
  | 2, 1, 2 => Data.Q2M1L2.tree
  | 2, 2, 2 => Data.Q2M2L2.tree
  | 3, 1, 1 => Data.Q3M1L1.tree
  | 3, 1, 2 => Data.Q3M1L2.tree
  | 3, 1, 3 => Data.Q3M1L3.tree
  | 3, 2, 2 => Data.Q3M2L2.tree
  | 3, 2, 3 => Data.Q3M2L3.tree
  | 3, 3, 3 => Data.Q3M3L3.tree
  | 4, 1, 1 => Data.Q4M1L1.tree
  | 4, 1, 2 => Data.Q4M1L2.tree
  | 4, 1, 3 => Data.Q4M1L3.tree
  | 4, 1, 4 => Data.Q4M1L4.tree
  | 4, 2, 2 => Data.Q4M2L2.tree
  | 4, 2, 3 => Data.Q4M2L3.tree
  | 4, 2, 4 => Data.Q4M2L4.tree
  | 4, 3, 3 => Data.Q4M3L3.tree
  | 4, 3, 4 => Data.Q4M3L4.tree
  | 4, 4, 4 => Data.Q4M4L4.tree
  | _, _, _ => .leaf .projection

/-- Every valid multiplicity triple has a kernel-accepted complete tree. -/
theorem allPairs_accepts (p : Parameters) (hp : p.Valid) :
    (certificate p).Accepts p (rootRectangle p.q) := by
  rcases p with ⟨q, m, l⟩
  rcases hp with ⟨hq, hm, hml, hl⟩
  have hmupper : m ≤ q := hml.trans hl
  have hllower : 1 ≤ l := hm.trans hml
  rcases hq with rfl | rfl | rfl
  all_goals interval_cases m <;> interval_cases l
  all_goals first
    | omega
    | exact Data.Q2M1L1.accepted
    | exact Data.Q2M1L2.accepted
    | exact Data.Q2M2L2.accepted
    | exact Data.Q3M1L1.accepted
    | exact Data.Q3M1L2.accepted
    | exact Data.Q3M1L3.accepted
    | exact Data.Q3M2L2.accepted
    | exact Data.Q3M2L3.accepted
    | exact Data.Q3M3L3.accepted
    | exact Data.Q4M1L1.accepted
    | exact Data.Q4M1L2.accepted
    | exact Data.Q4M1L3.accepted
    | exact Data.Q4M1L4.accepted
    | exact Data.Q4M2L2.accepted
    | exact Data.Q4M2L3.accepted
    | exact Data.Q4M2L4.accepted
    | exact Data.Q4M3L3.accepted
    | exact Data.Q4M3L4.accepted
    | exact Data.Q4M4L4.accepted

theorem allPairs_checked (p : Parameters) (hp : p.Valid) :
    (certificate p).check p (rootRectangle p.q) = true :=
  ((certificate p).check_eq_true_iff p (rootRectangle p.q)).mpr (allPairs_accepts p hp)

theorem allPairs_cover (p : Parameters) (hp : p.Valid) (c d : ℝ)
    (hcd : (rootRectangle p.q).Contains c d) :
    ∃ (r : Rectangle) (a : Leaf),
      (certificate p).HasLeaf (rootRectangle p.q) r a ∧ r.Contains c d ∧ a.Accepts p r :=
  (certificate p).accepts_covers p (rootRectangle p.q) (allPairs_accepts p hp) c d hcd

#print axioms allPairs_accepts
#print axioms allPairs_cover

end CubeSections.Certificates
