/-
Authors: Achyuth Jayadevan <achyuth@jayadevan.in>
Released under CC0 1.0 Universal; see LICENSE.
-/
import Kourovka.CentralHopfian
import Kourovka.QuotientProducts
import Kourovka.Problem

namespace Kourovka

/-- Kourovka Problem 5.38: the exact universal statement, with all factor hypotheses explicit. -/
theorem problem_5_38 (A B : Type*) [Group A] [Group B] : ProductHopficityStatement A B := by
  intro hfgA hfgB hsolA hsolB hhopA hhopB
  letI : Group.FG A := hfgA
  letI : Group.FG B := hfgB
  letI : IsSolvable A := hsolA
  letI : IsSolvable B := hsolB
  exact directProduct_isHopfian hhopA hhopB

end Kourovka
