/-
Authors: Achyuth Jayadevan <achyuth@jayadevan.in>
Released under CC0 1.0 Universal; see LICENSE.
-/
import Kourovka.Hopfian

namespace Kourovka

/-- The statement of Kourovka Problem 5.38, with all six factor hypotheses explicit. -/
def ProductHopficityStatement (A B : Type*) [Group A] [Group B] : Prop :=
  Group.FG A → Group.FG B → IsSolvable A → IsSolvable B →
    IsHopfian A → IsHopfian B → IsHopfian (A × B)

end Kourovka
