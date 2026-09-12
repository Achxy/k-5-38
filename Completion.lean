/-
Authors: Achyuth Jayadevan <achyuth@jayadevan.in>
Released under CC0 1.0 Universal; see LICENSE.
-/
import Kourovka.Paper

example (A B : Type*) [Group A] [Group B]
    (hfgA : Group.FG A) (hfgB : Group.FG B)
    (hsolA : IsSolvable A) (hsolB : IsSolvable B)
    (hhopA : Kourovka.IsHopfian A) (hhopB : Kourovka.IsHopfian B)
    (f : A × B →* A × B) (hf : Function.Surjective f) : Function.Injective f :=
  Kourovka.problem_5_38 A B hfgA hfgB hsolA hsolB hhopA hhopB f hf

#check @Kourovka.problem_5_38
