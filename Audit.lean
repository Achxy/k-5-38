/-
Authors: Achyuth Jayadevan <achyuth@jayadevan.in>
Released under CC0 1.0 Universal; see LICENSE.
-/
import Kourovka
import Lean.Util.CollectAxioms

open Lean in
run_cmd do
  let environment ← getEnv
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut count := 0
  for (name, _) in environment.constants.toList do
    if (`Kourovka).isPrefixOf name || name.toString.startsWith "_private.Kourovka." then
      for axiomName in ← collectAxioms name do
        unless allowed.contains axiomName do
          throwError "Unexpected axiom {axiomName} in {name}"
      count := count + 1
  unless count > 0 do
    throwError "No project declarations were imported"
  logInfo m!"Axiom audit passed for {count} project declarations."

#print axioms Kourovka.FinitePaths.middle_eq_terminal_of_bounded_prefixes
#print axioms Kourovka.CentralProducts.quotientEquiv
#print axioms Kourovka.retract_eq_bot_of_le_commutator
#print axioms Kourovka.injective_of_central_offDiagonal

#print axioms Kourovka.exists_central_offDiagonal_iterate

#print axioms Kourovka.CentralLattice.exists_group_correction_modulus
#print axioms Kourovka.directProduct_isHopfian
#print axioms Kourovka.problem_5_38
