
(* $Id$ *)

(*i*)
open Term
open Sign
open Proof_trees
(*i*)

(* The refiner (handles primitive rules and high-level tactics). *)

type 'a sigma = { 
  it : 'a ; 
  sigma : global_constraints }

val sig_it  : 'a sigma -> 'a
val sig_sig : 'a sigma -> global_constraints

val project_with_focus : goal sigma -> readable_constraints

val unpackage : 'a sigma -> global_constraints ref * 'a
val repackage : global_constraints ref -> 'a -> 'a sigma
val apply_sig_tac :
  global_constraints ref -> ('a sigma -> 'b sigma * 'c) -> 'a -> 'b * 'c

type validation = (proof_tree list -> proof_tree)

type tactic = goal sigma -> (goal list sigma * validation)

type transformation_tactic = proof_tree -> (goal list * validation)

val add_tactic             : string -> (tactic_arg list -> tactic) -> unit
val overwriting_add_tactic : string -> (tactic_arg list -> tactic) -> unit
val lookup_tactic          : string -> (tactic_arg list) -> tactic

val hide_tactic : 
  string -> (tactic_arg list -> tactic) -> (tactic_arg list -> tactic)

val overwrite_hidden_tactic : 
  string -> (tactic_arg list -> tactic) -> (tactic_arg list -> tactic)

val refiner : rule -> tactic
val context : ctxtty -> tactic
val vernac_tactic : tactic_expression -> tactic
val frontier : transformation_tactic
val list_pf : proof_tree -> goal list
val unTAC : tactic -> goal sigma -> proof_tree sigma

val extract_open_proof : 
  typed_type signature -> proof_tree -> constr * (int * constr) list


(*s Tacticals. *)

val tclIDTAC         : tactic
val tclORELSE        : tactic -> tactic -> tactic
val tclTHEN          : tactic -> tactic -> tactic
val tclTHEN_i        : tactic -> (int -> tactic) -> int -> tactic
val tclTHENL         : tactic -> tactic -> tactic
val tclTHENS         : tactic -> tactic list -> tactic
val tclTHENSI        : tactic -> tactic list -> tactic
val tclREPEAT        : tactic -> tactic
val tclFIRST         : tactic list -> tactic
val tclSOLVE         : tactic list -> tactic
val tclTRY           : tactic -> tactic
val tclTHENTRY       : tactic -> tactic -> tactic
val tclCOMPLETE      : tactic -> tactic
val tclAT_LEAST_ONCE : tactic -> tactic
val tclFAIL          : tactic
val tclDO            : int -> tactic -> tactic
val tclPROGRESS      : tactic -> tactic
val tclWEAK_PROGRESS : tactic -> tactic
val tclNOTSAMEGOAL   : tactic -> tactic


(*s Tactics handling a list of goals. *)

type validation_list = proof_tree list -> proof_tree list

type tactic_list = (goal list sigma) -> (goal list sigma) * validation_list

val tclFIRSTLIST       : tactic_list list -> tactic_list
val tclIDTAC_list      : tactic_list
val first_goal         : 'a list sigma -> 'a sigma
val apply_tac_list     : tactic -> tactic_list
val then_tactic_list   : tactic_list -> tactic_list -> tactic_list
val tactic_list_tactic : tactic_list -> tactic
val goal_goal_list     : 'a sigma -> 'a list sigma


(*s Functions for handling the state of the proof editor. *)

type pftreestate

val proof_of_pftreestate : pftreestate -> proof_tree
val cursor_of_pftreestate : pftreestate -> int list
val is_top_pftreestate : pftreestate -> bool
val evc_of_pftreestate : pftreestate -> global_constraints
val top_goal_of_pftreestate : pftreestate -> goal sigma
val nth_goal_of_pftreestate : int -> pftreestate -> goal sigma

val traverse : int -> pftreestate -> pftreestate
val solve_nth_pftreestate : int -> tactic -> pftreestate -> pftreestate
val solve_pftreestate : tactic -> pftreestate -> pftreestate
(* a weak version of logical undoing, that is really correct only *)
(* if there are no existential variables.                         *)
val weak_undo_pftreestate : pftreestate -> pftreestate

val mk_pftreestate : goal -> pftreestate
val extract_pftreestate : pftreestate -> constr
val first_unproven : pftreestate -> pftreestate
val last_unproven : pftreestate -> pftreestate
val nth_unproven : int -> pftreestate -> pftreestate
val node_prev_unproven : int -> pftreestate -> pftreestate
val node_next_unproven : int -> pftreestate -> pftreestate
val next_unproven : pftreestate -> pftreestate
val prev_unproven : pftreestate -> pftreestate
val top_of_tree : pftreestate -> pftreestate
val change_constraints_pftreestate 
  : global_constraints -> pftreestate -> pftreestate
