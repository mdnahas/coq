

(* val evaluable_of_global_reference : Libnames.global_reference -> Names.evaluable_global_reference *)
val tclUSER_if_not_mes : 
  Proof_type.tactic ->
  bool -> 
  Names.identifier list option -> 
  Proof_type.tactic
val recursive_definition :  
bool ->
           Names.identifier ->
           Constrintern.internalization_env ->
           Constrexpr.constr_expr ->
           Constrexpr.constr_expr ->
           int -> Constrexpr.constr_expr -> (Term.pconstant ->
            Term.constr option ref ->
            Term.pconstant ->
            Term.pconstant -> int -> Term.types -> int -> Term.constr -> 'a) -> Constrexpr.constr_expr list -> unit


