(****************************************************************)
(*                   DEDUCTION NATURELLE                        *)
(****************************************************************)

(****************************************************************)
(*    [A]     * implique_intro h :                              *)
(*    ...     * Si le but est de la forme A => B rajoute A aux  *)
(*     B      * hypotèses sous le nom h et remplace le but par  *)
(*  --------  * B.                                              *)
(*   A => B   *                                                 *)
(****************************************************************)

Ltac implique_intro h := 
	match goal with
	| |- _ -> _ => try intro h
	| |- ~ _  => try intro h
	| _ => idtac "Erreur: aucun implique dans le but courant."
	end
.


(****************************************************************)
(*             * implique_elim h :                              *)
(*             * Si h est de la forme A=>B et le but            *)
(*             * courant de la forme B remplace le but par A.   *)
(*             * Si h est de la forme A et le but courant de la *)
(*   A  A=>B   * forme A=>B remplace le but par A.              *)
(*  ---------  *                                                *)
(*      B      * implique_elim h i j :                          *)
(*             * Si h est de la forme A=>B et i de la forme A   *)
(*             * Cree une nouvelle hypothèse j contenant B.     *)
(*             *                                                *)
(****************************************************************)

Inductive ltac_No_arg : Set :=
  | ltac_no_arg : ltac_No_arg.

Ltac implique_elim_tac h i j :=
	match type of i with
	| ltac_No_arg => match goal with 
					 | |- _ -> _ => try elim h 
					 | |- ?X1 => try apply h
					 | _ => idtac "Erreur: l'hypotese n'est pas appliquable au but courant." end
	| _ => try pose ( j := h i )
	| _ => idtac "Erreur: impossible de creer le resolvant des deux hypoteses."
	end
.

Tactic Notation "implique_elim" constr(h) :=
  implique_elim_tac h ltac_no_arg ltac_no_arg.
Tactic Notation "implique_elim" constr(h) constr(i) ident(j) :=
  implique_elim_tac h i j.


(****************************************************************)
(*            * et_elim_1 h h_decomp:                           *)
(*   A /\ B   * Si h est de la forme A /\ B rajoute A aux       *)
(*  --------  * hypotèses sous le nom h_decomp.                 *)
(*     A      *                                                 *)
(*            *                                                 *)
(****************************************************************)

Ltac et_elim_1 h h_decomp :=
	match type of h with
	| _ /\ _ => try ( elim h; intros h_decomp Tmp ; clear Tmp ) 
	| _ => idtac "Erreur: l'hypotese n'est pas decomposable."
	end
.


(****************************************************************)
(*            * et_elim_1 h h_decomp:                           *)
(*   A /\ B   * Si h est de la forme A /\ B rajoute B aux       *)
(*  --------  * hypotèses sous le nom h_decomp.                 *)
(*     B      *                                                 *)
(*            *                                                 *)
(****************************************************************)

Ltac et_elim_2 h h_decomp :=
	match type of h with
	| _ /\ _ => try (elim h; intros Tmp h_decomp ; clear Tmp)
	| _ => idtac "Erreur: l'hypotese n'est pas decomposable."
	end
.


(****************************************************************)
(*            * et_intro :                                      *)
(*   A    B   * Si le but est de la forme A /\ B Decompose le   *)
(*  --------  * but courant en deux sous-but contenant A et B.  *)
(*   A /\ B   *                                                 *)
(*            *                                                 *)
(****************************************************************)

Ltac et_intro :=
	match goal with
	| |- _ /\ _ => try split
	| _ => idtac "Erreur: le but courant n'est pas décomposable."
	end
.


(****************************************************************)
(*            * ou_intro_1 :                                    *)
(*     A      * Si le but est de la forme A \/ B remplace le    *)
(*  --------  * but courant par A.                              *)
(*   A \/ B   *                                                 *)
(*            *                                                 *)
(****************************************************************)

Ltac ou_intro_1 :=
	match goal with
	| |- _ \/ _ => try left
	| _ => idtac "Erreur: introduction de l'hypotese impossible."
	end
.


(****************************************************************)
(*            * ou_intro_2 :                                    *)
(*     B      * Si le but est de la forme A \/ B remplace le    *)
(*  --------  * but courant par B.                              *)
(*   A \/ B   *                                                 *)
(*            *                                                 *)
(****************************************************************)

Ltac ou_intro_2 :=
	match goal with
	| |- _ \/ _ => try right
	| _ => idtac "Erreur: introduction de l'hypotese impossible."
	end
.


(****************************************************************)
(*                  * ou_elim h :                               *)
(*  A\/B A=>C B=>C  * Si h est de la forme A \/ B et le but     *)
(*  --------------  * courant de la forme C cree deux nouveaux  *)
(*        C         * buts A=>C et B=>C.                        *)
(*                  *                                           *)
(****************************************************************)

Ltac ou_elim h :=
	match type of h with
	| _ \/ _ => try elim h
	| _ => idtac "Erreur: forme de l'hypotese incorrecte."
	end
.


(****************************************************************)
(*           * efq :                                            *)
(*    _|_    * Remplace le but courant par False.               *)
(*  -------  *                                                  *)
(*     A     *                                                  *)
(*           *                                                  *)
(****************************************************************)

Ltac efq := try exfalso.


(****************************************************************)
(*           * raa :                                            *)
(*    ~~A    * Si le but est de la forme ~~A ou                 *)
(*  -------  * (A => False => False) le remplace par A.         *)
(*     A     *                                                  *)
(*           *                                                  *)
(****************************************************************)

Ltac raa :=
	match goal with
	| |- (~~ _ ) => try (intro tmp ; apply tmp ; clear tmp)
	| |- ( _ -> False -> False) => try (intro tmp ; apply tmp ; clear tmp)
	| _ => idtac "Erreur: reduction a l absurde impossible sur le but courant."
	end
.
