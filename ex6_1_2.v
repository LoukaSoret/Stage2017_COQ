(*************************************************************************)
(*  Poly Logique et demonstration automatique                            *)
(*  P133,Exemple 6.1.2                                                   *)
(*                                                                       *)
(*  (forall y, P y) /\ (forall y, Q y) -> (forall x, P x /\ Q x)         *)
(*                                                                       *)
(*  contexte | no | ligne                              | regle           *)
(*  1        | 1  | Sup forall y, P y /\ forall y, Q y | hyp             *)
(*  1        | 2  | forall y, P y                      | /\E1,1          *)
(*  1        | 3  | forall y, Q y                      | /\E2,1          *)
(*  1        | 4  | P x                                | forallE,2 y:=x  *)
(*  1        | 5  | Q x                                | forallE,3 y:=x  *)
(*  1        | 6  | P x /\ Q x                         | /\I,5 4         *)
(*  1        | 7  | forall x, P x /\ Q x               | forallI, 6      *)
(*           | 8  | Donc cqfd                          | =>I, 1 7        *)
(*                                                                       *)
(*************************************************************************)

Require Import Classical.

Section Declaration. 

Variable D : Set.
Variable P : D -> Prop.
Variable Q : D -> Prop.

Section Preuve.

Lemma ex612 : (forall y : D, P y) /\ (forall y : D, Q y) -> (forall x : D, P x /\ Q x). 

intro H0.
elim H0.
intros H0_decomp_G H0_decomp_D.
intro x0.
pose (P_x0 := H0_decomp_G x0).
pose (Q_x0 := H0_decomp_D x0).
split.
exact P_x0.
exact Q_x0.

Qed.

End Preuve.
End Declaration.

Check ex612.

Quit.