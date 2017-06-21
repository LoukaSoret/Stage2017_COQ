(***********************************************************************************)
(*  Poly Logique et demonstration automatique                                      *)
(*  P140,Exercice 97.6                                                             *)
(*                                                                                 *)
(*  (forall x, P x -> Q x) /\ (exists x, P x) -> (exists x, Q x)                   *)
(*                                                                                 *)
(*  contexte | no  | ligne                                        | regle          *)
(*  1        | 1   | Sup (forall x, P x => Q x)/\(exists x, P x)  | hyp            *)
(*  1        | 2   | forall x, P x => Q x                         | /\E1,1         *)
(*  1        | 3   | exists x, P x                                | /\E2,1         *)
(*  1,4      | 4   | P x /\ Q x                                   | forallE,2      *)
(*  1,4,6    | 5   | Sup P x                                      | hyp            *)
(*  1,4,6    | 6   | Q x                                          | =>E,4 5        *)
(*  1,4,6    | 7   | exists x, Q x                                | existsI,6      *)
(*  1,4      | 8   | Donc P x => exists x, Q x                    | =>I,5 7        *)
(*  1,4      | 9   | exists x, Q x                                | existsE,8 3    *)
(*  1,4      | 10  | Donc cqfd                                    | =>I,1 9        *)
(*                                                                                 *)
(***********************************************************************************)


Require Import Classical.


Section Declaration.

Variable D : Set.
Variable P : D -> Prop.
Variable Q : D -> Prop.


Section Preuve. 

Lemma ex976 : (forall x : D, P x -> Q x) /\ (exists x : D, P x) -> (exists x : D, Q x).

intro H0.
elim H0.
intros H0_decomp_G H0_decomp_D.
elim H0_decomp_D.
intros x0 P_x0.
exists x0.
apply H0_decomp_G.
exact P_x0.

Qed.

End Preuve.
End Declaration.

Check ex976.

Quit.