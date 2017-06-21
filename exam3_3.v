(***********************************************************************************)
(*  Examen mai 2017                                                                *)
(*  Exercice 3.3                                                                   *)
(*                                                                                 *)
(*  ((forall x, P x -> Q x) /\ (exists x, ~ Q x)) -> (exists x, ~ P x)             *)
(*                                                                                 *)
(*  contexte | no  | ligne                                        | regle          *)
(*  1        | 1   | Sup (forall x, P x => Q x)/\(exists x, ~Q x) | hyp            *)
(*  1        | 2   | forall x, P x => Q x                         | /\E1,1         *)
(*  1        | 3   | exists x, ~Q x                               | /\E2,1         *)
(*  1,4      | 4   | Sup ~Q x                                     | hyp            *)
(*  1,4      | 5   | P x /\ Q x                                   | forallE,2      *)
(*  1,4,6    | 6   | Sup P x                                      | hyp            *)
(*  1,4,6    | 7   | Q x                                          | =>E,5 6        *)
(*  1,4,6    | 8   | _|_                                          | =>E,4 7        *)
(*  1,4      | 9   | Donc ~P x                                    | =>I,6 8        *)
(*  1,4      | 10  | exists x, ~P x                               | existsI,9      *)
(*  1        | 11  | Donc ~Q x => exists x, ~P x                  | =>I, 4 10      *)
(*  1        | 12  | exists x, ~P x                               | existsE, 3 11  *)
(*           | 13  | Donc cqfd                                    | =>I, 1 12      *)
(*                                                                                 *)
(***********************************************************************************)


Require Import Classical.


Section Declaration.

Variable D : Set.
Variable P : D -> Prop.
Variable Q : D -> Prop.

Section Preuve. 

Lemma exam33 : ((forall x : D, P x -> Q x) /\ (exists x : D, ~ Q x)) -> (exists x : D, ~ P x).

intro H0.
elim H0.
intros H0_decomp_G H0_decomp_D.
elim H0_decomp_D.
intros x0 H1.
pose ( PimplieQ_x0 := H0_decomp_G x0).
exists x0.
intro H2.
pose (Q_x0 := PimplieQ_x0 H2).
pose (bottomProof := H1 Q_x0).
case bottomProof.

Qed.

End Preuve.
End Declaration.

Check exam33.

Quit.