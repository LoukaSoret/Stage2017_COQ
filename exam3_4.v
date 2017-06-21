(*******************************************************************************************)
(*  Examen mai 2017                                                                        *)
(*  Exercice 3.4                                                                           *)
(*                                                                                         *)
(*  (exists x, forall y, x = y) -> (forall x, forall y, x = y)                             *)
(*                                                                                         *)
(*  contexte | no  | ligne                                               | regle           *)
(*  1        | 1   | Sup exists x, forall y, x = y                       | hyp             *)
(*  1,2      | 2   | Sup forall y, x = y                                 | hyp             *)
(*  1,2      | 3   | x = u                                               | forallE,2 y:=u  *)
(*  1,2      | 4   | x = y                                               | forallE, 2      *)
(*  1,2      | 5   | u = y                                               | Congru,3 4      *)
(*  1,2      | 6   | forall y, u = y                                     | forallI, 5      *)
(*  1,2      | 7   | forall u, forall y, u = y                           | forallI, 5      *)
(*  1,2      | 8   | forall x, forall y, x = y                           | Copie 7         *)
(*  1        | 9   | Donc (forall y, x = y) => forall x, forall y, x = y | =>I,2 8         *)
(*  1        | 10  | forall x, forall y, x = y                           | existsE, 8 9    *)
(*           | 11  | Donc cqfd                                           | =>I, 1 11       *)
(*                                                                                         *)
(*******************************************************************************************)


Require Import Classical.


Section Declaration.

Variable D : Set.


Section Preuve. 

Lemma exam34 : (exists x : D, forall y : D, x = y) -> (forall x : D, forall y : D, x = y).

intros H0 x0 y0.
elim H0.
intros u H1.
replace x0 with u.
trivial.
apply H1.

Qed.

End Preuve.
End Declaration.

Check exam34.

Quit.