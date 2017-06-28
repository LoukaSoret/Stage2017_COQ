(*************************************************************************)
(*  Poly Logique et demonstration automatique                            *)
(*  P77,Exercice 53.2                                                    *)
(*                                                                       *)
(*  (A -> B) /\ (B -> C) -> (A -> C)                                     *)
(*                                                                       *)
(*  contexte | no | ligne                              | regle           *)
(*  1        | 1  | Sup (A -> B) /\ (B -> C)           | hyp             *)
(*  1        | 2  | A -> B                             | /\E1,1          *)
(*  1        | 3  | B -> C                             | /\E2,1          *)
(*  1,2      | 4  | Sup A                              | hyp             *)
(*  1,2      | 5  | B                                  | =>E,2 4         *)
(*  1,2      | 6  | C                                  | =>E,3 5         *)
(*  1        | 7  | Donc A -> C                        | =>I,4 6         *)
(*           | 8  | Donc cqfd                          | =>I,1 7         *)
(*                                                                       *)
(*************************************************************************)

Require Import Classical.

Section Declaration.

Variable A : Prop.
Variable B : Prop.
Variable C : Prop.

Section Preuve.

Lemma ex532 : (A -> B) /\ (B -> C) -> (A -> C).

implique_intro H0.
implique_intro HA.
et_elim_1 H0 H0_G.
et_elim_2 H0 H0_D.
implique_elim H0_D.
implique_elim H0_G.
exact HA.

Qed.

End Preuve.
End Declaration.

Check ex532.

