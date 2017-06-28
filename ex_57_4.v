(*************************************************************************)
(*  Poly Logique et demonstration automatique                            *)
(*  P77,Exercice 53.2                                                    *)
(*                                                                       *)
(*  A /\ (B \/ C) -> A /\ B \/ A /\ C                                    *)
(*                                                                       *)
(*  contexte | no | ligne                              | regle           *)
(*  1        | 1  | Sup A /\ (B \/ C)                  | hyp             *)
(*  1        | 2  | A                                  | /\E1,1          *)
(*  1        | 3  | B \/ C                             | /\E2,1          *)
(*  1,2      | 4  | Sup B                              | hyp             *)
(*  1,2      | 5  | A /\ B                             | /\I,2 4         *)
(*  1,2      | 6  | A /\ B \/ A /\ C                   | \/I1,5          *)
(*  1,2      | 7  | Donc B -> A /\ B \/ A /\ C         | =>I,4 6         *)
(*  1,2      | 8  | Sup C                              | hyp             *)
(*  1,2      | 9  | A /\ C                             | /\I,2 8         *)
(*  1,2      | 10 | A /\ B \/ A /\ C                   | \/I2,9          *)
(*  1,2      | 11 | Donc C -> A /\ B \/ A /\ C         | =>I,8 10        *)
(*  1        | 12 | A /\ B \/ A /\ C                   | \/E,3 7 11      *)
(*           | 13 | Donc cqfd                          | =>I,1 12        *)
(*                                                                       *)
(*************************************************************************)


Section Declaration.

Variable A : Prop.
Variable B : Prop.
Variable C : Prop.

Section Preuve.

Lemma ex574 : A /\ (B \/ C) -> A /\ B \/ A /\ C.

implique_intro H.
et_elim_1 H H_G.
et_elim_2 H H_D.
ou_elim H_D.
 implique_intro HB.
 ou_intro_1.
 et_intro.
  exact H_G.

  exact HB.

 implique_intro HC.
 ou_intro_2.
 et_intro.
  exact H_G.

  exact HC.

Qed

End Preuve.
End Declaration.

Check ex574.