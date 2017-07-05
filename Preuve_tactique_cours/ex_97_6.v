
Section Declaration.

Variable D : Set.
Variable P : D->Prop.
Variable Q : D->Prop.
Variable x0 : D.

Section Preuve.

Lemma ex976 : ((forall x:D, P x -> Q x) /\ (exists x:D, P x)) -> (exists x:D, Q x) .

implique_intro H.
et_elim_1 H H_G.
et_elim_2 H H_D.
existe_elim H_D x.
implique_intro H0.
pourtout_elim H_G implie x.
implique_elim implie H0 H1.
existe_intro x.
exact H1.

Qed.

End Preuve.
End Declaration.

Check ex976.