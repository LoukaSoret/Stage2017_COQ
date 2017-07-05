
Section Declaration.

Variable D : Set.
Variable P : D->Prop.
Variable Q : D->Prop.
Variable x0 : D.

Section Preuve.

Lemma ex974 : (forall x:D, P x /\ Q x) -> (forall x:D, P x) /\ (forall x:D, Q x) .

implique_intro H.
et_intro.
pourtout_intro x.
pourtout_elim H H0 x. 
et_elim_1 H0 H0_G.
exact H0_G.
pourtout_intro x.
pourtout_elim H H0 x. 
et_elim_2 H0 H0_D.
exact H0_D.

Qed.

End Preuve.
End Declaration.

Check ex974.
