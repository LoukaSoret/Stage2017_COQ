Ltac implique_intro h := 
	match goal with
	| |- (?X1 -> ?X2) => try intro h
	| |- (~?X1) => try intro h
	| _ => idtac "Erreur: aucun implique dans le but courant."
	end
.

Ltac noname h i j := try pose (j := h i).

Ltac implique_elim h :=
	match goal with
	| |- (?X1 -> ?X2) => try elim h
	| |- (?X1) => try apply h
	| _ => idtac "Erreur: l'hypotese n'est pas appliquable au but courant."
	end
.

Ltac et_elim_1 h h_decomp :=
	match type of h with
	| _ /\ _ => try ( elim h; intros h_decomp Tmp ; clear Tmp ) 
	| _ => idtac "Erreur: l'hypotese n'est pas decomposable."
	end
.

Ltac et_elim_2 h h_decomp :=
	match type of h with
	| _ /\ _ => try (elim h; intros Tmp h_decomp ; clear Tmp)
	| _ => idtac "Erreur: l'hypotese n'est pas decomposable."
	end
.

Ltac et_intro :=
	match goal with
	| |- (?X1 /\ ?X2) => try split
	| _ => idtac "Erreur: le but courant n'est pas décomposable."
	end
.

Ltac ou_intro_1 :=
	match goal with
	| |- (?X1 \/ ?X2) => try left
	| _ => idtac "Erreur: introduction de l'hypotese impossible."
	end
.

Ltac ou_intro_2 :=
	match goal with
	| |- (?X1 \/ ?X2) => try right
	| _ => idtac "Erreur: introduction de l'hypotese impossible."
	end
.

Ltac ou_elim h :=
	match type of h with
	| _ \/ _ => try elim h
	| _ => idtac "Erreur: forme de l'hypotese incorrecte."
	end
.

Ltac efq := try exfalso.

Ltac raa :=
	match goal with
	| |- (~~?X1) => try (intro tmp ; apply tmp ; clear tmp)
	| |- (?X1 -> False -> False) => try (intro tmp ; apply tmp ; clear tmp)
	| _ => idtac "Erreur: reduction a l absurde impossible sur le but courant."
	end
.
