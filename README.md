# Stage2017_COQ
La logique du premier ordre prouvée avec Coq

## Synopsis

Adapter les tactiques de preuve en logique du premier ordre de COQ à celles du cours de _logique et démonstration automatique_ (INF402).

## Liste du contenu

- Preuve_tactique_classique/ : preuves avec les tactiques natives de Coq;
- Preuve_tactique_cours/ : preuves utilisant les tactiques réecrites ( Deduction naturelle seulement pour l'instant );
- tactics.v : tactiques du cours écrites avec Ltac.

## Installation

Ces fichiers requièrent Coq 8.6 :
https://coq.inria.fr/download

## Execution

> coqtop -lv filename.v

Donne la trace de la preuve dans la sortie standard et la stock dans l'environement de la session coqtop.

Pour les fichiers requierant "tactics.v" le seul moyen que j'ai trouvé pour le moment est de copier/coller le contenu de "tactics.v" dans coqtop puis de faire de même avec le fichier de preuve.
