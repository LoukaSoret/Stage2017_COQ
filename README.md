# Stage2017_COQ
La logique du premier ordre prouver avec Coq

## Synopsis

Adapter les tactiques de preuve en logique du premier ordre de COQ à celles du cours de logique et démonstration automatique (INF402). 

## Installation

Ces fichiers requièrent Coq 8.6 :
https://coq.inria.fr/download

## Execution

> coqtop -lv filename.v

Donne la trace de la preuve dans la sortie standard et la stock dans l'environement de la session coqtop.

Pour les fichiers requierant "tactics.v" le seul moyen que j'ai trouver pour le moment et de copier/coller le contenu de "tactics.v" dans coqtop puis de faire de même avec le fichier de preuve.
