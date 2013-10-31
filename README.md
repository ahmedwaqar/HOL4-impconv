=====================================
Implicational conversions
=====================================


This HOL4 library provides essentially three tactics:
  - IMP_REWRITE_TAC
  - TARGET_REWRITE_TAC
  - HINT_EXISTS_TAC

The most useful ones are IMP_REWRITE_TAC and TARGET_REWRITE_TAC.
These tactics are very powerful and many proofs end up being combinations of these two tactics only.

The general objective of these tactics is to reduce the distance between the informal reasoning
of the user, and the formal reasoning of the theorem prover.
As often, this is done through automation.
Contrarily to the usual automation developments, we do not target the automation of \emph{complex} reasoning
(e.g., arithmetic, inductive, SMT reasoning, etc.),
but instead focus on intuitively \emph{simple} reasoning steps which
translate into complex tactics sequences.
The underlying rationale is to leave complex reasoning to the human,
and simple reasoning to the machine (which is not the case currently, since a lot of informally simple
reasoning still ends up being formally complex).

More concretely, these tactics have a common point: they avoid writing terms 
(or expressions related to terms, like paths) explicitly in proof scripts.
This happens generally when using SUBGOAL_THEN, ... by ..., EXISTS_TAC, or GEN_TAC.
The motivation behind this is that such an explicit piece of information
is tedious and time-consuming to devise and to write.
Another disadvantage of writing explicitly these sorts of information is that it yields very fragile proofs:
definition changes, goal changes, name changes, etc., can break the tactic and therefore the whole script.
We basically provide here heuristics to automate the generation of such information.


INSTALLATION

Compile using Holmake:
 
  .../HOL4-imp-conv> Holmake

Use inside HOL4:

  - app load ["TargetRewrite"];
  - open ImpRewrite TargetRewrite;

