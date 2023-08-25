---
title: Coq Tactics Cheatsheet
---

Place holder for now. This is a growing list of Coq-specific things I needed to clarify while working on the Wasm project.


reflexivity
-------------
`reflexivity` is a basic tactic to be used when proving something equals itself.

```coq
Lemma use_reflexivity:
    forall x: Set, x = x.
Proof.
    intro.
    reflexivity.
Qed.
```