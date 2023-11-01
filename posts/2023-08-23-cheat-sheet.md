---
title: Coq Tactics Cheatsheet
---

This is a growing list of Coq-specific things I encountered while working on a modeling project.
I figured this could help as an introductory guide to Coq for those unfamiliar.


reflexivity
-------------
`reflexivity` is a basic tactic to be used when proving something equals itself.

<pre><code class="language-coq">Lemma use_reflexivity:
    forall x: Set, x = x.
Proof.
    intro.
    reflexivity.
Qed.
</code></pre>