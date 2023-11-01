---
title: Coq Tactics Cheatsheet
date: 2023-11-01
toc: true
---

# Solving Simple Goals
This is a growing list of Coq-specific things I encountered while working on a modeling project.
I figured this could help as an introductory guide to Coq for those unfamiliar.
Typically, when writing Coq proofs, your goal is to transform or simplify the goal until it can be solved using one of the following tactics.

reflexivity
-----------
`reflexivity` is a basic tactic to be used when proving something equals itself:

<pre><code class="language-coq">Lemma use_reflexivity:
    (* Simple theorem, x always equals x *)
    forall x: Set, x = x.
Proof.
    (* Iintroduce variables/hypotheses *)
    intro.
    reflexivity.
Qed.
</code></pre>

assumption
----------
When the goal is already in the context, you can use `assumption` to prove it:

<pre><code class="language-coq">Lemma p_implies_p : forall P : Prop,
    (* P implies P is always true *)
    P -> P.
Proof.
    (* We can specify names for introduced variables/hypotheses *)
    intros P P_holds.
</code></pre>
After introducing this hypothesis, `P_holds` (stating that `P` is true) into the context, we can use `assumption` to complete the proof:
<pre><code class="language-coq">Lemma p_implies_p : forall P : Prop,
    P -> P.
Proof.
    intros P P_holds.
    assumption.
Qed.
</code></pre>