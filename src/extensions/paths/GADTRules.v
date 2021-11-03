(** printing ⊢#    %\vdash_{\#}%    #&vdash;<sub>&#35;</sub>#     *)
(** printing ⊢##   %\vdash_{\#\#}%  #&vdash;<sub>&#35&#35</sub>#  *)
(** printing ⊢##v  %\vdash_{\#\#v}% #&vdash;<sub>&#35&#35v</sub># *)
(** printing ⊢!    %\vdash_!%       #&vdash;<sub>!</sub>#         *)
(** remove printing ~ *)

Require Import Coq.Program.Equality.
Require Import Definitions TightTyping SemanticSubtyping PreciseTyping.
Require Import Replacement.


Lemma subtyp_sngl_pq1_t : forall G p q S S' T U,
    G ⊢!!! p : {{ q }} ->
    G ⊢!!! q : U ->
    G ⊢# S <: T ->
    repl_typ p q S S' ->
    G ⊢# S' <: T.
Proof.
  introv Hp Hq Hst Hr.
  destruct repl_swap as [repl_swap _].
  apply repl_swap in Hr.
  eauto.
Qed.


Lemma subtyp_sngl_qp1_t : forall G p q S S' T U,
    G ⊢!!! p : {{ q }} ->
    G ⊢!!! q : U ->
    G ⊢# S <: T ->
    repl_typ q p S S' ->
    G ⊢# S' <: T.
Proof.
  introv Hp Hq Hst Hr.
  destruct repl_swap as [repl_swap _].
  apply repl_swap in Hr.
  eauto.
Qed.


Lemma invert_subtyp_typ_s : forall G A S1 T1 S2 T2,
    G ⊢{} typ_rcd {A >: S1 <: T1} <: typ_rcd {A >: S2 <: T2} ->
    G ⊢# S2 <: S1 /\ G ⊢# T1 <: T2.
Proof.
  introv Hsub.
  remember (typ_rcd {A >: S1 <: T1}) as typ1 in Hsub.
  remember (typ_rcd {A >: S2 <: T2}) as typ2 in Hsub.
  gen S1 T1 S2 T2.
  induction Hsub; intros; try inversion Heqtyp1; try inversion Heqtyp2.
  - subst T. inversion H0. eauto.
  - subst. eauto.
  - subst. clear H2 H3.
    specialize (IHHsub S1 T1).
    inversion H1; subst.
    inversion H6; subst.
    -- assert (G ⊢# T0 <: S1 /\ G ⊢# T1 <: T2) as Hg.
       {
         apply IHHsub with (S2 := T0) (T3 := T2); trivial.
       }
       destruct Hg as [Hg1 Hg2].
       split; try trivial.
       eapply subtyp_sngl_pq1_t.
       exact H.
       exact H0.
       exact Hg1.
       exact H7.
    -- assert (G ⊢# S2 <: S1 /\ G ⊢# T1 <: T0) as Hg.
       {
         apply IHHsub with (S3 := S2) (T2 := T0); trivial.
       }
       destruct Hg as [Hg1 Hg2].
       split; auto.
       eauto.
  - subst. clear H2 H3.
    specialize (IHHsub S1 T1).
    inversion H1; subst. inversion H6; subst; clear H6.
    -- assert (G ⊢# T0 <: S1 /\ G ⊢# T1 <: T2) as [Hg1 Hg2].
       {
         apply IHHsub with (S2 := T0) (T3 := T2); trivial.
       }
       split; auto.
       eapply subtyp_sngl_qp1_t.
       exact H. exact H0. exact Hg1. exact H7.
    -- assert (G ⊢# S2 <: S1 /\ G ⊢# T1 <: T0) as [Hg1 Hg2].
       {
         apply IHHsub with (S3 := S2) (T2 := T0); trivial.
       }
       split; auto.
       eauto.
  - subst. clear H2 H3.
    inversion H1; subst. inversion H6; subst; clear H6.
    -- assert (G ⊢# S2 <: T0 /\ G ⊢# T1 <: T2) as [Hg1 Hg2].
       {
         apply IHHsub with (S1 := T0) (T3 := T1) (S3 := S2) (T4 := T2); trivial.
       }
       split; auto.
       destruct repl_swap as [Hs _]. apply Hs in H7.
       eauto.
     -- assert (G ⊢# S2 <: S1 /\ G ⊢# T0 <: T2) as [Hg1 Hg2].
        {
          apply IHHsub with (S3 := S1) (T1 := T0) (S4 := S2) (T3 := T2); trivial.
        }
        split; auto. destruct repl_swap as [Hs _]. eauto.
  - subst; clear H2 H3.
    inversion H1; subst. inversion H6; subst; clear H6.
    -- assert (G ⊢# S2 <: T0 /\ G ⊢# T1 <: T2) as [Hg1 Hg2].
       {
         apply IHHsub with (S1 := T0) (T3 := T1) (S3 := S2) (T4 := T2); trivial.
       }
       split; auto.
       destruct repl_swap as [Hs _]. apply Hs in H7.
       eauto.
     -- assert (G ⊢# S2 <: S1 /\ G ⊢# T0 <: T2) as [Hg1 Hg2].
        {
          apply IHHsub with (S3 := S1) (T1 := T0) (S4 := S2) (T3 := T2); trivial.
        }
        split; auto. destruct repl_swap as [Hs _]. eauto.
Qed.


Theorem invert_subtyp_typ_t : forall G A S1 T1 S2 T2,
    inert G ->
    G ⊢# typ_rcd {A >: S1 <: T1} <: typ_rcd {A >: S2 <: T2} ->
    G ⊢# S2 <: S1 /\ G ⊢# T1 <: T2.
Proof.
  introv Hi Hs.
  eapply invert_subtyp_typ_s.
  apply tight_to_semantic; eauto.
Qed.

