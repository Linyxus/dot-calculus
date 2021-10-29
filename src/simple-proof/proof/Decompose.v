(** printing ⊢#    %\vdash_{\#}%    #&vdash;<sub>&#35;</sub>#     *)
(** printing ⊢##   %\vdash_{\#\#}%  #&vdash;<sub>&#35&#35</sub>#  *)
(** printing ⊢##v  %\vdash_{\#\#v}% #&vdash;<sub>&#35&#35v</sub># *)
(** printing ⊢!    %\vdash_!%       #&vdash;<sub>!</sub>#         *)
(** remove printing ~ *)

(** This module reasons about the precise types of variables in inert contexts. *)

Set Implicit Arguments.

Require Import Coq.Program.Equality.
Require Import Definitions RecordAndInertTypes TightTyping PreciseSubtyping.
Require Import Binding.


Theorem destruct_subtyp_typ_t : forall G0,
    inert G0 ->
    (forall A S1 T1 S2 T2,
        G0 ⊢# typ_rcd (dec_typ A S1 T1) <: typ_rcd (dec_typ A S2 T2) ->
        G0 ⊢# S2 <: S1 /\ G0 ⊢# T1 <: T2).
Proof.
  eauto.
Qed.


Lemma sub_p_reduce_rcd_right : forall G U1 U2 A S T L,
    G ⊢! U1 <: U2 ->
    rcd_with_unique_typ U2 L (typ_rcd (dec_typ A S T)) ->
    G ⊢! U1 <: typ_rcd (dec_typ A S T).
Proof.
  intros G U1 U2 A S T L H H1.
  remember (typ_rcd (dec_typ A S T)) as Obj2.
  rename HeqObj2 into Heq.
  induction H1.
  - (* typ *) auto.
  - (* fld *) inversion Heq.
  - (* andl *)
    apply destruct_subtyp_and2_p in H.
    destruct H as [H1 H2].
    specialize (IHrcd_with_unique_typ1 H1 Heq). auto.
  - (* andr *)
    apply destruct_subtyp_and2_p in H.
    destruct H as [H1 H2].
    specialize (IHrcd_with_unique_typ2 H2 Heq). auto.
Qed.


Lemma rcd_with_unique_typ_in_labels : forall U L A S T,
    rcd_with_unique_typ U L (typ_rcd (dec_typ A S T)) ->
    A \in L.
Proof.
  intros U L A S T H.
  remember (typ_rcd (dec_typ A S T)) as T1.
  induction H.
  - (* typ *) inversion HeqT1. subst. apply in_singleton_self.
  - (* fld *) inversion HeqT1.
  - (* andl *)
    specialize (IHrcd_with_unique_typ1 HeqT1).
    rewrite in_union. left. auto.
  - (* andr *)
    specialize (IHrcd_with_unique_typ2 HeqT1).
    rewrite in_union. right. auto.
Qed.


Lemma destruct_and_subp_rcd : forall G U1 U2 A S T,
    G ⊢! typ_and U1 U2 <: typ_rcd (dec_typ A S T) ->
    G ⊢! U1 <: typ_rcd (dec_typ A S T) \/ G ⊢! U2 <: typ_rcd (dec_typ A S T).
Proof.
  intros G U1 U2 A S T H.
  inversion H.
  - auto.
  - auto.
Qed.


Lemma rcd_with_unique_typ_notin_labels : forall G U L T1 A S T,
    rcd_with_unique_typ U L T1 ->
    A \notin L ->
    ~ G ⊢! U <: typ_rcd (dec_typ A S T).
Proof.
  intros G U L T1 A S T H1 Hn Ha.
  induction H1.
  - (* typ *)
    rewrite -> notin_singleton in Hn.
    apply destruct_subtyp_typ_p_label in Ha.
    subst A0. apply Hn. trivial.
  - (* fld *)
    inversion Ha.
  - (* andl *)
    apply notin_union in Hn. destruct Hn as [Hn1 Hn2].
    apply destruct_and_subp_rcd in Ha.
    destruct Ha.
    -- specialize (IHrcd_with_unique_typ1 Hn1 H0). contradiction.
    -- specialize (IHrcd_with_unique_typ2 Hn2 H0). contradiction.
  - (* andl *)
    apply notin_union in Hn. destruct Hn as [Hn1 Hn2].
    apply destruct_and_subp_rcd in Ha.
    destruct Ha.
    -- specialize (IHrcd_with_unique_typ1 Hn1 H0). contradiction.
    -- specialize (IHrcd_with_unique_typ2 Hn2 H0). contradiction.
Qed.


Lemma sub_p_reduce_rcd_left : forall G U L A S1 T1 S2 T2,
    G ⊢! U <: typ_rcd (dec_typ A S2 T2) ->
    rcd_with_unique_typ U L (typ_rcd (dec_typ A S1 T1)) ->
    G ⊢! typ_rcd (dec_typ A S1 T1) <: typ_rcd (dec_typ A S2 T2).
Proof.
  intros G U L A S1 T1 S2 T2 H Hu.
  remember (typ_rcd (dec_typ A S1 T1)) as Tr in Hu.
  induction Hu.
  - (* typ *) inversion HeqTr. subst. exact H.
  - (* fld *) inversion HeqTr.
  - (* andl *)
    apply destruct_and_subp_rcd in H.
    destruct H as [H | H].
    + specialize (IHHu1 H HeqTr). auto.
    + subst T0. apply rcd_with_unique_typ_in_labels in Hu1.
      apply (disjoint_in_notin H0) in Hu1.
      contradict H.
      eapply rcd_with_unique_typ_notin_labels.
      apply Hu2. auto.
  - (* andr *)
    apply destruct_and_subp_rcd in H.
    destruct H as [H | H].
    + subst T3. apply rcd_with_unique_typ_in_labels in Hu2.
      apply disjoint_comm in H0.
      apply (disjoint_in_notin H0) in Hu2.
      contradict H.
      eapply rcd_with_unique_typ_notin_labels.
      apply Hu1. auto.
    + specialize (IHHu2 H HeqTr). auto.
Qed.

Lemma sub_p_reduce_rcd_both : forall G U1 U2 A S1 T1 S2 T2,
    rcd_has_uniq_tm U1 A S1 T1 ->
    rcd_has_uniq_tm U2 A S2 T2 ->
    G ⊢! U1 <: U2 ->
    G ⊢! typ_rcd (dec_typ A S1 T1) <: typ_rcd (dec_typ A S2 T2).
Proof.
  intros G U1 U2 A S1 T1 S2 T2 Hu1 Hu2 Hs.
  destruct Hu1 as [L1 Hu1].
  destruct Hu2 as [L2 Hu2].
  eapply sub_p_reduce_rcd_left.
  - eapply sub_p_reduce_rcd_right.
    -- apply Hs.
    -- apply Hu2.
  - apply Hu1.
Qed.


Lemma destruct_subtyp_rcd_p : forall G0,
    inert G0 ->
    (forall U1 U2 A S1 T1 S2 T2,
        rcd_has_uniq_tm U1 A S1 T1 ->
        rcd_has_uniq_tm U2 A S2 T2 ->
        G0 ⊢! U1 <: U2 ->
        G0 ⊢# S2 <: S1 /\ G0 ⊢# T1 <: T2).
Proof.
  intros G0 H0 U1 U2 A S1 T1 S2 T2 Hu1 Hu2 Gs.
  assert (G0 ⊢! typ_rcd (dec_typ A S1 T1) <: typ_rcd (dec_typ A S2 T2)) as Hs1.
  {
    eapply sub_p_reduce_rcd_both. apply Hu1. apply Hu2. auto.
  }
  eapply destruct_subtyp_typ_p. apply H0. apply Hs1.
Qed.


Lemma destruct_subtyp_rcd_t : forall G0,
    inert G0 ->
    (forall U1 U2 A S1 T1 S2 T2,
        rcd_has_uniq_tm U1 A S1 T1 ->
        rcd_has_uniq_tm U2 A S2 T2 ->
        G0 ⊢# U1 <: U2 ->
        G0 ⊢# S2 <: S1 /\ G0 ⊢# T1 <: T2).
Proof.
  intros G0 H0 U1 U2 A S1 T1 S2 T2 Hu1 Hu2 Hs.
  eapply destruct_subtyp_rcd_p.
  - apply H0.
  - apply Hu1.
  - apply Hu2.
  - eapply tight_to_prec.
    apply H0.
    apply Hs.
Qed.

