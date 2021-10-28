(** printing ⊢#    %\vdash_{\#}%    #&vdash;<sub>&#35;</sub>#     *)
(** printing ⊢##   %\vdash_{\#\#}%  #&vdash;<sub>&#35&#35</sub>#  *)
(** printing ⊢##v  %\vdash_{\#\#v}% #&vdash;<sub>&#35&#35v</sub># *)
(** printing ⊢!    %\vdash_!%       #&vdash;<sub>!</sub>#         *)
(** remove printing ~ *)

(** This module reasons about the precise types of variables in inert contexts. *)

Set Implicit Arguments.

Require Import Coq.Program.Equality.
Require Import Definitions RecordAndInertTypes InvertibleTyping TightTyping PreciseTyping.

Reserved Notation "G '⊢!' T '<:' U" (at level 40, T at level 59).

Inductive subtyp_p : ctx -> typ -> typ -> Prop :=

(** G ⊢! T <: top *)
| subtyp_top_p : forall G T,
    G ⊢! T <: typ_top

(** [G ⊢! bot <: T] *)
| subtyp_bot_p: forall G T,
    G ⊢! typ_bot <: T

(** [G ⊢! T <: T] *)
| subtyp_refl_p: forall G T,
    G ⊢! T <: T

(** [G ⊢! T <: S]       #<br>#
    [――――――――――――――――]   #<br>#
    [G ⊢! T ∧ U <: S]       *)
| subtyp_and11_p: forall G T U S,
    G ⊢! T <: S ->
    G ⊢! typ_and T U <: S

(** [G ⊢! U <: S]       #<br>#
    [――――――――――――――――]   #<br>#
    [G ⊢! T ∧ U <: S]       *)
| subtyp_and12_p: forall G T U S,
    G ⊢! U <: S ->
    G ⊢! typ_and T U <: S

(** [G ⊢! S <: T]       #<br>#
    [G ⊢! S <: U]       #<br>#
    [――――――――――――――――]   #<br>#
    [G ⊢! S <: T /\ U]       *)
| subtyp_and2_p: forall G S T U,
    G ⊢! S <: T ->
    G ⊢! S <: U ->
    G ⊢! S <: typ_and T U

(** [G ⊢! T <: U]           #<br>#
    [――――――――――――――――――――――] #<br>#
    [G ⊢! {a: T} <: {a: U}]     *)
| subtyp_fld_p: forall G a T U,
    G ⊢! T <: U ->
    G ⊢! typ_rcd (dec_trm a T) <: typ_rcd (dec_trm a U)

(** [G ⊢! x: {A: T..T}] #<br>#
    [G ⊢! S <: T]       #<br>#
    [――――――――――――――――――] #<br>#
    [G ⊢! S <: x.A]         *)
| subtyp_sel2_p: forall G x A T U S,
    G ⊢! x : U ⪼ typ_rcd (dec_typ A T T) ->
    G ⊢! S <: T ->
    G ⊢! S <: typ_sel (avar_f x) A

(** [G ⊢! x: {A: T..T}] #<br>#
    [G ⊢! T <: S]       #<br>#
    [――――――――――――――――――] #<br>#
    [G ⊢! x.A <: S]         *)
| subtyp_sel1_p: forall G x A T U S,
    G ⊢! x : U ⪼ typ_rcd (dec_typ A T T) ->
    G ⊢! T <: S ->
    G ⊢! typ_sel (avar_f x) A <: S


(** [G ⊢ S2 <: S1]                   #<br>#
    [G ⊢ T1 <: T2]                   #<br>#
    [――――――――――――――――――――――――――――――――] #<br>#
    [G ⊢! {A: S1..T1} <: {A: S2..T2}]     *)
| subtyp_typ_p: forall G A S1 T1 S2 T2,
    G ⊢ S2 <: S1 ->
    G ⊢ T1 <: T2 ->
    G ⊢! typ_rcd (dec_typ A S1 T1) <: typ_rcd (dec_typ A S2 T2)

(** [G ⊢! S2 <: S1]                #<br>#
    [G, x: S2 ⊢ T1^x <: T2^x]       #<br>#
    [x fresh]                       #<br>#
    [――――――――――――――――――――――――]      #<br>#
    [G ⊢! forall(S1)T1 <: forall(S2)T2]          *)
| subtyp_all_p: forall L G S1 T1 S2 T2,
    G ⊢! S2 <: S1 ->
    (forall x, x \notin L ->
       G & x ~ S2 ⊢ open_typ x T1 <: open_typ x T2) ->
    G ⊢! typ_all S1 T1 <: typ_all S2 T2

where "G '⊢!' T '<:' U" := (subtyp_p G T U).

Hint Constructors subtyp_p.

Lemma subtyp_p_decompose_typ : forall G0,
    inert G0 ->
    (forall A S1 T1 S2 T2,
        G0 ⊢! typ_rcd (dec_typ A S1 T1) <: typ_rcd (dec_typ A S2 T2) ->
        (G0 ⊢ S2 <: S1 /\ G0 ⊢ T1 <: T2)).
Proof.
  intros G0 H0 A S1 T1 S2 T2 H.
  inversion H; subst; auto.
Qed.

Lemma typ_p_bound_deterministic : forall G0,
    inert G0 ->
    (forall x A U1 U2 T1 T2,
        G0 ⊢! x: U1 ⪼ typ_rcd (dec_typ A T1 T1) ->
        G0 ⊢! x: U2 ⪼ typ_rcd (dec_typ A T2 T2) ->
        T1 = T2).
Proof.
Admitted.

Lemma subtyp_p_trans_typ : forall G0,
    inert G0 ->
    (forall A S1 T1 S2 T2 U,
        G0 ⊢! typ_rcd (dec_typ A S1 T1) <: U ->
        G0 ⊢! U <: typ_rcd (dec_typ A S2 T2) ->
        G0 ⊢! typ_rcd (dec_typ A S1 T1) <: typ_rcd (dec_typ A S2 T2)).
Proof.
  intros G0 Hi.
  intros A S1 T1 S2 T2 U H1 H2.
  generalize dependent S2. generalize dependent T2.
  remember (typ_rcd (dec_typ A S1 T1)) as Obj1 in H1.
  induction H1.
  - intros T2 S2 H.
    inversion H.
  - intros T2 S2 H.
    inversion HeqObj1.
  - intros T2 S2 H.
    subst T. auto.
  - inversion HeqObj1.
  - inversion HeqObj1.
  - specialize (IHsubtyp_p1 Hi HeqObj1). specialize (IHsubtyp_p2 Hi HeqObj1).
    intros T2 S2 H.
    inversion H; subst.
    {
      specialize (IHsubtyp_p1 T2 S2 H4). auto.
    }
    {
      specialize (IHsubtyp_p2 T2 S2 H4). auto.
    }
  - inversion HeqObj1.
  - intros T2 S2 Hsub.
    specialize (IHsubtyp_p Hi HeqObj1 T2 S2).
    inversion Hsub; subst.
    assert (T = T0) as Teq.
      eapply typ_p_bound_deterministic.
        apply Hi.
        apply H.
        apply H4.
    subst T0.
    specialize (IHsubtyp_p H6). auto.
  - inversion HeqObj1.
  - intros T3 S3 Hsub.
    inversion HeqObj1. subst. clear HeqObj1.
    apply (subtyp_p_decompose_typ Hi) in Hsub. destruct Hsub as [H1 H2].
    assert (G ⊢ S3 <: S1) as Hb1.
      eauto.
    assert (G ⊢ T1 <: T3) as Hb2.
      eauto.
    eauto.
  - inversion HeqObj1.
Qed.

Lemma destruct_sub_p_and : forall G S T U,
    G ⊢! typ_and S T <: U ->
    (G ⊢! S <: U \/ G ⊢! T <: U \/ U = typ_and S T).
Proof.
  intros.
  remember (typ_and S T) as And1.
  generalize dependent S. generalize dependent T.
  induction H; intros; auto; eauto; try inversion HeqAnd1.
  - subst. auto.
  - subst. auto.
Admitted.

Inductive fld_intersection_sub_ok (G : ctx) (sub : typ) : typ -> Prop :=
| fiso_top : fld_intersection_sub_ok G sub typ_top
| fiso_fld : forall a T,
  G ⊢! sub <: typ_rcd (dec_trm a T) ->
  fld_intersection_sub_ok G sub (typ_rcd (dec_trm a T))
| fiso_sel : forall x A U T,
  G ⊢! x: U ⪼ typ_rcd (dec_typ A T T) ->
  G ⊢! sub <: T ->
  fld_intersection_sub_ok G sub T ->
  fld_intersection_sub_ok G sub (typ_sel (avar_f x) A)
| fiso_and : forall T1 T2,
  fld_intersection_sub_ok G sub T1 ->
  fld_intersection_sub_ok G sub T2 ->
  fld_intersection_sub_ok G sub (typ_and T1 T2)
.

Hint Constructors fld_intersection_sub_ok.

Lemma fiso_to_sub : forall G0,
    inert G0 ->
    (forall sub T,
        fld_intersection_sub_ok G0 sub T ->
        G0 ⊢! sub <: T).
Proof.
Admitted.

Lemma destruct_fld_sub_p_fiso : forall G0,
    inert G0 ->
    (forall a T U,
        G0 ⊢! typ_rcd (dec_trm a T) <: U ->
        fld_intersection_sub_ok G0 (typ_rcd (dec_trm a T)) U).
Proof.
  intros G0 H0 a T U H.
  remember (typ_rcd (dec_trm a T)) as fld1 in H.
  induction H.
  - (* Top *) auto.
  - (* Bot *) inversion Heqfld1.
  - (* Refl *) subst T0. auto.
  - (* And1-<: *) inversion Heqfld1.
  - (* And2-<: *) inversion Heqfld1.
  - (* <:-And *)
    specialize (IHsubtyp_p1 H0 Heqfld1).
    specialize (IHsubtyp_p2 H0 Heqfld1).
    auto.
  - (* Fld-<:-Fld *)
    inversion Heqfld1. subst.
    assert (G ⊢! typ_rcd (dec_trm a T) <: typ_rcd (dec_trm a U)) as Hsub. auto. auto.
  - (* <:-Sel *)
    subst S.
    assert (G ⊢! typ_rcd (dec_trm a T) <: typ_sel (avar_f x) A) as Hsub. eauto. eauto.
  - (* Sel-<: *)
    inversion Heqfld1.
  - (* Typ-<:-Typ *)
    inversion Heqfld1.
  - (* All-<:-All *)
    inversion Heqfld1.
Qed.


Lemma fld_sub_p_trans_fiso : forall G0,
    inert G0 ->
    (forall a S T U,
        (forall U1, G0 ⊢! T <: U1 -> G0 ⊢! S <: U1) ->
        fld_intersection_sub_ok G0 (typ_rcd (dec_trm a T)) U ->
        fld_intersection_sub_ok G0 (typ_rcd (dec_trm a S)) U).
Proof.
  intros G0 H0 a S T U Ht H.
  induction H.
  - (* top *) auto.
  - (* fld *)
    inversion H; subst.
    { assert (G0 ⊢! S <: T0). auto.
      eauto.
    }
    { assert (G0 ⊢! S <: T0). auto.
      eauto.
    }
  - (* sel *)
    assert (G0 ⊢! typ_rcd (dec_trm a S) <: T0) as Hsub.
      apply fiso_to_sub. auto. auto.
    eauto.
  - (* and *) eauto.
Qed.


Lemma destruct_sel_sub_p1 : forall G0,
    inert G0 ->
    (forall x A U T S,
        G0 ⊢! x: U ⪼ typ_rcd (dec_typ A T T) ->
        G0 ⊢! S <: typ_sel (avar_f x) A ->
        G0 ⊢! S <: T).
Proof.
  intros.
  generalize dependent U. generalize dependent T.
  remember (typ_sel (avar_f x) A) as Sel in H1.
  induction H1.
  - (* Top *) intros. inversion HeqSel.
  - (* Bot *)
    intros. auto.
  - (* Refl *)
    intros. subst T. eauto.
  - (* And1-<: *)
    intros. specialize (IHsubtyp_p H HeqSel).
    apply IHsubtyp_p in H0.
    eauto.
  - (* And1-<: *)
    intros. specialize (IHsubtyp_p H HeqSel).
    apply IHsubtyp_p in H0.
    eauto.
  - (* <:-And *)
    inversion HeqSel.
  - (* Fld-<:-Fld *)
    inversion HeqSel.
  - (* <:-Sel *)
    inversion HeqSel; subst. intros.
    assert (T = T0) as Heq.
      eapply typ_p_bound_deterministic.
        apply H.
        apply H0.
        apply H2.
    subst T. auto.
  - (* Sel-<: *)
    intros. specialize (IHsubtyp_p H HeqSel).
    apply IHsubtyp_p in H2.
    eauto.
  - (* Typ-<:-Typ *)
    intros. inversion HeqSel.
  - (* All-<:-All *)
    intros. inversion HeqSel.
Qed.

Lemma destruct_sel_sub_p2 : forall G0,
    inert G0 ->
    (forall x A U T S,
        G0 ⊢! x: U ⪼ typ_rcd (dec_typ A T T) ->
        G0 ⊢! typ_sel (avar_f x) A <: S ->
        G0 ⊢! T <: S).
Admitted.

Lemma destruct_top_sub_T_p : forall G0,
    inert G0 ->
    (forall S T,
        G0 ⊢! typ_top <: S ->
        G0 ⊢! T <: S).
Proof.
  intros. generalize dependent T.
  remember typ_top as Top in H0.
  induction H0.
  - (* Top *)
    intros. eauto.
  - (* Bot *)
    intros. inversion HeqTop.
  - (* Refl *)
    intros. subst T. auto.
  - (* And1-<: *)
    intros. inversion HeqTop.
  - (* And2-<: *)
    intros. inversion HeqTop.
  - (* <:-And *)
    intros.
    specialize (IHsubtyp_p1 H HeqTop).
    specialize (IHsubtyp_p2 H HeqTop).
    assert (G ⊢! T0 <: T) as H1. auto.
    assert (G ⊢! T0 <: U) as H2. auto.
    eauto.
  - (* Fld-<:-Fld *)
    inversion HeqTop.
  - (* <:-Sel *)
    intros.
    specialize (IHsubtyp_p H HeqTop).
    assert (G ⊢! T0 <: T) as Hsub. auto.
    eauto.
  - (* Sel-<: *)
    intros. inversion HeqTop.
  - (* Typ-<:-Typ *)
    intros. inversion HeqTop.
  - (* All-<:-All *)
    inversion HeqTop.
Qed.

Lemma subtyp_p_trans : forall G S T U,
    inert G ->
    G ⊢! S <: T ->
    G ⊢! T <: U ->
    G ⊢! S <: U.
Proof.
  intros G S T U H0 H H1. generalize dependent U.
  induction H.
  - (* Top *)
    intros. apply destruct_top_sub_T_p; auto.
  - (* Bot *) intros. eauto.
  - (* Refl *) intros. eauto.
  - (* And1-<: *) intros. specialize (IHsubtyp_p H0). apply IHsubtyp_p in H1. eauto.
  - (* And2-<: *) intros. specialize (IHsubtyp_p H0). apply IHsubtyp_p in H1. eauto.
  - (* <:-And *) intros. apply destruct_sub_p_and in H2.
    specialize (IHsubtyp_p1 H0).
    specialize (IHsubtyp_p2 H0).
    destruct H2 as [H2 | [H2 | H2]].
    { apply IHsubtyp_p1 in H2. auto.
    }
    { apply IHsubtyp_p2 in H2. auto.
    }
    { subst U0. auto.
    }
  - (* Fld-<:-Fld *) intros.
    assert (fld_intersection_sub_ok G (typ_rcd (dec_trm a U)) U0) as Hf.
    { apply destruct_fld_sub_p_fiso. auto. auto. }
    specialize (IHsubtyp_p H0).
    assert (fld_intersection_sub_ok G (typ_rcd (dec_trm a T)) U0) as Hf1.
    { eapply fld_sub_p_trans_fiso. auto. apply IHsubtyp_p. auto. }
    apply fiso_to_sub. auto. auto.
  - (* <:-Sel *) intros.
    specialize (IHsubtyp_p H0).
    assert (G ⊢! T <: U0) as Hsub.
      eapply destruct_sel_sub_p2. apply H0. apply H. apply H2.
    apply IHsubtyp_p in Hsub. auto.
  - (* Sel-<: *)
    intros. specialize (IHsubtyp_p H0).
    eauto.
  - (* Typ-<:-Typ *)
    intros. admit.
  - intros. admit.
Admitted.

Lemma tight_to_prec_sub_typ__l : forall G0,
    inert G0 ->
    (forall A S T U,
        G0 ⊢# typ_rcd (dec_typ A S T) <: U ->
        G0 ⊢! typ_rcd (dec_typ A S T) <: U).
Proof.
  intros.
  remember (typ_rcd (dec_typ A S T)) as Obj in H0.
  induction H0.
  - auto.
  - rewrite <- HeqObj. auto.
  - subst T0. auto.
  - specialize (IHsubtyp_t1 H HeqObj).
Admitted.

Lemma tight_to_prec_sub_typ: forall G0,
    inert G0 ->
    (forall S T A S1 T1 S2 T2,
        G0 ⊢# S <: T ->
        S = typ_rcd (dec_typ A S1 T1) ->
        T = typ_rcd (dec_typ A S2 T2) ->
        G0 ⊢! S <: T).
Proof.
  intros.
  generalize dependent A.
  generalize dependent S1.
  generalize dependent S2.
  generalize dependent T1.
  generalize dependent T2.
  induction H0.
  - intros. inversion H2.
  - intros. inversion H1.
  - intros. auto.
  - intros.
    specialize (IHsubtyp_t1 H). specialize (IHsubtyp_t2 H).
Admitted.

