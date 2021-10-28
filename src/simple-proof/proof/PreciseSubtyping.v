(** printing ⊢#    %\vdash_{\#}%    #&vdash;<sub>&#35;</sub>#     *)
(** printing ⊢##   %\vdash_{\#\#}%  #&vdash;<sub>&#35&#35</sub>#  *)
(** printing ⊢##v  %\vdash_{\#\#v}% #&vdash;<sub>&#35&#35v</sub># *)
(** printing ⊢!    %\vdash_!%       #&vdash;<sub>!</sub>#         *)
(** remove printing ~ *)

(** This module reasons about the precise types of variables in inert contexts. *)

Set Implicit Arguments.

Require Import Coq.Program.Equality.
Require Import Definitions RecordAndInertTypes InvertibleTyping TightTyping PreciseTyping.
Require Import Subenvironments Narrowing.

Reserved Notation "G '⊢!' T '<:' U" (at level 40, T at level 59).
Reserved Notation "G '⊢&f' T '<:' U" (at level 40, T at level 59).
Reserved Notation "G '⊢&t' T '<:' U" (at level 40, T at level 59).
Reserved Notation "G '⊢&a' T '<:' U" (at level 40, T at level 59).

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
    G ⊢# S2 <: S1 ->
    G ⊢# T1 <: T2 ->
    G ⊢! typ_rcd (dec_typ A S1 T1) <: typ_rcd (dec_typ A S2 T2)

(** [G ⊢! S2 <: S1]                #<br>#
    [G, x: S2 ⊢ T1^x <: T2^x]       #<br>#
    [x fresh]                       #<br>#
    [――――――――――――――――――――――――]      #<br>#
    [G ⊢! forall(S1)T1 <: forall(S2)T2]          *)
| subtyp_all_p: forall L G S1 T1 S2 T2,
    G ⊢# S2 <: S1 ->
    (forall x, x \notin L ->
       G & x ~ S2 ⊢ open_typ x T1 <: open_typ x T2) ->
    G ⊢! typ_all S1 T1 <: typ_all S2 T2

where "G '⊢!' T '<:' U" := (subtyp_p G T U).

Hint Constructors subtyp_p.

Lemma destruct_subtyp_typ_p : forall G0,
    inert G0 ->
    (forall A S1 T1 S2 T2,
        G0 ⊢! typ_rcd (dec_typ A S1 T1) <: typ_rcd (dec_typ A S2 T2) ->
        (G0 ⊢# S2 <: S1 /\ G0 ⊢# T1 <: T2)).
Proof.
  intros G0 H0 A S1 T1 S2 T2 H.
  inversion H; subst; auto.
Qed.

Lemma destruct_subtyp_typ_p_label : forall G0,
    inert G0 ->
    (forall A B S1 T1 S2 T2,
        G0 ⊢! typ_rcd (dec_typ A S1 T1) <: typ_rcd (dec_typ B S2 T2) ->
        A = B).
Proof.
  intros G0 H0 A B S1 T1 S2 T2 H.
  remember (typ_rcd (dec_typ A S1 T1)) as Obj1 in H.
  remember (typ_rcd (dec_typ B S2 T2)) as Obj2 in H.
  rename HeqObj1 into Heq1.
  rename HeqObj2 into Heq2.
  induction H.
  - (* top *) inversion Heq2.
  - (* bot *) inversion Heq1.
  - (* refl *) subst T. inversion Heq2. trivial.
  - (* And1-<: *) inversion Heq1.
  - (* And2-<: *) inversion Heq1.
  - (* <:-And *) inversion Heq2.
  - (* Fld-<:-Fld *) inversion Heq1.
  - (* <:-Sel *) inversion Heq2.
  - (* Sel-<: *) inversion Heq1.
  - (* Typ-<:-Typ *) inversion Heq1. inversion Heq2. subst.
    trivial.
  - (* All-<:-All *) inversion Heq1.
Qed.

Lemma subtyp_sel_p_alias_deterministic : forall G0,
    inert G0 ->
    (forall x A U1 U2 T1 T2,
        G0 ⊢! x: U1 ⪼ typ_rcd (dec_typ A T1 T1) ->
        G0 ⊢! x: U2 ⪼ typ_rcd (dec_typ A T2 T2) ->
        T1 = T2).
Proof.
  intros G0 H0. intros x A U1 U2 T1 T2 H1 H2.
  assert (U1 = U2) as Hequ.
  {
    eapply x_bound_unique.
    apply H1.
    apply H2.
  }
  subst U1.
  eapply pf_inert_unique_tight_bounds.
    apply H0.
    apply H1.
    apply H2.
Qed.

(** Intersection Subtyping for Fields *)

Inductive subtyp_intf (G : ctx) (sub : typ) : typ -> Prop :=

| subtyp_top_intf : G ⊢&f sub <: typ_top

| subtyp_fld_intf : forall a T,
  G ⊢! sub <: typ_rcd (dec_trm a T) ->
  G ⊢&f sub <: typ_rcd (dec_trm a T)

| subtyp_sel_intf : forall x A U T,
  G ⊢! x: U ⪼ typ_rcd (dec_typ A T T) ->
  G ⊢! sub <: T ->
  G ⊢&f sub <: T ->
  G ⊢&f sub <: typ_sel (avar_f x) A

| subtyp_and_intf : forall T1 T2,
  G ⊢&f sub <: T1 ->
  G ⊢&f sub <: T2 ->
  G ⊢&f sub <: typ_and T1 T2

where "G '⊢&f' T '<:' U" := (subtyp_intf G T U).


Hint Constructors subtyp_intf.


Lemma intf_to_prec : forall G0,
    inert G0 ->
    (forall sub T,
        G0 ⊢&f sub <: T ->
        G0 ⊢! sub <: T).
Proof.
  intros G0 H0 sub T H.
  induction H.
  - (* top *) auto.
  - (* fld *) auto.
  - (* sub *)
    eauto.
  - (* and *) auto.
Qed.

Lemma prec_to_intf: forall G0,
    inert G0 ->
    (forall a T U,
        G0 ⊢! typ_rcd (dec_trm a T) <: U ->
        G0 ⊢&f typ_rcd (dec_trm a T) <: U).
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


Lemma trans_intf : forall G0,
    inert G0 ->
    (forall a S T U,
        (forall U1, G0 ⊢! T <: U1 -> G0 ⊢! S <: U1) ->
        G0 ⊢&f typ_rcd (dec_trm a T) <: U ->
        G0 ⊢&f typ_rcd (dec_trm a S) <: U).
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
      apply intf_to_prec. auto. auto.
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
      eapply subtyp_sel_p_alias_deterministic.
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
Proof.
  intros G0 H0 x A U T S H1 H2.
  remember (typ_sel (avar_f x) A) as Sel1 in H2.
  rename HeqSel1 into Heq.
  induction H2; eauto; try inversion Heq; eauto.
  - subst. clear Heq.
    specialize (IHsubtyp_p H0 H1).
    assert (T = T0) as Heq.
    {
      eapply subtyp_sel_p_alias_deterministic. apply H0.
      apply H1. apply H.
    }
    subst T0. auto.
Qed.

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


Inductive subtyp_intt (G : ctx) (sub : typ) : typ -> Prop :=

| subtyp_top_intt : G ⊢&t sub <: typ_top

| subtyp_typ_intt : forall A S T,
  G ⊢! sub <: typ_rcd (dec_typ A S T) ->
  G ⊢&t sub <: typ_rcd (dec_typ A S T)

| subtyp_sel_intt : forall x A U T,
  G ⊢! x: U ⪼ typ_rcd (dec_typ A T T) ->
  G ⊢! sub <: T ->
  G ⊢&t sub <: T ->
  G ⊢&t sub <: typ_sel (avar_f x) A

| subtyp_and_intt : forall T1 T2,
  G ⊢&t sub <: T1 ->
  G ⊢&t sub <: T2 ->
  G ⊢&t sub <: typ_and T1 T2

where "G '⊢&t' T '<:' U" := (subtyp_intt G T U).


Hint Constructors subtyp_intt.

Lemma intt_to_prec : forall G S T,
    G ⊢&t S <: T ->
    G ⊢! S <: T.
Proof.
  intros.
  induction H.
  - (* top *) auto.
  - (* typ *) auto.
  - (* sel *) eauto.
  - (* and *) auto.
Qed.

Lemma prec_to_intt : forall G0,
    inert G0 ->
    (forall A S T U,
        G0 ⊢! typ_rcd (dec_typ A S T) <: U ->
        G0 ⊢&t typ_rcd (dec_typ A S T) <: U).
Proof.
  intros G0 H0 A S T U Hp.
  remember (typ_rcd (dec_typ A S T)) as obj1 in Hp.
  rename Heqobj1 into Heq.
  induction Hp.
  - (* top *) auto.
  - (* bot *) inversion Heq.
  - (* refl *) subst T0. eauto.
  - (* And1-<: *) inversion Heq.
  - (* And2-<: *) inversion Heq.
  - (* <:-And *)
    specialize (IHHp1 H0 Heq).
    specialize (IHHp2 H0 Heq). eauto.
  - (* Fld-<:-Fld *) inversion Heq.
  - (* <:-Sel *) specialize (IHHp H0 Heq).
    subst S0. eauto.
  - (* Sel-<: *) inversion Heq.
  - (* Typ-<:-Typ *) inversion Heq. subst. eauto.
  - (* All-<:-All *) inversion Heq.
Qed.

Lemma trans_intt : forall G0,
    inert G0 ->
    (forall A S1 T1 S2 T2 U,
        G0 ⊢# S2 <: S1 ->
        G0 ⊢# T1 <: T2 ->
        G0 ⊢&t typ_rcd (dec_typ A S2 T2) <: U ->
        G0 ⊢&t typ_rcd (dec_typ A S1 T1) <: U).
Proof.
  intros G0 H0 A S1 T1 S2 T2 U Hs Ht Hi.
  induction Hi.
  - (* top *) auto.
  - (* typ *)
    assert (A = A0) as Heq.
    {
      eapply destruct_subtyp_typ_p_label. apply H0.
      apply H.
    }
    assert (G0 ⊢# S <: S2 /\ G0 ⊢# T2 <: T) as Hsub.
    {
      eapply destruct_subtyp_typ_p. apply H0.
      subst A0. apply H.
    }
    destruct Hsub as [Hs1 Hs2].
    assert (G0 ⊢! typ_rcd (dec_typ A S1 T1) <: typ_rcd (dec_typ A S2 T2)) as Hsub.
    { eauto. }
    subst A0. eauto.
  - (* sel *)
    assert (G0 ⊢! typ_rcd (dec_typ A S1 T1) <: T) as Hsub.
    { apply intt_to_prec. auto. }
    eauto.
  - (* and *)
    eauto.
Qed.


Inductive subtyp_inta (G : ctx) (sub : typ) : typ -> Prop :=

| subtyp_top_inta : G ⊢&a sub <: typ_top

| subtyp_all_inta : forall S T,
  G ⊢! sub <: typ_all S T ->
  G ⊢&a sub <: typ_all S T

| subtyp_sel_inta : forall x A U T,
  G ⊢! x: U ⪼ typ_rcd (dec_typ A T T) ->
  G ⊢! sub <: T ->
  G ⊢&a sub <: T ->
  G ⊢&a sub <: typ_sel (avar_f x) A

| subtyp_and_inta : forall T1 T2,
  G ⊢&a sub <: T1 ->
  G ⊢&a sub <: T2 ->
  G ⊢&a sub <: typ_and T1 T2

where "G '⊢&a' T '<:' U" := (subtyp_inta G T U).


Hint Constructors subtyp_inta.


Lemma inta_to_prec : forall G S T,
    G ⊢&a S <: T -> G ⊢! S <: T.
Proof.
  intros G S T H.
  induction H; auto; eauto.
Qed.


Lemma trans_subtyp_and_p : forall G0 S T U U1,
    inert G0 ->
    (forall U2, G0 ⊢! T <: U2 -> G0 ⊢! S <: U2) ->
    (forall U2, G0 ⊢! U <: U2 -> G0 ⊢! S <: U2) ->
    G0 ⊢! typ_and T U <: U1 ->
    G0 ⊢! S <: U1.
Proof.
  intros G0 S T U U1 H0 Ht Hu H.
  remember (typ_and T U) as And1 in H.
  rename HeqAnd1 into Heq.
  induction H.
  - (* top *)
    auto.
  - (* bot *)
    inversion Heq.
  - (* refl *)
    subst T0.
    eauto.
  - (* and11 *)
    inversion Heq; subst. auto.
  - (* and12 *)
    inversion Heq; subst. auto.
  - (* and2 *)
    eauto.
  - (* fld *)
    inversion Heq.
  - (* sel1 *)
    eauto.
  - (* sel2 *)
    inversion Heq.
  - (* typ *)
    inversion Heq.
  - (* all *)
    inversion Heq.
Qed.


Lemma inert_to_ok : forall G,
    inert G -> ok G.
Proof.
  intros G H0.
  induction H0; eauto.
Qed.


Lemma trans_subtyp_all_p: forall L G S1 S2 T1 T2 U,
    inert G ->
    G ⊢# S2 <: S1 ->
    (forall x : var,
        x \notin L -> G & x ~ S2 ⊢ open_typ x T1 <: open_typ x T2) ->
    G ⊢! typ_all S2 T2 <: U ->
    G ⊢! typ_all S1 T1 <: U.
Proof.
  intros L G S1 S2 T1 T2 U H0 Hs Ht H.
  remember (typ_all S2 T2) as Lam2 in H.
  rename HeqLam2 into Heq.
  induction H.
  - (* top *)
    auto.
  - (* bot *)
    inversion Heq.
  - (* refl *)
    subst T. eauto.
  - (* and11 *)
    inversion Heq.
  - (* and12 *)
    inversion Heq.
  - (* and2 *)
    specialize (IHsubtyp_p1 H0 Hs Ht Heq).
    specialize (IHsubtyp_p2 H0 Hs Ht Heq).
    eauto.
  - (* fld *)
    inversion Heq.
  - (* sel2 *)
    specialize (IHsubtyp_p H0 Hs Ht Heq).
    eauto.
  - (* sel1 *)
    inversion Heq.
  - (* typ *)
    inversion Heq.
  - (* all *)
    inversion Heq.
    subst. clear Heq.

    assert (forall x : var,
               x \notin (L \u L0 \u dom G) -> G & x ~ S3 ⊢ open_typ x T1 <: open_typ x T3) as Ht0.
    {
      intros x Hni.
      apply notin_union in Hni.
      destruct Hni as [Hn1 Hn2].
      apply notin_union in Hn2.
      destruct Hn2 as [Hn2 Hn3].
      specialize (Ht x Hn1) as Ht1.
      specialize (H1 x Hn2) as Ht2. clear Ht H1 Hn1 Hn2.
      destruct tight_to_general as [_ Pt].
      apply Pt in H.
      assert (G & x ~ S3 ⪯ G & x ~ S2) as Hsubenv.
      { eapply subenv_grow. auto. auto. auto. }
      eapply subtyp_trans.
      - eapply narrow_subtyping. apply Ht1. apply Hsubenv.
      - apply Ht2.
    }
    eauto.
Qed.

Lemma trans_subtyp_p : forall G S T U,
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
  - (* <:-And *) intros.
    specialize (IHsubtyp_p1 H0).
    specialize (IHsubtyp_p2 H0).

    eapply trans_subtyp_and_p.
      apply H0.
      apply IHsubtyp_p1.
      apply IHsubtyp_p2.
      apply H2.
  - (* Fld-<:-Fld *) intros.
    assert (G ⊢&f typ_rcd (dec_trm a U) <: U0) as Hf.
    { apply prec_to_intf. auto. auto. }
    specialize (IHsubtyp_p H0).
    assert (G ⊢&f typ_rcd (dec_trm a T) <: U0) as Hf1.
    { eapply trans_intf. auto. apply IHsubtyp_p. auto. }
    apply intf_to_prec. auto. auto.
  - (* <:-Sel *) intros.
    specialize (IHsubtyp_p H0).
    assert (G ⊢! T <: U0) as Hsub.
      eapply destruct_sel_sub_p2. apply H0. apply H. apply H2.
    apply IHsubtyp_p in Hsub. auto.
  - (* Sel-<: *)
    intros. specialize (IHsubtyp_p H0).
    eauto.
  - (* Typ-<:-Typ *)
    intros.
    assert (G ⊢&t typ_rcd (dec_typ A S2 T2) <: U) as Hit.
    { apply prec_to_intt. auto. auto. }
    assert (G ⊢&t typ_rcd (dec_typ A S1 T1) <: U) as Hit1.
    { eapply trans_intt. auto. apply H. apply H1. auto. }
    apply intt_to_prec. auto.
  - intros. eapply trans_subtyp_all_p.
    apply H0. apply H.
    apply H1. auto.
Qed.

Hint Resolve trans_subtyp_p.


Theorem prec_to_tight : forall G0,
    inert G0 ->
    (forall S T,
        G0 ⊢! S <: T ->
        G0 ⊢# S <: T).
Proof.
  intros G0 H0 S T H.
  induction H; auto; eauto.
Qed.

Theorem tight_to_prec : forall G0,
    inert G0 ->
    (forall S T,
        G0 ⊢# S <: T ->
        G0 ⊢! S <: T).
Proof.
  intros G0 H0 S T H.
  induction H; eauto.
Qed.

Hint Resolve destruct_subtyp_typ_p.
Hint Resolve prec_to_tight.
Hint Resolve tight_to_prec.


Theorem destruct_subtyp_typ_t : forall G0,
    inert G0 ->
    (forall A S1 T1 S2 T2,
        G0 ⊢# typ_rcd (dec_typ A S1 T1) <: typ_rcd (dec_typ A S2 T2) ->
        G0 ⊢# S2 <: S1 /\ G0 ⊢# T1 <: T2).
Proof.
  eauto.
Qed.

(** * Legacy *)

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
      eapply subtyp_sel_p_alias_deterministic.
        apply Hi.
        apply H.
        apply H4.
    subst T0.
    specialize (IHsubtyp_p H6). auto.
  - inversion HeqObj1.
  - intros T3 S3 Hsub.
    inversion HeqObj1. subst. clear HeqObj1.
    apply (destruct_subtyp_typ_p Hi) in Hsub. destruct Hsub as [H1 H2].
    assert (G ⊢ S3 <: S1) as Hb1.
      eauto.
    assert (G ⊢ T1 <: T3) as Hb2.
      eauto.
    eauto.
  - inversion HeqObj1.
Qed.
