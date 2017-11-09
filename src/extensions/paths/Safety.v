Set Implicit Arguments.

Require Import LibLN.
Require Import Coq.Program.Equality.
Require Import Binding CanonicalForms Definitions GeneralToTight InvertibleTyping Narrowing
            OperationalSemantics PreciseTyping RecordAndInertTypes Substitution Weakening.

(** The typing of a term with a stack *)
Inductive sta_trm_typ : sta * trm -> typ -> Prop :=
| sta_trm_typ_c : forall G s t T,
    inert G ->
    well_typed G s ->
    G ⊢ t : T ->
    sta_trm_typ (s, t) T.

Hint Constructors sta_trm_typ.

Notation "'⊢' t ':' T" := (sta_trm_typ t T) (at level 40, t at level 59).

(** * Preservation *)

(** If a value [v] has type [T], then [v] has a precise type [T']
    that is a subtype of [T].
    This lemma corresponds to Lemma 3.15 in the paper. *)
Lemma val_typing: forall G v T,
  G ⊢ trm_val v : T ->
  exists T', G ⊢! trm_val v : T' /\
        G ⊢ T' <: T.
Proof.
  intros G v T H. dependent induction H; eauto.
  destruct (IHty_trm _ eq_refl). destruct_all. eauto.
Qed.

(** Helper tactics for proving Preservation *)

Ltac lookup_eq :=
  match goal with
  | [Hl1: ?s ∋ ?t1,
     Hl2: ?s ∋ ?t2 |- _] =>
     apply (lookup_func_s Hl1) in Hl2; inversions Hl2
  end.

Ltac invert_red :=
  match goal with
  | [Hr: (_, _) |-> (_, _) |- _] => inversions Hr
  end.

Ltac solve_IH :=
  match goal with
  | [IH: well_typed _ _ ->
         inert _ ->
         forall t', (_, _) |-> (_, _) -> _,
       Wt: well_typed _ _,
       In: inert _,
       Hr: (_, _) |-> (_, ?t') |- _] =>
    specialize (IH Wt In t' Hr); destruct_all
  end;
  match goal with
  | [Hi: _ & ?G' ⊢ _ : _ |- _] =>
    exists G'; repeat split; auto
  end.

Ltac solve_let :=
  invert_red; solve_IH; fresh_constructor; eauto; apply* weaken_rules.

(** [s: G]                  #<br>#
    [inert [G]              #<br>#
    [(s, t) |-> (s', t')]   #<br>#
    [G ⊢ t: T]              #<br>#
    [―――――――――――――――――――]   #<br>#
    [exists G', inert G']        #<br>#
    [s': G, G']             #<br>#
    [G, G' ⊢ t': T]         *)
Lemma preservation_helper: forall G s t s' t' T,
    well_typed G s ->
    inert G ->
    (s, t) |-> (s', t') ->
    G ⊢ t : T ->
    exists G', inert G' /\
          well_typed (G & G') s' /\
          G & G' ⊢ t' : T.
Proof.
  introv Hwt Hin Hred Ht. gen t'.
  induction Ht; intros; try solve [invert_red].
  - Case "ty_all_elim".
    match goal with
    | [Hp: _ ⊢ trm_path _ : typ_all _ _ |- _] =>
        pose proof (canonical_forms_fun Hin Hwt Hp) as [L [T' [t [Bis [Hsub Hty]]]]];
          inversions Hred
    end.
    lookup_eq.
    exists (@empty typ). rewrite concat_empty_r. repeat split; auto.
    pick_fresh y. assert (y \notin L) as FrL by auto. specialize (Hty y FrL).
    eapply renaming_typ_open; eauto.
  - Case "ty_let".
    inversions Hred.
    * SCase "red_let_val".
      destruct (val_typing Ht) as [T' [Hv Hs]].
      lets Hp: (precise_inert_typ Hv).
      lets Hn: (well_typed_notin_dom Hwt H2).
      exists (x ~ T'). repeat split.
      + rewrite* <- concat_empty_l.
      + apply well_typed_push; auto. apply* precise_to_general.
      + pick_fresh y. assert (y \notin L) as Hy by auto. specialize (H y Hy).
        apply* renaming_typ. apply* narrow_typing.
    * SCase "red_let_path".


      match goal with
      | [IH: well_typed _ _ ->
             inert _ ->
             forall t', (_, _) |-> (_, _) -> _,
           Wt: well_typed _ _,
           In: inert _,
           Hr: (_, _) |-> (_, ?t') |- _] =>
        specialize (IH Wt In t' Hr); destruct_all
      end;
        match goal with
        | [Hi: _ & ?G' ⊢ _ : _ |- _] =>
          exists G'; repeat split; auto
        end.
  - Case "ty_new_elim".
    pose proof (canonical_forms_obj Hin Hwt Ht) as [S [ds [t [Bis [Has Ty]]]]].
    invert_red. binds_eq.
    exists (@empty typ). rewrite concat_empty_r. repeat split; auto.
    match goal with
    | [Hd: defs_has _ (def_trm _ ?t') |- G ⊢ t': T] =>
      rewrite* <- (defs_has_inv Has Hd)
    end.
  - Case "ty_let".
    destruct t; try solve [solve_let].
    + SCase "[t = (let x = a in u)] where a is a variable".
      repeat invert_red.
      exists (@empty typ). rewrite concat_empty_r. repeat split; auto.
      apply* renaming_fresh.
    + SCase "[t = (let x = v in u)] where v is a value".
      repeat invert_red.
      match goal with
        | [Hn: ?x # ?s |- _] =>
          pose proof (well_typed_notin_dom Hwf Hn) as Hng
      end.
      pose proof (val_typing Ht) as [V [Hv Hs]].
      exists (x ~ V). repeat split.
      ** rewrite <- concat_empty_l. constructor~. apply (precise_inert_typ Hv).
      ** constructor~. apply (precise_to_general Hv).
      ** eapply renaming_fresh with (L:=L \u dom G \u \{x}). apply* ok_push.
         intros. apply* weaken_rules. apply ty_sub with (T:=V); auto. apply* weaken_subtyp.
  - Case "ty_sub".
    solve_IH.
    match goal with
    | [Hs: _ ⊢ _ <: _,
       Hg: _ & ?G' ⊢ _: _ |- _] =>
      apply weaken_subtyp with (G2:=G') in Hs;
      eauto
    end.
Qed.

(** ** Preservation Theorem *)

(** [⊢ (s, t): T]           #<br>#
    [(s, t) |-> (s', t')]   #<br>#
    [―――――――――――――――――――]   #<br>#
    [⊢ (s', t'): T]         *)
Theorem preservation : forall s s' t t' T,
    ⊢ (s, t) : T ->
    (s, t) |-> (s', t') ->
    ⊢ (s', t') : T.
Proof.
  introv Ht Hr. destruct Ht as [* Hi Hwf Ht].
  lets Hp: (preservation_helper Hwf Hi Hr Ht). destruct Hp as [G' [Hi' [Hwf' Ht']]].
  apply sta_trm_typ_c with (G:=G & G'); auto. apply* inert_concat.
Qed.

(** * Progress *)

(** Helper tactic for proving progress *)
Ltac solve_let_prog :=
  match goal with
      | [IH: ⊢ (?s, ?t) : ?T ->
             inert _ ->
             well_typed _ _ -> _,
         Hi: inert _,
         Hwt: well_typed _ _ |- _] =>
        assert (⊢ (s, t): T) as Hs by eauto;
        specialize (IH Hs Hi Hwt) as [IH | [s' [t' Hr]]];
        eauto; inversion IH
      end.

(** ** Progress Theorem *)

(** [⊢ (s, t): T]           #<br>#
    [(s, t) |-> (s', t')]   #<br>#
    [―――――――――――――――――――]   #<br>#
    [t] is in normal form   #<br>#
    or [exists s', t'] such that [(s, t) |-> (s', t')] *)
Theorem progress: forall s t T,
    ⊢ (s, t) : T ->
    norm_form t \/ exists s' t', (s, t) |-> (s', t').
Proof.
  introv Ht. inversion Ht as [G s' t' T' Hi Hwt HT]. subst.
  induction HT; eauto.
  - Case "ty_all_elim".
    pose proof (canonical_forms_fun Hi Hwt HT1). destruct_all. right*.
  - Case "ty_new_elim".
    pose proof (canonical_forms_obj Hi Hwt HT). destruct_all. right*.
  - Case "ty_let".
    right. destruct t; try solve [solve_let_prog].
    + pose proof (var_typing_implies_avar_f HT) as [x A]. subst*.
    + pick_fresh x. exists (s & x ~ v) (open_trm x u). auto.
Qed.
