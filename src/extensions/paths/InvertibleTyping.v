(** printing |-#    %\vdash_{\#}%    #&vdash;<sub>&#35;</sub>#     *)
(** printing |-##   %\vdash_{\#\#}%  #&vdash;<sub>&#35&#35</sub>#  *)
(** printing |-##v  %\vdash_{\#\#v}% #&vdash;<sub>&#35&#35v</sub># *)
(** printing |-!    %\vdash_!%       #&vdash;<sub>!</sub>#         *)
(** remove printing ~ *)

(** This module contains lemmas related to invertible typing
    ([ty_var_inv], [|-##] and [ty_val_inv], [|-##v]). *)

Set Implicit Arguments.

Require Import Coq.Program.Equality.
Require Import LibLN.
Require Import Sequences.
Require Import Definitions Binding Narrowing PreciseTyping RecordAndInertTypes Replacement
               Subenvironments TightTyping Weakening.

(** ** Invertible typing *)

(** The invertible-typing relation describes the possible types that a variable or value
can be typed with in an inert context. For example, if [G] is inert, [G ⊢! x: {a: T}],
and [G ⊢ T <: T'], then [G ⊢## x: {a: T'}].

The purpose of invertible typing is to be easily invertible into a precise typing relation.
To achieve that, invertible typing avoids typing cycles that could result from, for example,
repeated applications of recursion introduction and elimination.
For this case, invertible typing defines only recursion introduction (whereas precise typing
defines only recursion elimination). *)

(** ** Invertible typing of paths [G ⊢## p: T] *)

Reserved Notation "G '⊢##' p ':' T" (at level 40, p at level 59).

Inductive ty_path_inv : ctx -> path -> typ -> Prop :=

(** [G ⊢• p: qs ⪼ T]  #<br>#
    [―――――――――――――――] #<br>#
    [G ⊢## p: T]     *)
| ty_precise_inv : forall G p U T m,
  G ⊢! p : U ⪼ T // m ->
  G ⊢## p : T

(** [G ⊢## p: {a: T}] #<br>#
    [G ⊢# T <: U]     #<br>#
    [――――――――――――――――] #<br>#
    [G ⊢## p: {a: U}]     *)
| ty_dec_trm_inv : forall G p a T U,
  G ⊢## p : typ_rcd {a ⦂ T} ->
  G ⊢# T <: U ->
  G ⊢## p : typ_rcd {a ⦂ U}

(** [G ⊢## p: {A: T1..S1}]   #<br>#
    [G ⊢# T2 <: T1]         #<br>#
    [G ⊢# S1 <: S2]         #<br>#
    [―――――――――――――――――――――] #<br>#
    [G ⊢## p: {A: T2..S2}]     *)
| ty_dec_typ_inv : forall G p A T1 T2 S1 S2,
  G ⊢## p : typ_rcd {A >: T1 <: S1} ->
  G ⊢# T2 <: T1 ->
  G ⊢# S1 <: S2 ->
  G ⊢## p : typ_rcd {A >: T2 <: S2}

(** [G ⊢## p: T^p]   #<br>#
    [―――――――――――――――] #<br>#
    [G ⊢## p: mu(T)] *)
| ty_bnd_inv : forall G p T,
  G ⊢## p : open_typ_p p T ->
  G ⊢## p : typ_bnd T

(** [G ⊢## p: forall(S1)T1]          #<br>#
    [G ⊢# S2 <: S1]            #<br>#
    [G, y: S2 ⊢ T1^y <: T2^y]   #<br>#
    [y fresh]                  #<br>#
    [――――――――――――――――――――――]   #<br>#
    [G ⊢## p: forall(S')T']            *)
| ty_all_inv : forall G T1 T2 S1 S2 L p,
  G ⊢## p : typ_all S1 T1 ->
  G ⊢# S2 <: S1 ->
  (forall y, y \notin L ->
   G & y ~ S2 ⊢ open_typ y T1 <: open_typ y T2) ->
  G ⊢## p : typ_all S2 T2

(** [G ⊢## p : T]     #<br>#
    [G ⊢## p : U]     #<br>#
    [――――――――――――――――] #<br>#
    [G ⊢## p : T /\ U]      *)
| ty_and_inv : forall G p S1 S2,
  G ⊢## p : S1 ->
  G ⊢## p : S2 ->
  G ⊢## p : typ_and S1 S2

(** [G ⊢## p: S]        #<br>#
    [G ⊢! q: {A: S..S}] #<br>#
    [――――――――――――――――――] #<br>#
    [G ⊢## p: q.A           *)
| ty_sel_inv : forall G p q A S T m,
  G ⊢## p : S ->
  G ⊢! q : T ⪼ typ_rcd {A >: S <: S} // m ->
  G ⊢## p : typ_path q A

(** [G ⊢## p: T]   #<br>#
    [―――――――――――――] #<br>#
    [G ⊢## p: top]     *)
| ty_top_inv : forall G p T,
  G ⊢## p : T ->
  G ⊢## p : typ_top

(* replacement rules: recursive types, selection types, singleton types *)

| ty_rec_qp_inv : forall G p q r T T',
    G ⊢# trm_path p : typ_sngl q ->
    G ⊢## r : typ_bnd T ->
    repl_typ q p T T' ->
    G ⊢## r : typ_bnd T'

| ty_sel_qp_inv : forall G p q r r' r'' A,
    G ⊢# trm_path p : typ_sngl q ->
    G ⊢## r : typ_path r' A ->
    repl_typ q p (typ_path r' A) (typ_path r'' A) ->
    G ⊢## r : typ_path r'' A

| ty_sngl_qp_inv : forall G p q r r' r'',
    G ⊢# trm_path p : typ_sngl q ->
    G ⊢## r : typ_sngl r' ->
    repl_typ q p (typ_sngl r') (typ_sngl r'') ->
    G ⊢## r : typ_sngl r''

where "G '⊢##' p ':' T" := (ty_path_inv G p T).

Hint Constructors ty_path_inv.

(** *** Invertible to Precise Typing [|-## to |-!] *)

(** Invertible typing implies tight typing. *)
Lemma inv_to_tight: forall G p T,
    G ⊢## p: T ->
    G ⊢# trm_path p: T.
Proof.
  introv Ht. induction Ht; eauto.
  apply* precise_to_tight.
Qed.

(** Invertible-to-precise typing for field declarations: #<br>#
    [G |-## p: {a: T}]            #<br>#
    [――――――――――――――――――――――]      #<br>#
    [exists T', G |-! p: {a: T'}]      #<br>#
    [G |-# T' <: T]. *)
Lemma invertible_to_precise_trm_dec: forall G p a T,
  inert G ->
  G ⊢## p : typ_rcd {a ⦂ T} ->
  exists U T' m,
    G ⊢! p: U ⪼ typ_rcd {a ⦂ T'} // m /\
    G ⊢# T' <: T.
Proof.
  introv Hi Hinv.
  dependent induction Hinv.
  - repeat eexists; eauto.
  - specialize (IHHinv _ _ Hi eq_refl). destruct IHHinv as [U [T' [m' [Hp Hs]]]]. repeat eexists; eauto.
Qed.

(** Invertible-to-precise typing for function types: #<br>#
    [ok G]                        #<br>#
    [G ⊢## x: forall(S)T]             #<br>#
    [――――――――――――――――――――――――――]  #<br>#
    [exists S', T'. G ⊢! x: forall(S')T']  #<br>#
    [G ⊢# S <: S']               #<br>#
    [G ⊢# T'^y <: T^y], where [y] is fresh. *)
Lemma invertible_to_precise_typ_all: forall G p S T,
  inert G ->
  G ⊢## p : typ_all S T ->
  exists U m S' T' L,
    G ⊢! p : U ⪼ typ_all S' T' // m /\
    G ⊢# S <: S' /\
    (forall y,
        y \notin L ->
            G & y ~ S ⊢ open_typ y T' <: open_typ y T).
Proof.
  introv Hi Hinv.
  dependent induction Hinv.
  - exists U m S T (dom G); eauto.
  - specialize (IHHinv _ _ Hi eq_refl). destruct IHHinv as [U [m' [S' [T' [L' [Hp [Hs1 Hs]]]]]]].
    exists U m' S' T' (L \u L'). repeat split; auto. eauto. (* renaming *) admit.
Qed.

(** ** Invertible Replacement Closure *)

Ltac invert_repl :=
  repeat match goal with
         | [H: repl_dec _ _ {_ ⦂ _} _ |- _ ] =>
           inversions H
         | [H: repl_dec _ _ _ {_ ⦂ _} |- _ ] =>
           inversions H
         | [H: repl_dec _ _ {_ >: _ <: _} _ |- _ ] =>
           inversions H
         | [H: repl_dec _ _ _ {_ >: _ <: _} |- _ ] =>
           inversions H
         | [H: repl_typ _ _ (typ_rcd _) _ |- _ ] =>
           inversions H
         | [H: repl_typ _ _ _ (typ_rcd _) |- _ ] =>
           inversions H
         | [H: repl_typ _ _ (typ_and _ _) _ |- _ ] =>
           inversions H
         | [H: repl_typ _ _ _ (typ_and _ _) |- _ ] =>
           inversions H
         | [H: repl_typ _ _ (typ_bnd _) _ |- _ ] =>
           inversions H
         | [H: repl_typ _ _ _ (typ_bnd _) |- _ ] =>
           inversions H
         | [H: repl_typ _ _ (typ_all _ _) _ |- _ ] =>
           inversions H
         | [H: repl_typ _ _ _ (typ_all _ _) |- _ ] =>
           inversions H
         | [H: repl_typ _ _ (typ_path _ _) _ |- _ ] =>
           inversions H
         | [H: repl_typ _ _ _ (typ_path _ _) |- _ ] =>
           inversions H
         | [H: repl_typ _ _ typ_top _ |- _ ] =>
           inversions H
         | [H: repl_typ _ _ _ typ_top |- _ ] =>
           inversions H
         | [H: repl_typ _ _ typ_bot _ |- _ ] =>
           inversions H
         | [H: repl_typ _ _ _ typ_bot |- _ ] =>
           inversions H
         | [H: repl_typ _ _ (typ_sngl _) _ |- _ ] =>
           inversions H
         | [H: repl_typ _ _ _ (typ_sngl _) |- _ ] =>
           inversions H
    end.

Lemma repl_sub: forall G p q T U,
    repl_typ p q T U ->
    G ⊢# trm_path p: typ_sngl q ->
    G ⊢# U <: T.
Proof.
  introv Hr Hpq. apply repl_swap in Hr. eauto.
Qed.

Lemma repl_sub_swap: forall G p q T U,
    repl_typ q p T U ->
    G ⊢# trm_path p: typ_sngl q ->
    G ⊢# U <: T.
Proof.
  introv Hr Hpq. apply repl_swap in Hr. eauto.
Qed.

Ltac solve_repl_sub :=
    try (apply* tight_to_general);
    try solve [apply* repl_sub];
    try solve [apply* repl_sub_swap];
    eauto.

Lemma invertible_repl_closure_helper :
  (forall D,
      record_dec D -> forall G p T m q r D',
      inert G ->
      G ⊢! p: T ⪼ typ_rcd D // m ->
      G ⊢# trm_path q : typ_sngl r ->
      repl_dec r q D D' ->
      G ⊢## p: typ_rcd D') /\
  (forall U ls,
      record_typ U ls -> forall G p T m q r U',
      inert G ->
      G ⊢! p: T ⪼ U // m ->
      G ⊢# trm_path q : typ_sngl r ->
      repl_typ r q U U' ->
      G ⊢## p: U') /\
  (forall U,
      inert_typ U -> forall G p T q r U' m,
      inert G ->
      G ⊢! p: T ⪼ U // m ->
      G ⊢# trm_path q : typ_sngl r ->
      repl_typ r q U U' ->
      G ⊢## p: U').
Proof.
  apply rcd_mutind; intros; try solve [invert_repl; eauto].
  - invert_repl; eapply ty_dec_typ_inv. eapply ty_precise_inv. apply H0.
    solve_repl_sub. eauto.
    eauto. eauto. solve_repl_sub.
  - invert_repl; eapply ty_and_inv. apply* H. apply* pf_and_destruct1.
    apply pf_and_destruct2 in H2; auto. eauto.
    apply pf_and_destruct1 in H2; auto. eauto.
    invert_repl. apply pf_and_destruct2 in H2; auto. eauto.
  - lets Hg: ((proj21 tight_to_general) _ _ _ H1).
    lets Hs: (sngl_path_named Hg). lets Ht: (typed_paths_named Hg).
    invert_repl; eapply ty_all_inv with (L:=dom G). eauto. apply repl_swap in H8. eauto.
    introv Hy.
    lets Ho: (repl_open_var y H8 Hs Ht). eauto.
    eauto. auto. introv Hy.
    lets Ho: (repl_open_var y H8 Hs Ht).
    apply* weaken_subtyp.
Qed.

Lemma invertible_repl_closure : forall G p q r T T',
    inert G ->
    G ⊢## p : T ->
    G ⊢# trm_path q : typ_sngl r ->
    repl_typ r q T T' ->
    G ⊢## p : T'.
Proof.
  introv Hi Hp Hqr Hrep. gen q r T'.
  induction Hp; introv Hq Hrep; invert_repl; eauto 4.
  - Case "ty_precise_inv".
    destruct (pf_inert Hi H) as [Hin | Hs].
    * inversions Hin.
      ** lets Heq: (pf_forall_U H). subst.
         apply* invertible_repl_closure_helper.
      ** destruct (pf_rec_rcd_U Hi H) as [Hp | Hp]; subst.
         + inversions Hrep. eauto.
         + inversions Hp.
           lets Hh: (proj32 invertible_repl_closure_helper).
           specialize (Hh _ _ H1). apply* Hh.
    * inversions Hs. lets Hs: (pf_sngl_U H). subst.
      inversions Hrep. eauto.
  - Case "ty_dec_typ_inv 1".
    eapply ty_dec_typ_inv.
    apply Hp; eapply subtyp_trans_t. apply repl_swap in H8. eauto. auto.
  - Case "ty_all_inv".
    eapply ty_all_inv with (L:=L \u dom G).
    * apply Hp.
    * apply repl_swap in H6. eauto.
    * introv Hy. eapply narrow_subtyping. apply H0. auto. constructor; auto.
      apply tight_to_general. solve_repl_sub.
  - eapply ty_all_inv with (L:=L \u dom G).
    * apply Hp.
    * auto.
    * lets Hg: ((proj21 tight_to_general) _ _ _ Hq). introv Hy. eapply subtyp_trans. apply* H0.
      eapply repl_open_var in H6. eapply subtyp_sngl_qp.
      apply* weaken_ty_trm. apply H6. apply* sngl_path_named. apply* typed_paths_named.
  - Case "ty_sel_inv".
    eauto 5.
  - Case "ty_sngl_qp_inv".
    eauto.
Qed.

Lemma invertible_repl_closure_comp: forall G p q r T T',
    inert G ->
    G ⊢## p: T ->
    G ⊢# trm_path q: typ_sngl r ->
    repl_composition r q T T' ->
    G ⊢## p: T'.
Proof.
  introv Hi Hp Hq Hc. gen p. dependent induction Hc; introv Hp; eauto.
  apply* IHHc. apply* invertible_repl_closure.
Qed.

Lemma invertible_bot : forall G p,
    inert G ->
    G ⊢## p: typ_bot -> False.
Proof.
  introv Hi Hp. dependent induction Hp; eauto. false* pf_bot.
Qed.

Lemma invertible_and : forall G p T U,
    inert G ->
    G ⊢## p: typ_and T U ->
    G ⊢## p: T /\ G ⊢## p: U.
Proof.
  introv Hi Hp. dependent induction Hp; auto.
  split. apply pf_and_destruct1 in H. eauto. apply pf_and_destruct2 in H. eauto. auto.
  apply pf_and_destruct2 in H; eauto.
Qed.

Lemma invertible_bnd : forall G p T,
    inert G ->
    G ⊢## p: typ_bnd T ->
    G ⊢## p: open_typ_p p T.
Proof.
  introv Hi Hp. dependent induction Hp; auto.
  - destruct m. apply pf_open in H. eauto.
    destruct (original_path_exists H) as [q Hor]. unfolds original_path.
    specialize (Hor H). destruct Hor as [Hq Hand].
    lets Hb: (pf_bnd_T Hi H). subst. apply pf_open in Hq. destruct Hand as [Heq | Hp'].
    * subst. eauto.
    * lets Ht: (pf_sngl_trans Hp' Hq).
      apply ty_precise_inv in Ht. apply precise_to_tight in Hp'. destruct Hp' as [Hp _].
      lets Hop: (repl_comp_open q p T). apply* invertible_repl_closure_comp.
  - lets Hg: ((proj21 tight_to_general) _ _ _ H).
    specialize (IHHp _ Hi eq_refl). apply* invertible_repl_closure. apply* repl_open.
    apply* sngl_path_named. apply* typed_paths_named.
Qed.

(** * Replacement typing
    Whereas invertible typing does replacment for singleton types in one direction,
    replacement typing does the replacment in the other direction.

    Note that we can't simply define this using three rules:
    1) identity from invertible typing
    2) two repl subtyping rules
    The reason is that if we did that, repl typing would necessarily apply the replacement
    in all subterms of a term, whereas we want to be able to say, for example:
    Г ⊢## p: T
    Г ⊢// p: U
    __________
    Г ⊢// p: T ∧ U
*)

Reserved Notation "G '⊢//' p ':' T" (at level 40, p at level 59).

Inductive ty_repl : ctx -> path -> typ -> Prop :=

| ty_inv_r : forall G p T,
    G ⊢## p: T ->
    G ⊢// p: T

| ty_and_r : forall G p T U,
    G ⊢// p: T ->
    G ⊢// p: U ->
    G ⊢// p: typ_and T U

| ty_bnd_r : forall G p T,
    G ⊢// p: open_typ_p p T ->
    G ⊢// p: typ_bnd T

| ty_rec_pq_r : forall G p q r T T',
    G ⊢# trm_path p : typ_sngl q ->
    G ⊢// r : typ_bnd T ->
    repl_typ p q T T' ->
    G ⊢// r : typ_bnd T'

| ty_sel_pq_r : forall G p q r r' r'' A,
    G ⊢# trm_path p : typ_sngl q ->
    G ⊢// r : typ_path r' A ->
    repl_typ p q (typ_path r' A) (typ_path r'' A) ->
    G ⊢// r : typ_path r'' A

| ty_sngl_pq_inv : forall G p q r r' r'',
    G ⊢# trm_path p : typ_sngl q ->
    G ⊢// r : typ_sngl r' ->
    repl_typ p q (typ_sngl r') (typ_sngl r'') ->
    G ⊢// r : typ_sngl r''

where "G '⊢//' p ':' T" := (ty_repl G p T).

Hint Constructors ty_repl.

Lemma repl_bot : forall G p,
    inert G ->
    G ⊢// p: typ_bot -> False.
Proof.
  introv Hi Hr. dependent induction Hr; invert_repl; eauto. false* invertible_bot.
Qed.

Lemma repl_to_tight : forall G p T,
    G ⊢// p : T ->
    G ⊢# trm_path p : T.
Proof.
  introv Hp. induction Hp; eauto. apply* inv_to_tight.
Qed.

Lemma repl_and: forall G p T U,
    inert G ->
    G ⊢// p: typ_and T U ->
    G ⊢// p: T /\ G ⊢// p: U.
Proof.
  introv Hi Hp. dependent induction Hp; eauto.
  destruct (invertible_and Hi H). split*.
Qed.

Lemma repl_to_invertible: forall G p U,
    inert G ->
    G ⊢// p: U ->
    exists T, repl_composition U T /\ G ⊢## p: T.
Admitted.

Lemma repl_rec_intro: forall G p T,
    inert G ->
    G ⊢// p: typ_bnd T ->
    G ⊢// p: open_typ_p p T.
Proof.
  introv Hi Hp. dependent induction Hp; auto.
  - Case "ty_inv_r".



  - Case "ty_and_r".
    destruct T; inversions x. unfolds open_typ_p.
    specialize (IHHp1 _ Hi eq_refl). specialize (IHHp2 _ Hi eq_refl).
    admit.
  - destruct T; inversions x.

  destruct (repl_to_invertible Hi Hp) as [U [Hr Hinv]].



Lemma replacement_repl_closure_qp : forall G p q r T T',
    inert G ->
    G ⊢# trm_path q : typ_sngl r ->
    G ⊢// p : T ->
    repl_typ r q T T' ->
    G ⊢// p : T'.
Proof.
  introv Hi Hq Hp. gen q r T'. induction Hp; introv Hq; introv Hr; invert_repl; eauto 5.
  - gen q r T'. induction H; introv Hq; introv Hr; try solve [invert_repl; eauto 5].
    * Case "ty_precise_inv".
      destruct (pf_inertsngl Hi H) as [Ht [[Hit | Hst] | [Hit Hst]]].
      + inversions Hit; invert_repl.
        ++ apply ty_inv_r. eapply ty_all_inv. apply* ty_precise_inv.
           apply repl_swap in H5.
           eapply subtyp_sngl_pq_t. apply Hq. auto. introv Hy. auto.
        ++ apply ty_inv_r. lets Hg: ((proj21 tight_to_general) _ _ _ Hq).
           eapply ty_all_inv. apply* ty_precise_inv.
           auto. introv Hy. eapply repl_open_var in H5.
           eapply subtyp_sngl_qp. apply* weaken_ty_trm.
           apply H5. apply* sngl_path_named. apply* typed_paths_named.
        ++ apply* ty_rec_qp_r.
      + inversions Hst. invert_repl. eauto.
      + admit. (* inverstion on record type and usual stuff *)
    * Case "ty_dec_typ_inv".
      invert_repl. eapply ty_inv_r. eapply ty_dec_typ_inv. apply  H.
      eapply subtyp_trans_t. apply repl_swap in H9. eapply subtyp_sngl_pq_t.
      apply Hq. apply H9. auto. auto. eauto.
    * Case "ty_all_inv".
      invert_repl; apply ty_inv_r; eapply ty_all_inv. apply H.
      admit. (* simple *)
      introv Hy. admit. (* narrowing *)
      apply H. auto. introv Hy. eapply subtyp_trans. apply* H1.
      eapply repl_open_var in H7; admit. (* simple *)
    * Case "ty_sel_pq_inv".
      inversions Hr. eauto.
    * Case "ty_sngl_pq_inv".
      inversions Hr. eauto.
Admitted. (* shelved stuff *)

Lemma replacement_repl_closure_pq : forall G p q r T T',
    inert G ->
    G ⊢// p : T ->
    G ⊢// q : typ_sngl r ->
    repl_typ q r T T' ->
    G ⊢// p : T'.
Proof.
  introv Hi Hp Hqr.
  gen q r T'. induction Hp; introv Hq; introv Hr; invert_repl; eauto 3.
  - Case "ty_inv_r".
    constructor. apply repl_to_tight in Hq. apply* invertible_repl_closure.
  - Case "ty_rec_qp_r".
Admitted.


Lemma replacement_closure :
  (forall G t T, G ⊢# t : T -> forall p,
            t = trm_path p ->
            inert G ->
            G ⊢// p: T) /\
  (forall G T U, G ⊢# T <: U -> forall p,
            G ⊢// p: T ->
            inert G ->
            G ⊢// p: U).
Proof.
  apply ts_mutind_ts; intros; subst; try solve [(inversions H || inversions H0 || inversions H1); eauto]; eauto.
  - Case "ty_new_elim_t".
    inversions H0. specialize (H _ eq_refl). admit.
  - Case "ty_sngl_t".
    inversions H1.
    specialize (H _ eq_refl H2). specialize (H0 _ eq_refl H2). admit.
  - Case "ty_rec_intro_t".
    inversions H0. specialize (H _ eq_refl H1). admit.
  - Case "ty_rec_elim_t".
    inversions H0. specialize (H _ eq_refl H1). admit.
  - Case "subtyp_top_t".
    induction H; eauto.
  - Case "subtyp_bot_t".
    false* repl_bot.
  - Case "subtyp_and_11_t".
    apply repl_and in H; destruct_all; auto.
  - Case "subtyp_and_22_t".
    apply repl_and in H; destruct_all; auto.
  - Case "subtyp_sngl_pq_t".
    apply* replacement_repl_closure_pq.
  - Case "subtyp_sngl_qp_t".
    apply* replacement_repl_closure_qp.
  - Case "subtyp_sel2_t".
    admit.
  - Case "subtyp_sel1_t".
    admit.
Qed.
