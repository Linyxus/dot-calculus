Set Implicit Arguments.

Require Import LibLN.
Require Import Coq.Program.Equality.
Require Import Definitions.
Require Import Weakening.
Require Import Narrowing.
Require Import Helper_lemmas.
Require Import Precise_types.
Require Import Substitution.
Require Import Canonical_forms.
Require Import Safety.


(* TODO move to definitions *)
Definition close_rec_avar (k: nat) (u: var) (a: avar) : avar :=
  match a with
  | avar_b i => avar_b i
  | avar_f x => If x = u then avar_b k else avar_f x
  end.

Fixpoint close_rec_typ (k: nat) (u: var) (T: typ): typ :=
  match T with
  | typ_top        => typ_top
  | typ_bot        => typ_bot
  | typ_rcd D      => typ_rcd (close_rec_dec k u D)
  | typ_and T1 T2  => typ_and (close_rec_typ k u T1) (close_rec_typ k u T2)
  | typ_sel x L    => typ_sel (close_rec_avar k u x) L
  | typ_bnd T      => typ_bnd (close_rec_typ (S k) u T)
  | typ_all T1 T2  => typ_all (close_rec_typ k u T1) (close_rec_typ (S k) u T2)
  end
with close_rec_dec (k: nat) (u: var) (D: dec): dec :=
  match D with
  | dec_typ L T U => dec_typ L (close_rec_typ k u T) (close_rec_typ k u U)
  | dec_trm m T   => dec_trm m (close_rec_typ k u T)
  end.

Fixpoint close_rec_trm (k: nat) (u: var) (t: trm): trm :=
  match t with
  | trm_var a      => trm_var (close_rec_avar k u a)
  | trm_val v      => trm_val (close_rec_val k u v)
  | trm_sel v m    => trm_sel (close_rec_avar k u v) m
  | trm_app f a    => trm_app (close_rec_avar k u f) (close_rec_avar k u a)
  | trm_let t1 t2  => trm_let (close_rec_trm k u t1) (close_rec_trm (S k) u t2)
  end
with close_rec_val (k: nat) (u: var) (v: val): val :=
  match v with
  | val_new T ds   => val_new (close_rec_typ (S k) u T) (close_rec_defs (S k) u ds)
  | val_lambda T e => val_lambda (close_rec_typ k u T) (close_rec_trm (S k) u e)
  end
with close_rec_def (k: nat) (u: var) (d: def): def :=
  match d with
  | def_typ L T => def_typ L (close_rec_typ k u T)
  | def_trm m e => def_trm m (close_rec_trm k u e)
  end
with close_rec_defs (k: nat) (u: var) (ds: defs): defs :=
  match ds with
  | defs_nil       => defs_nil
  | defs_cons tl d => defs_cons (close_rec_defs k u tl) (close_rec_def k u d)
  end.

Definition close_avar u a := close_rec_avar  0 u a.
Definition close_typ  u t := close_rec_typ   0 u t.
Definition close_dec  u D := close_rec_dec   0 u D.
Definition close_trm  u e := close_rec_trm   0 u e.
Definition close_val  u v := close_rec_val   0 u v.
Definition close_def  u d := close_rec_def   0 u d.
Definition close_defs u l := close_rec_defs  0 u l.

(* Inductive lc_rec_avar : nat -> avar -> Prop := *)
(* | lc_avar_f : forall n x, lc_rec_avar n (avar_f x) *)
(* | lc_avar_b : forall n m, *)
(*     n > m -> *)
(*     lc_rec_avar n (avar_b m). *)

(* Definition lc_var' := lc_rec_avar 0. *)

(* Lemma test: forall x, *)
(*     lc_var x <-> lc_var' x. *)
(* Proof. *)
(*   intros. split; intros. *)
(*   - inversions H. constructor. *)
(*   - inversions H. *)
(*     + constructor. *)
(*     + inversions H0. *)
(* Qed. *)

Fixpoint ec_trm_helper (e: ec) (s: sto) (t: trm) : trm :=
  match s with
  | nil => match e with
          | e_hole _ => t
          | e_term _ u => trm_let t u
          end
  | cons (x, v) s => trm_let (trm_val v) (close_trm x (ec_trm_helper e s t))
  end.

Fixpoint ec_trm (e: ec) (t: trm): trm := ec_trm_helper e (ec_sto e) t.

Inductive ec_trm' : ec -> trm -> trm -> Prop :=
| ec_trm_empty_hole : forall t,
    ec_trm' (e_hole empty) t t
| ec_trm_empty_term : forall t u,
    ec_trm' (e_term empty u) t (trm_let t u)
| ec_trm_sto_hole : forall x v s t t',
    x \notin (fv_trm t') ->
    ec_trm' (e_hole s) t (open_trm x t') ->
    ec_trm' (e_hole (s & x ~ v)) t (trm_let (trm_val v) t')
| ec_trm_sto_term: forall x v s t t' u,
    x \notin (fv_trm t') ->
    ec_trm' (e_term s u) t (open_trm x t') ->
    ec_trm' (e_term (s & x ~ v) u) t (trm_let (trm_val v) t').

Fixpoint ec_vars (e: ec) := from_list (keys (ec_sto e)).

Fixpoint max_ec (t': trm) : ec * trm :=
  match t' with
  | trm_let (trm_val v) u =>
    match max_ec u with
    | ((e_hole s), t) =>
      let x := (var_gen (fv_ec (e_hole s))) in
      ((e_hole (s & x ~ v)), (open_trm x t))
    | ((e_term s u), t) =>
      let x := (var_gen (fv_ec (e_term s u))) in
      ((e_term (s & x ~ v) u), (open_trm x t))
    end
  | trm_let t u => ((e_term nil u), t)
  | t => ((e_hole nil), t)
  end.

(* Coq doesn't accept this *)
(* Fixpoint max_ec' (t' : trm) : ec * trm := *)
(*   match t' with *)
(*   | trm_let (trm_val v) u => *)
(*     let x := (var_gen (fv_trm t')) in *)
(*     match max_ec' (open_trm x u) with *)
(*     | (e_hole s, t)    => (e_hole (s & x ~ v),    t) *)
(*     | (e_term s u', t) => (e_term (s & x ~ v) u', t) *)
(*     end *)
(*   | trm_let t u => (e_term empty u, t) *)
(*   | t => (e_hole empty, t) *)
(*   end. *)

Inductive max_ec': trm -> ec -> trm -> Prop :=
| max_ec_var : forall x,
    max_ec' (trm_var x) (e_hole empty) (trm_var x)
| max_ec_val : forall v,
    max_ec' (trm_val v) (e_hole empty) (trm_val v)
| max_ec_sel : forall x a,
    max_ec' (trm_sel x a) (e_hole empty) (trm_sel x a)
| max_ec_app : forall x y,
    max_ec' (trm_app x y) (e_hole empty) (trm_app x y)
| max_ec_let_var : forall x t,
    max_ec' (trm_let (trm_var x) t) (e_term empty t) (trm_var x)
| max_ec_let_sel : forall x a t,
    max_ec' (trm_let (trm_sel x a) t) (e_term empty t) (trm_sel x a)
| max_ec_let_app : forall x y t,
    max_ec' (trm_let (trm_app x y) t) (e_term empty t) (trm_app x y)
| max_ec_let_let : forall t' u' t,
    max_ec' (trm_let (trm_let t' u') t) (e_term empty t) (trm_let t' u')
| max_ec_let_val_hole : forall u s t v x,
    x \notin ((dom s) \u (fv_trm u) \u (fv_trm t) \u (fv_val v)) ->
    max_ec' (open_trm x u) (e_hole s) t ->
    max_ec' (trm_let (trm_val v) u) (e_hole (s & x ~ v)) t
| max_ec_let_val_term : forall u s u' t v x,
    x \notin ((dom s) \u (fv_trm u) \u (fv_trm u') \u (fv_trm t) \u (fv_val v)) ->
    max_ec' (open_trm x u) (e_term s u') t ->
    max_ec' (trm_let (trm_val v) u) (e_term (s & x ~ v) u') t.

(* Inductive max_ec': trm -> ec -> trm -> Prop := *)
(* | max_ec_var : forall x, *)
(*     max_ec' (trm_var x) (e_hole empty) (trm_var x) *)
(* | max_ec_val : forall v, *)
(*     max_ec' (trm_val v) (e_hole empty) (trm_val v) *)
(* | max_ec_sel : forall x a, *)
(*     max_ec' (trm_sel x a) (e_hole empty) (trm_sel x a) *)
(* | max_ec_app : forall x y, *)
(*     max_ec' (trm_app x y) (e_hole empty) (trm_app x y) *)
(* | max_ec_let_var : forall x t, *)
(*     max_ec' (trm_let (trm_var x) t) (e_term empty t) (trm_var x) *)
(* | max_ec_let_sel : forall x a t, *)
(*     max_ec' (trm_let (trm_sel x a) t) (e_term empty t) (trm_sel x a) *)
(* | max_ec_let_app : forall x y t, *)
(*     max_ec' (trm_let (trm_app x y) t) (e_term empty t) (trm_app x y) *)
(* | max_ec_let_let : forall t' u' t, *)
(*     max_ec' (trm_let (trm_let t' u') t) (e_term empty t) (trm_let t' u') *)
(* | max_ec_let_val_hole : forall u s t v x, *)
(*     max_ec' u (e_hole s) t -> *)
(*     x # s -> *)
(*     max_ec' (trm_let (trm_val v) u) (e_hole (s & x ~ v)) (open_trm x t) *)
(* | max_ec_let_val_term : forall u s u' t v x, *)
(*     max_ec' u (e_term s u') t -> *)
(*     x # s -> (* notin u' also? *) *)
(*     max_ec' (trm_let (trm_val v) u) (e_term (s & x ~ v) u') (open_trm x t). *)

(* Lemma ec_let_val: forall v t u e, *)
(*     max_ec u = (e, trm_let (trm_val v) t) -> False. *)
(* Proof. *)
(*   intros. gen v t e. induction u; intros; inversions H. *)
(*   induction u1; inversions H1. *)
(*   - destruct (max_ec u2); simpl in *. destruct e0; inversions H0. *)
(*     + admit. *)
(*     + admit. *)
(*   - destruct (max_ec u2); simpl in *. *)
(*     destruct t; simpl in *. *)

Lemma ec_inverse'': forall e t u u',
    max_ec' u e t ->
    ec_trm' e t u' ->
    u = u'.
Proof.
  intros. gen u'.
  dependent induction H; intros; try solve [inversions~ H0; false* empty_push_inv].
  - gen u. dependent induction H1; intros.
    + symmetry in x. false* empty_push_inv.
    + destruct (eq_push_inv x) as [? [? ?]]. subst.
      f_equal. specialize (IHmax_ec' _ H1).
      eapply (proj41 open_fresh_trm_val_def_defs_injective); eauto.
  - dependent induction H1.
    + symmetry in x. false* empty_push_inv.
    + destruct (eq_push_inv x) as [? [? ?]]. subst.
      f_equal. specialize (IHmax_ec' _ H1).
      eapply (proj41 open_fresh_trm_val_def_defs_injective); eauto.
Qed.

Lemma ec_trm_helper_e: forall s s' s'' t t',
    ec_trm_helper (e_hole s') s t = ec_trm_helper (e_hole s'') s t /\
    ec_trm_helper (e_term s' t') s t = ec_trm_helper (e_term s'' t') s t.
Proof.
  intros. induction s.
  - split~.
  - destruct a. destruct IHs. simpl. rewrite H. rewrite H0. split~.
Qed.

Lemma close_open_avar: forall x a n,
    lc_var a ->
    open_rec_avar n x (close_rec_avar n x a) = a.
Proof.
  intros. destruct a; simpl; case_if~; subst; inversion H; simpl; case_if~.
Qed.

Lemma max_ec_preserves_lc: forall u e t,
    lc_trm u ->
    (e, t) = max_ec u ->
    lc_term e t.
Proof.
  intros.
  induction u; simpl in *;
    try solve [inversions H0; split~; rewrite~ <- empty_def].
  destruct u1;
    try solve [inversions H; inversions H0; split~; constructor~; rewrite~ <- empty_def].
  destruct (max_ec u2). inversions H0.

(* Lemma ec_preserves_lc: forall e t, *)
(*     ok (ec_sto e) -> *)
(*     lc_ec e -> *)
(*     lc_trm (ec_trm e t) -> *)
(*     lc_term e t. *)
(* Proof. *)
(*   introv Hok Hlc_ec Hlc. destruct e. *)
(*   - simpl in *. gen t. induction s; intros. *)
(*     + split~. *)
(*     + destruct a as [x v]. simpl in *. inversions Hlc. *)
(*       split. *)
(* Qed. *)
(* Admitted. *)

(*
Definition ctx_sto (s: sto) (G: ctx): Prop :=
    forall x v, binds x v s -> exists T, binds x T G /\ G |- (trm_val v) : T
.

I would prefer to use the above definition, but the definition below is
closer to what we already have, so it will be less work.
*)

Definition ctx_sto (s: sto) (G: ctx): Prop := G ~~ s.
Hint Unfold ctx_sto.

Lemma ctx_sto_exists: forall e t U,
    empty |- ec_trm e t : U ->
    exists G, inert G /\ ctx_sto (ec_sto e) G.
(* Use the fact that all the (let x=v in) in u have to type. Use
val_typing lemma from the existing proof to show that they have a precise
type. This type is inert.
*)
Proof.
  intros. dependent induction H.
  - destruct e.
    + gen t. induction s; intros; inversions x.
      * exists (@empty typ). split~. rewrite~ <- empty_def.
      * destruct a as [x v]. simpl in *. Admitted.

Lemma hole_type : forall s t u U G,
    ec_trm (e_hole s) t = u ->
    empty |- u : U ->
    ctx_sto s G ->
    G |- t : U.
Admitted.

Lemma term_type : forall s t' t u U G,
    ec_trm (e_term s t') t = u ->
    empty |- u : U ->
    ctx_sto s G ->
    exists U', G |- t : U'.
Admitted.

Lemma hole_term: forall s t u,
    ec_trm (e_hole s) (trm_let t u) = ec_trm (e_term s u) t.
Proof.
  intros s.
  simpl.
  induction s using env_ind.
  - intros t u.
    unfold ec_trm_helper; rewrite? empty_def; auto.
  - intros t u.
    replace (ec_trm_helper (e_hole (s & x ~ v)) (s & x ~ v) (trm_let t u))
      with (ec_trm_helper (e_hole empty) (s & x ~ v) (trm_let t u))
      by (apply ec_trm_helper_e; auto).
    replace (ec_trm_helper (e_term (s & x ~ v) u) (s & x ~ v) t)
      with (ec_trm_helper (e_term empty u) (s & x ~ v) t)
      by (apply ec_trm_helper_e; auto).
    unfold ec_trm_helper; rewrite? single_def, concat_def; unfold LibList.append; simpl.
    apply f_equal, f_equal.
    replace (fix ec_trm_helper (e : ec) (s0 : sto) (t0 : trm) {struct s0} : trm :=
               match s0 with
               | nil => match e with
                       | e_hole _ => t0
                       | e_term _ u0 => trm_let t0 u0
                       end
               | ((x0, v0) :: s1)%list => trm_let (trm_val v0) (close_trm x0 (ec_trm_helper e s1 t0))
               end) with ec_trm_helper by auto.
    replace (ec_trm_helper (e_hole empty) s (trm_let t u))
      with (ec_trm_helper (e_hole s) s (trm_let t u))
      by (apply ec_trm_helper_e; auto).
    replace (ec_trm_helper (e_term empty u) s t)
      with (ec_trm_helper (e_term s u) s t)
      by (apply ec_trm_helper_e; auto).
    auto.
Qed.


Reserved Notation "e1 '/' t1 '||->' e2 '/' t2" (at level 40, e2 at level 39).

Inductive red' : ec -> trm -> ec -> trm -> Prop :=
(** [e(x) = lambda(T)t]  #<br>#
    [――――――――――――]  #<br>#
    [e | x y |-> e | t^y]  *)
| red_apply : forall x y e T t,
    binds x (val_lambda T t) (ec_sto e) ->
    e / trm_app (avar_f x) (avar_f y) ||-> e / open_trm y t
(** [e(x) = nu(T)...{a = t}...]  #<br>#
    [――――――――――――――――――――――――]  #<br>#
    [e | x.a |-> e | t]  *)
| red_project : forall x a e T ds t,
    binds x (val_new T ds) (ec_sto e) ->
    defs_has (open_defs x ds) (def_trm a t) ->
    e / trm_sel (avar_f x) a ||-> e / t
(** [e[let x = [ ] in t] | y |-> e[ ] | t^y] *)
| red_let_var : forall x t s,
    e_term s t / trm_var (avar_f x) ||-> e_hole s / open_trm x t
(** [e[let x = [ ] in t1] | let t2 in t3 |-> e[let x = [ ] in let t3 in t1] | t2] *)
| red_let_let : forall s t1 t2 t3,
    e_term s t1 / trm_let t2 t3 ||-> e_term s (trm_let t3 t1) / t2
where "t1 '/' st1 '||->' t2 '/' st2" := (red' t1 st1 t2 st2).

Lemma progress : forall u T e t,
  empty |- u : T ->
  (e, t) = max_ec u ->
  normal_form e t \/ exists e' t', e / t ||-> e' / t'.
(* Proof sketch:

Use ctx_sto_exists on (ec_sto e) to get G.
Then do the same things as in old progress theorem.
We no longer have congruence reduction rules.
In their place, use the fact that max_ec never returns a let term that would need them.
*)
Admitted.



(* I think this one is false. Replacing both hole_preserves_type and term_preserves_type
with ec_preserves_type below.

Lemma hole_preserves_type : forall s t u t' u' U G,
    ec_trm (e_hole s) t = u ->
    ec_trm (e_hole s) t' = u' ->
    empty |- u : U ->
    ctx_sto s G ->
    G |- t' : U ->
    empty |- u' : U.
Admitted.
*)

(*
I don't know whether the following lemma is true or not.
I don't know whether we will need the following lemma or not.

Lemma term_preserves_type : forall s t u t' u' U G U' t'',
    ec_trm (e_term s t'') t = u ->
    ec_trm (e_term s t'') t' = u' ->
    empty |- u : U ->
    ctx_sto s G ->
    G |- t : U' ->
    G |- t' : U' ->
    empty |- u' : U.
Admitted.
*)

Lemma ec_preserves_type : forall s t u t' u' U G,
    ec_trm (e_hole s) t = u ->
    ec_trm (e_hole s) t' = u' ->
    empty |- u : U ->
    ctx_sto s G ->
    (forall T, G |- t : T -> G |- t' : T) ->
    empty |- u' : U.
Admitted.

Lemma red_preserves_sto : forall e t e' t',
    e / t ||-> e' / t' ->
    ec_sto e = ec_sto e'.
Admitted.

Lemma preservation : forall u T e t e' t' u',
    lc_trm u ->
    empty |- u : T ->
    ec_trm e t = u ->
    e / t ||-> e' / t' ->
    ec_trm e' t' = u' ->
    empty |- u' : T /\ lc_trm u'.
(*
1) apply ctx_sto_exists
2) case-split on e (e_hole vs e_term)
3) for e_hole case, apply hole_type to get typing for t
4) induct on typing for t, inverting the ||-> in each case, like in the old proof
5) apply hole_preserves_type to go from type of t' to type of u'
6) for e_term case, apply term_type and/or hole_term and ???
*)
Admitted.