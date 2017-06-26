Set Implicit Arguments.

Require Import LibLN.
Require Import Coq.Program.Equality.

(* ###################################################################### *)
(* ###################################################################### *)
(** * Definitions *)

(* ###################################################################### *)
(** ** Syntax *)

Parameter typ_label: Set.
Parameter trm_label: Set.

Inductive label: Set :=
| label_typ: typ_label -> label
| label_trm: trm_label -> label.

Inductive avar : Set :=
  | avar_b : nat -> avar  (* bound var (de Bruijn index) *)
  | avar_f : var -> avar. (* free var ("name"), refers to store or ctx *)

Inductive typ : Set :=
  | typ_top  : typ
  | typ_bot  : typ
  | typ_rcd  : dec -> typ (* { D } *)
  | typ_and  : typ -> typ -> typ
  | typ_sel  : avar -> typ_label -> typ (* x.L *)
  | typ_bnd  : typ -> typ (* rec(x: T) *)
  | typ_all  : typ -> typ -> typ (* all(x: S)T *)
with dec : Set :=
  | dec_typ  : typ_label -> typ -> typ -> dec (* A: S..U *)
  | dec_trm  : trm_label -> typ -> dec (* a: T *).

Inductive trm : Set :=
  | trm_var  : avar -> trm
  | trm_val  : val -> trm
  | trm_sel  : avar -> trm_label -> trm
  | trm_app  : avar -> avar -> trm
  | trm_let  : trm -> trm -> trm (* let x = t in u *)
with val : Set :=
  | val_new  : typ -> defs -> val
  | val_lambda : typ -> trm -> val
with def : Set :=
  | def_typ  : typ_label -> typ -> def
  | def_trm  : trm_label -> trm -> def
with defs : Set :=
  | defs_nil : defs
  | defs_cons : defs -> def -> defs.

(** *** Typing environment ("Gamma") *)
Definition ctx := env typ.

(** *** Value environment ("store") *)
Definition sto := env val.

Inductive ec : Set :=
| e_empty     : ec              (* [] *)
| e_let_val   : var -> val -> ec -> ec  (* let x = v in e *)
| e_let_trm   : var -> trm -> ec.      (* let x = [] in t *)

(* ###################################################################### *)
(** ** Definition list membership *)

Definition label_of_def(d: def): label := match d with
| def_typ L _ => label_typ L
| def_trm m _ => label_trm m
end.

Definition label_of_dec(D: dec): label := match D with
| dec_typ L _ _ => label_typ L
| dec_trm m _   => label_trm m
end.

Fixpoint get_def(l: label)(ds: defs): option def :=
match ds with
| defs_nil => None
| defs_cons ds' d => If label_of_def d = l then Some d else get_def l ds'
end.

Definition defs_has(ds: defs)(d: def) := get_def (label_of_def d) ds = Some d.
Definition defs_hasnt(ds: defs)(l: label) := get_def l ds = None.

(* ###################################################################### *)
(** ** Opening *)

(** Opening replaces in some syntax a bound variable with dangling index (k)
   by a free variable x. *)

Definition open_rec_avar (k: nat) (u: var) (a: avar) : avar :=
  match a with
  | avar_b i => If k = i then avar_f u else avar_b i
  | avar_f x => avar_f x
  end.

Fixpoint open_rec_typ (k: nat) (u: var) (T: typ): typ :=
  match T with
  | typ_top        => typ_top
  | typ_bot        => typ_bot
  | typ_rcd D      => typ_rcd (open_rec_dec k u D)
  | typ_and T1 T2  => typ_and (open_rec_typ k u T1) (open_rec_typ k u T2)
  | typ_sel x L    => typ_sel (open_rec_avar k u x) L
  | typ_bnd T      => typ_bnd (open_rec_typ (S k) u T)
  | typ_all T1 T2  => typ_all (open_rec_typ k u T1) (open_rec_typ (S k) u T2)
  end
with open_rec_dec (k: nat) (u: var) (D: dec): dec :=
  match D with
  | dec_typ L T U => dec_typ L (open_rec_typ k u T) (open_rec_typ k u U)
  | dec_trm m T   => dec_trm m (open_rec_typ k u T)
  end.

Fixpoint open_rec_trm (k: nat) (u: var) (t: trm): trm :=
  match t with
  | trm_var a      => trm_var (open_rec_avar k u a)
  | trm_val v      => trm_val (open_rec_val k u v)
  | trm_sel v m    => trm_sel (open_rec_avar k u v) m
  | trm_app f a    => trm_app (open_rec_avar k u f) (open_rec_avar k u a)
  | trm_let t1 t2  => trm_let (open_rec_trm k u t1) (open_rec_trm (S k) u t2)
  end
with open_rec_val (k: nat) (u: var) (v: val): val :=
  match v with
  | val_new T ds => val_new (open_rec_typ (S k) u T) (open_rec_defs (S k) u ds)
  | val_lambda T e => val_lambda (open_rec_typ k u T) (open_rec_trm (S k) u e)
  end
with open_rec_def (k: nat) (u: var) (d: def): def :=
  match d with
  | def_typ L T => def_typ L (open_rec_typ k u T)
  | def_trm m e => def_trm m (open_rec_trm k u e)
  end
with open_rec_defs (k: nat) (u: var) (ds: defs): defs :=
  match ds with
  | defs_nil => defs_nil
  | defs_cons tl d => defs_cons (open_rec_defs k u tl) (open_rec_def k u d)
  end.

Definition open_avar u a := open_rec_avar  0 u a.
Definition open_typ  u t := open_rec_typ   0 u t.
Definition open_dec  u D := open_rec_dec   0 u D.
Definition open_trm  u e := open_rec_trm   0 u e.
Definition open_val  u v := open_rec_val   0 u v.
Definition open_def  u d := open_rec_def   0 u d.
Definition open_defs u l := open_rec_defs  0 u l.

Fixpoint open_ec (u: var) (e: ec): ec :=
  match e with
  | e_empty => e_empty
  | e_let_val x v e => e_let_val x (open_val u v) (open_ec u e)
  | e_let_trm x t => e_let_trm x (open_trm u t)
  end.

(* ###################################################################### *)
(** ** Record types *)

Inductive record_dec : dec -> Prop :=
| rd_typ : forall A T, record_dec (dec_typ A T T)
| rd_trm : forall a T, record_dec (dec_trm a T).

Inductive record_typ : typ -> fset label -> Prop :=
| rt_one : forall D l,
  record_dec D ->
  l = label_of_dec D ->
  record_typ (typ_rcd D) \{l}
| rt_cons: forall T ls D l,
  record_typ T ls ->
  record_dec D ->
  l = label_of_dec D ->
  l \notin ls ->
  record_typ (typ_and T (typ_rcd D)) (union ls \{l}).

Definition record_type T := exists ls, record_typ T ls.

Inductive record_has: typ -> dec -> Prop :=
| rh_one : forall D,
    record_has (typ_rcd D) D
| rh_andl : forall T U D,
    record_has T D ->
    record_has (typ_and T U) D
| rh_andr : forall T U D,
    record_has U D ->
    record_has (typ_and T U) D.

(* ###################################################################### *)
(** ** Free variables *)

Definition fv_avar (a: avar) : vars :=
  match a with
  | avar_b i => \{}
  | avar_f x => \{x}
  end.

Fixpoint fv_typ (T: typ) : vars :=
  match T with
  | typ_top        => \{}
  | typ_bot        => \{}
  | typ_rcd D      => (fv_dec D)
  | typ_and T U    => (fv_typ T) \u (fv_typ U)
  | typ_sel x L    => (fv_avar x)
  | typ_bnd T      => (fv_typ T)
  | typ_all T1 T2  => (fv_typ T1) \u (fv_typ T2)
  end
with fv_dec (D: dec) : vars :=
  match D with
  | dec_typ L T U => (fv_typ T) \u (fv_typ U)
  | dec_trm m T   => (fv_typ T)
  end.

Fixpoint fv_trm (t: trm) : vars :=
  match t with
  | trm_var a       => (fv_avar a)
  | trm_val v        => (fv_val v)
  | trm_sel x m      => (fv_avar x)
  | trm_app f a      => (fv_avar f) \u (fv_avar a)
  | trm_let t1 t2    => (fv_trm t1) \u (fv_trm t2)
  end
with fv_val (v: val) : vars :=
  match v with
  | val_new T ds    => (fv_typ T) \u (fv_defs ds)
  | val_lambda T e  => (fv_typ T) \u (fv_trm e)
  end
with fv_def (d: def) : vars :=
  match d with
  | def_typ _ T     => (fv_typ T)
  | def_trm _ t     => (fv_trm t)
  end
with fv_defs(ds: defs) : vars :=
  match ds with
  | defs_nil         => \{}
  | defs_cons tl d   => (fv_defs tl) \u (fv_def d)
  end.

Fixpoint fv_ec (e: ec) : vars :=
  match e with
  | e_empty => \{}
  | e_let_val x v e => \{x} \u (fv_val v) \u (fv_ec e)
  | e_let_trm x t => \{x} \u (fv_trm t)
  end.

Definition fv_ctx_types(G: ctx): vars := (fv_in_values (fun T => fv_typ T) G).


(* ###################################################################### *)
(** ** Tactics *)

Ltac gather_vars :=
  let A := gather_vars_with (fun x : vars      => x         ) in
  let B := gather_vars_with (fun x : var       => \{ x }    ) in
  let C := gather_vars_with (fun x : ctx       => (dom x) \u (fv_ctx_types x)) in
  let D := gather_vars_with (fun x : sto       => dom x     ) in
  let E := gather_vars_with (fun x : avar      => fv_avar  x) in
  let F := gather_vars_with (fun x : trm       => fv_trm   x) in
  let G := gather_vars_with (fun x : val       => fv_val   x) in
  let H := gather_vars_with (fun x : def       => fv_def   x) in
  let I := gather_vars_with (fun x : defs      => fv_defs  x) in
  let J := gather_vars_with (fun x : typ       => fv_typ   x) in
  let K := gather_vars_with (fun x : ec        => fv_ec    x) in
  constr:(A \u B \u C \u D \u E \u F \u G \u H \u I \u J \u K).

Ltac pick_fresh x :=
  let L := gather_vars in (pick_fresh_gen L x).

Ltac in_empty_contradiction :=
  solve [match goal with
  | H: _ \in \{} |- _ => rewrite in_empty in H; exfalso; exact H
  end].

Ltac eq_specialize :=
  repeat match goal with
  | H:                 _ = _ -> _ |- _ => specialize (H         eq_refl)
  | H: forall _      , _ = _ -> _ |- _ => specialize (H _       eq_refl)
  | H: forall _ _    , _ = _ -> _ |- _ => specialize (H _ _     eq_refl)
  | H: forall _ _ _  , _ = _ -> _ |- _ => specialize (H _ _ _   eq_refl)
  | H: forall _ _ _ _, _ = _ -> _ |- _ => specialize (H _ _ _ _ eq_refl)
  end.

Ltac crush := eq_specialize; eauto.

Tactic Notation "apply_fresh" constr(T) "as" ident(x) :=
  apply_fresh_base T gather_vars x.

(* ###################################################################### *)
(** ** Operational Semantics *)

Reserved Notation "t1 '/' st1 '=>' t2 '/' st2" (at level 40, t2 at level 39).

Inductive red : trm -> sto -> trm -> sto -> Prop :=
| red_sel : forall x m s t T ds,
    binds x (val_new T ds) s ->
    defs_has (open_defs x ds) (def_trm m t) ->
    trm_sel (avar_f x) m / s => t / s
| red_app : forall f a s T t,
    binds f (val_lambda T t) s ->
    trm_app (avar_f f) (avar_f a) / s => open_trm a t / s
| red_let : forall v t s x,
    x # s ->
    trm_let (trm_val v) t / s => open_trm x t / s & x ~ v
| red_let_var : forall t s x,
    trm_let (trm_var (avar_f x)) t / s => open_trm x t / s
| red_let_tgt : forall t0 t s t0' s',
    t0 / s => t0' / s' ->
    trm_let t0 t / s => trm_let t0' t / s'
where "t1 '/' st1 '=>' t2 '/' st2" := (red t1 st1 t2 st2).

(* ###################################################################### *)
(** ** Typing *)

Reserved Notation "G '|-' t ':' T" (at level 40, t at level 59).
Reserved Notation "G '|-' T '<:' U" (at level 40, T at level 59).
Reserved Notation "G '/-' d : D" (at level 40, d at level 59).
Reserved Notation "G '/-' ds :: D" (at level 40, ds at level 59).

Inductive ty_trm : ctx -> trm -> typ -> Prop :=
| ty_var : forall G x T,
    binds x T G ->
    G |- trm_var (avar_f x) : T
| ty_all_intro : forall L G T t U,
    (forall x, x \notin L ->
      G & x ~ T |- open_trm x t : open_typ x U) ->
    G |- trm_val (val_lambda T t) : typ_all T U
| ty_all_elim : forall G x z S T,
    G |- trm_var (avar_f x) : typ_all S T ->
    G |- trm_var (avar_f z) : S ->
    G |- trm_app (avar_f x) (avar_f z) : open_typ z T
| ty_new_intro : forall L G T ds,
    (forall x, x \notin L ->
      G & (x ~ open_typ x T) /- open_defs x ds :: open_typ x T) ->
    G |- trm_val (val_new T ds) : typ_bnd T
| ty_new_elim : forall G x m T,
    G |- trm_var (avar_f x) : typ_rcd (dec_trm m T) ->
    G |- trm_sel (avar_f x) m : T
| ty_let : forall L G t u T U,
    G |- t : T ->
    (forall x, x \notin L ->
      G & x ~ T |- open_trm x u : U) ->
    G |- trm_let t u : U
| ty_rec_intro : forall G x T,
    G |- trm_var (avar_f x) : open_typ x T ->
    G |- trm_var (avar_f x) : typ_bnd T
| ty_rec_elim : forall G x T,
    G |- trm_var (avar_f x) : typ_bnd T ->
    G |- trm_var (avar_f x) : open_typ x T
| ty_and_intro : forall G x T U,
    G |- trm_var (avar_f x) : T ->
    G |- trm_var (avar_f x) : U ->
    G |- trm_var (avar_f x) : typ_and T U
| ty_sub : forall G t T U,
    G |- t : T ->
    G |- T <: U ->
    G |- t : U
where "G '|-' t ':' T" := (ty_trm G t T)

with ty_def : ctx -> def -> dec -> Prop :=
| ty_def_typ : forall G A T,
    G /- def_typ A T : dec_typ A T T
| ty_def_trm : forall G a t T,
    G |- t : T ->
    G /- def_trm a t : dec_trm a T
where "G '/-' d ':' D" := (ty_def G d D)

with ty_defs : ctx -> defs -> typ -> Prop :=
| ty_defs_one : forall G d D,
    G /- d : D ->
    G /- defs_cons defs_nil d :: typ_rcd D
| ty_defs_cons : forall G ds d T D,
    G /- ds :: T ->
    G /- d : D ->
    defs_hasnt ds (label_of_def d) ->
    G /- defs_cons ds d :: typ_and T (typ_rcd D)
where "G '/-' ds '::' T" := (ty_defs G ds T)

with subtyp : ctx -> typ -> typ -> Prop :=
| subtyp_top: forall G T,
    G |- T <: typ_top
| subtyp_bot: forall G T,
    G |- typ_bot <: T
| subtyp_refl: forall G T,
    G |- T <: T
| subtyp_trans: forall G S T U,
    G |- S <: T ->
    G |- T <: U ->
    G |- S <: U
| subtyp_and11: forall G T U,
    G |- typ_and T U <: T
| subtyp_and12: forall G T U,
    G |- typ_and T U <: U
| subtyp_and2: forall G S T U,
    G |- S <: T ->
    G |- S <: U ->
    G |- S <: typ_and T U
| subtyp_fld: forall G a T U,
    G |- T <: U ->
    G |- typ_rcd (dec_trm a T) <: typ_rcd (dec_trm a U)
| subtyp_typ: forall G A S1 T1 S2 T2,
    G |- S2 <: S1 ->
    G |- T1 <: T2 ->
    G |- typ_rcd (dec_typ A S1 T1) <: typ_rcd (dec_typ A S2 T2)
| subtyp_sel2: forall G x A S T,
    G |- trm_var (avar_f x) : typ_rcd (dec_typ A S T) ->
    G |- S <: typ_sel (avar_f x) A
| subtyp_sel1: forall G x A S T,
    G |- trm_var (avar_f x) : typ_rcd (dec_typ A S T) ->
    G |- typ_sel (avar_f x) A <: T
| subtyp_all: forall L G S1 T1 S2 T2,
    G |- S2 <: S1 ->
    (forall x, x \notin L ->
       G & x ~ S2 |- open_typ x T1 <: open_typ x T2) ->
    G |- typ_all S1 T1 <: typ_all S2 T2
where "G '|-' T '<:' U" := (subtyp G T U).

Reserved Notation "G '|-!' t ':' T" (at level 40, t at level 59).

Inductive ty_trm_p : ctx -> trm -> typ -> Prop :=
| ty_var_p : forall G x T,
    binds x T G ->
    G |-! trm_var (avar_f x) : T
| ty_all_intro_p : forall L G T t U,
    (forall x, x \notin L ->
      G & x ~ T |- open_trm x t : open_typ x U) ->
    G |-! trm_val (val_lambda T t) : typ_all T U
| ty_new_intro_p : forall L G T ds,
    (forall x, x \notin L ->
      G & (x ~ open_typ x T) /- open_defs x ds :: open_typ x T) ->
    G |-! trm_val (val_new T ds) : typ_bnd T
| ty_rec_elim_p : forall G x T,
    G |-! trm_var (avar_f x) : typ_bnd T ->
    G |-! trm_var (avar_f x) : open_typ x T
| ty_and1_p : forall G x T U,
    G |-! trm_var (avar_f x) : typ_and T U ->
    G |-! trm_var (avar_f x) : T
| ty_and2_p : forall G x T U,
    G |-! trm_var (avar_f x) : typ_and T U ->
    G |-! trm_var (avar_f x) : U
where "G '|-!' t ':' T" := (ty_trm_p G t T).

Reserved Notation "G '|-#' t ':' T" (at level 40, t at level 59).
Reserved Notation "G '|-#' T '<:' U" (at level 40, T at level 59).

Inductive ty_trm_t : ctx -> trm -> typ -> Prop :=
| ty_var_t : forall G x T,
    binds x T G ->
    G |-# trm_var (avar_f x) : T
| ty_all_intro_t : forall L G T t U,
    (forall x, x \notin L ->
      G & x ~ T |- open_trm x t : open_typ x U) ->
    G |-# trm_val (val_lambda T t) : typ_all T U
| ty_all_elim_t : forall G x z S T,
    G |-# trm_var (avar_f x) : typ_all S T ->
    G |-# trm_var (avar_f z) : S ->
    G |-# trm_app (avar_f x) (avar_f z) : open_typ z T
| ty_new_intro_t : forall L G T ds,
    (forall x, x \notin L ->
      G & (x ~ open_typ x T) /- open_defs x ds :: open_typ x T) ->
    G |-# trm_val (val_new T ds) : typ_bnd T
| ty_new_elim_t : forall G x m T,
    G |-# trm_var (avar_f x) : typ_rcd (dec_trm m T) ->
    G |-# trm_sel (avar_f x) m : T
| ty_let_t : forall L G t u T U,
    G |-# t : T ->
    (forall x, x \notin L ->
      G & x ~ T |- open_trm x u : U) ->
    G |-# trm_let t u : U
| ty_rec_intro_t : forall G x T,
    G |-# trm_var (avar_f x) : open_typ x T ->
    G |-# trm_var (avar_f x) : typ_bnd T
| ty_rec_elim_t : forall G x T,
    G |-# trm_var (avar_f x) : typ_bnd T ->
    G |-# trm_var (avar_f x) : open_typ x T
| ty_and_intro_t : forall G x T U,
    G |-# trm_var (avar_f x) : T ->
    G |-# trm_var (avar_f x) : U ->
    G |-# trm_var (avar_f x) : typ_and T U
| ty_sub_t : forall G t T U,
    G |-# t : T ->
    G |-# T <: U ->
    G |-# t : U
where "G '|-#' t ':' T" := (ty_trm_t G t T)

with subtyp_t : ctx -> typ -> typ -> Prop :=
| subtyp_top_t: forall G T,
    G |-# T <: typ_top
| subtyp_bot_t: forall G T,
    G |-# typ_bot <: T
| subtyp_refl_t: forall G T,
    G |-# T <: T
| subtyp_trans_t: forall G S T U,
    G |-# S <: T ->
    G |-# T <: U ->
    G |-# S <: U
| subtyp_and11_t: forall G T U,
    G |-# typ_and T U <: T
| subtyp_and12_t: forall G T U,
    G |-# typ_and T U <: U
| subtyp_and2_t: forall G S T U,
    G |-# S <: T ->
    G |-# S <: U ->
    G |-# S <: typ_and T U
| subtyp_fld_t: forall G a T U,
    G |-# T <: U ->
    G |-# typ_rcd (dec_trm a T) <: typ_rcd (dec_trm a U)
| subtyp_typ_t: forall G A S1 T1 S2 T2,
    G |-# S2 <: S1 ->
    G |-# T1 <: T2 ->
    G |-# typ_rcd (dec_typ A S1 T1) <: typ_rcd (dec_typ A S2 T2)
| subtyp_sel2_t: forall G x A T,
    G |-! trm_var (avar_f x) : typ_rcd (dec_typ A T T) ->
    G |-# T <: typ_sel (avar_f x) A
| subtyp_sel1_t: forall G x A T,
    G |-! trm_var (avar_f x) : typ_rcd (dec_typ A T T) ->
    G |-# typ_sel (avar_f x) A <: T
| subtyp_all_t: forall L G S1 T1 S2 T2,
    G |-# S2 <: S1 ->
    (forall x, x \notin L ->
       G & x ~ S2 |- open_typ x T1 <: open_typ x T2) ->
    G |-# typ_all S1 T1 <: typ_all S2 T2
where "G '|-#' T '<:' U" := (subtyp_t G T U).

Reserved Notation "G '|-##' x ':' T" (at level 40, x at level 59).

Inductive ty_trm_inv : ctx -> var -> typ -> Prop :=
  (* Precise typing *)
| ty_precise_inv : forall G x T,
  G |-! trm_var (avar_f x) : T ->
  G |-## x : T
  (* Term member subtyping *)
| ty_dec_trm_inv : forall G x a T T',
  G |-## x : typ_rcd (dec_trm a T) ->
  G |-# T <: T' ->
  G |-## x : typ_rcd (dec_trm a T')
  (* Type member subtyping *)
| ty_dec_typ_inv : forall G x A T T' U' U,
  G |-## x : typ_rcd (dec_typ A T U) ->
  G |-# T' <: T ->
  G |-# U <: U' ->
  G |-## x : typ_rcd (dec_typ A T' U')
  (* Recursive Types *)
| ty_bnd_inv : forall G x S S',
  G |-## x : S ->
  S = open_typ x S' ->
  G |-## x : typ_bnd S'
  (* Forall *)
| ty_all_inv : forall L G x S T S' T',
  G |-## x : typ_all S T ->
  G |-# S' <: S ->
  (forall y, y \notin L ->
   G & y ~ S' |- open_typ y T <: open_typ y T') ->
  G |-## x : typ_all S' T'
  (* And *)
| ty_and_inv : forall G x S1 S2,
  G |-## x : S1 ->
  G |-## x : S2 ->
  G |-## x : typ_and S1 S2
  (* Tight Selection *)
| ty_sel_inv : forall G x y A S,
  G |-## x : S ->
  G |-! trm_var y : typ_rcd (dec_typ A S S) ->
  G |-## x : typ_sel y A
  (* Top *)
| ty_top_inv : forall G x T,
  G |-## x : T ->
  G |-## x : typ_top
where "G '|-##' x ':' T" := (ty_trm_inv G x T).

Reserved Notation "G '|-##v' v ':' T" (at level 40, v at level 59).

Inductive ty_trm_inv_v : ctx -> val -> typ -> Prop :=
  (* Precise typing *)
| ty_precise_inv_v : forall G v T,
  G |-! trm_val v : T ->
  G |-##v v : T
  (* Forall *)
| ty_all_inv_v : forall L G v S T S' T',
  G |-##v v : typ_all S T ->
  G |-# S' <: S ->
  (forall y, y \notin L ->
   G & y ~ S' |- open_typ y T <: open_typ y T') ->
  G |-##v v : typ_all S' T'
  (* Tight Selection *)
| ty_sel_inv_v : forall G v y A S,
  G |-##v v : S ->
  G |-! trm_var y : typ_rcd (dec_typ A S S) ->
  G |-##v v : typ_sel y A
| ty_and_inv_v : forall G v T U,
  G |-##v v : T ->
  G |-##v v : U ->
  G |-##v v : typ_and T U
  (* Top *)
| ty_top_inv_v : forall G v T,
  G |-##v v : T ->
  G |-##v v : typ_top
where "G '|-##v' v ':' T" := (ty_trm_inv_v G v T).

(** TODO: move **)

Reserved Notation "e '{{' u '}}' '==' t" (at level 60).
Inductive ec_app : ec -> trm -> trm -> Prop :=
(* e[u] ≡ t *)
| ec_empty : forall t,
    e_empty {{ t }} == t
(* ⦰[t] ≡ t *)
| ec_val : forall x e u t v,
    x \notin ((fv_ec e) \u (fv_trm t) \u (fv_val v) \u (fv_trm u)) ->
    e {{ u }} == t ->
    e_let_val x v (open_ec x e) {{ open_trm x u }} == (trm_let (trm_val v) t)
(* let x = v in e[u] ≡ let x=v in t *)
(* (e,x=v)[u] ≡ let x=v in t *)
| ec_trm : forall x u t,
    x \notin ((fv_trm u) \u (fv_trm t)) ->
    (e_let_trm x (open_trm x t)) {{ u }} == (trm_let u t)
(* let x = [u] in t ≡ let x=u in t *)
where "e '{{' u '}}' '==' t" := (ec_app e u t).

(** TODO: remove ' from names **)
Reserved Notation "t1 '|=>' t2" (at level 60).
Inductive ec_red : trm -> trm -> Prop :=
| red_term' : forall t t' e et et',
    t |=> t' ->
    e {{ t }} == et ->
    e {{ t' }} == et' ->
    et |=> et'
| red_apply' : forall x e y t T t1 t2,
    x \notin ((fv_ec e) \u (fv_trm t) \u (fv_typ T)) ->
    (e_let_val x (val_lambda T t) e) {{ (trm_app (avar_f x) (avar_f y)) }} == t1 ->
    (e_let_val x (val_lambda T t) e) {{ (open_trm y t) }} == t2 ->
    t1 |=> t2
| red_project' : forall x e a t ds T t1 t2,
    x \notin ((fv_ec e) \u (fv_defs ds)) ->
    defs_has (open_defs x ds) (def_trm a t) ->
    (e_let_val x (val_new T ds) e) {{ (trm_sel (avar_f x) a) }} == t1 ->
    (e_let_val x (val_new T ds) e) {{ t }} == t2 ->
    t1 |=> t2
| red_let_var' : forall y t,
    trm_let (trm_var (avar_f y)) t |=> (open_trm y t)
| red_let_let' : forall s t u,
    trm_let (trm_let s t) u |=> (trm_let s (trm_let t u))
where "t1 '|=>' t2 " := (ec_red t1 t2).

(* Reserved Notation "e '{{' G '}}' '==' G'" (at level 60). *)
(* Inductive eg_app : ec -> ctx -> ctx -> Prop := *)
(* | eg_empty : forall G, e_empty {{G}} == G *)
(* | eg_val : forall L G x e (v: val) T G', *)
(*     x \notin L -> *)
(*     G |-! trm_val v : T -> *)
(*     e{{G & x ~ T}} == G' -> *)
(*     (e_let_val x v e) {{G}} == G' *)
(* | eg_trm : forall G x u, (e_let_trm x u) {{G}} == G *)
(* where "e '{{' G '}}' '==' G'" := (eg_app e G G'). *)

Reserved Notation "G '~~' s" (at level 40).

Inductive wf_sto: ctx -> sto -> Prop :=
| wf_sto_empty: empty ~~ empty
| wf_sto_push: forall G s x T v,
    G ~~ s ->
    x # G ->
    x # s ->
    G |- trm_val v : T ->
    G & x ~ T ~~ s & x ~ v
where "G '~~' s" := (wf_sto G s).

(* ###################################################################### *)
(* ###################################################################### *)
(** * Infrastructure *)

(* ###################################################################### *)
(** ** Induction principles *)

Scheme typ_mut := Induction for typ Sort Prop
with   dec_mut := Induction for dec Sort Prop.
Combined Scheme typ_mutind from typ_mut, dec_mut.

Scheme trm_mut  := Induction for trm  Sort Prop
with   val_mut  := Induction for val Sort Prop
with   def_mut  := Induction for def  Sort Prop
with   defs_mut := Induction for defs Sort Prop.
Combined Scheme trm_mutind from trm_mut, val_mut, def_mut, defs_mut.

Scheme ts_ty_trm_t_mut := Induction for ty_trm_t Sort Prop
with   ts_subtyp_t     := Induction for subtyp_t Sort Prop.
Combined Scheme ts_mutind_t from ts_ty_trm_t_mut, ts_subtyp_t.

Scheme ts_ty_trm_mut := Induction for ty_trm Sort Prop
with   ts_subtyp     := Induction for subtyp Sort Prop.
Combined Scheme ts_mutind from ts_ty_trm_mut, ts_subtyp.

Scheme rules_trm_mut    := Induction for ty_trm Sort Prop
with   rules_def_mut    := Induction for ty_def Sort Prop
with   rules_defs_mut   := Induction for ty_defs Sort Prop
with   rules_subtyp     := Induction for subtyp Sort Prop.
Combined Scheme rules_mutind from rules_trm_mut, rules_def_mut, rules_defs_mut, rules_subtyp.

Hint Constructors
  ty_trm ty_def ty_defs subtyp
  ty_trm_p
  ty_trm_t subtyp_t
  ty_trm_inv ty_trm_inv_v.

Hint Constructors wf_sto.

Hint Constructors record_has.

Lemma fresh_push_eq_inv: forall A x a (E: env A),
  x # (E & x ~ a) -> False.
Proof.
  intros. rewrite dom_push in H. false H. rewrite in_union.
  left. rewrite in_singleton. reflexivity.
Qed.
