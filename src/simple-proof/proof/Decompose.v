(** printing ⊢#    %\vdash_{\#}%    #&vdash;<sub>&#35;</sub>#     *)
(** printing ⊢##   %\vdash_{\#\#}%  #&vdash;<sub>&#35&#35</sub>#  *)
(** printing ⊢##v  %\vdash_{\#\#v}% #&vdash;<sub>&#35&#35v</sub># *)
(** printing ⊢!    %\vdash_!%       #&vdash;<sub>!</sub>#         *)
(** remove printing ~ *)

(** This module reasons about the precise types of variables in inert contexts. *)

Set Implicit Arguments.

Require Import Coq.Program.Equality.
Require Import Definitions RecordAndInertTypes TightTyping PreciseSubtyping.


Theorem destruct_subtyp_typ_t : forall G0,
    inert G0 ->
    (forall A S1 T1 S2 T2,
        G0 ⊢# typ_rcd (dec_typ A S1 T1) <: typ_rcd (dec_typ A S2 T2) ->
        G0 ⊢# S2 <: S1 /\ G0 ⊢# T1 <: T2).
Proof.
  eauto.
Qed.

