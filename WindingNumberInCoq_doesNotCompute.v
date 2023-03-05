From HoTT Require Import Spaces.Pos Spaces.Int.
From HoTT Require Import Basics Types.
From HoTT Require Import Spaces.Circle.

Local Open Scope int_scope.

Context `{Univalence}.

(*
Here we defined the function helix from https://dl.acm.org/doi/abs/10.1145/3372885.3373825
In the HoTT book this is called code (Def. 8.1.1.)
 *)

Definition helix : Circle -> Set 
  := Circle_rec Set Int (path_universe int_succ).

(*
If we input loop^n to winding, we get n. So it counts, how much we go around the circle.
*)

Definition winding (p : (base = base)): Int
  := transport helix p (zero).

(*
the function winding number does not compute, if you check the following proofs you will get an error
*)

Definition winding_at_3 : winding (loopexp loop 3) = 3.
Proof.
reflexivity.
Abort.

Definition winding_at_m1 : winding (loop^ @ loop @ loop^) = -1.
Proof.
reflexivity.
Abort.

(*
In the following we use two theorems from https://github.com/HoTT/Coq-HoTT/blob/master/theories/Spaces/Circle.v 
to actually proof winding_at_3 and winding_at_m1
*)

Theorem transport_helix_loopV (z : Int)
    : transport helix loop^ z = int_pred z.
Proof.
    refine (transport_compose idmap helix loop^ z @ _).
    rewrite ap_V.
    unfold helix; rewrite Circle_rec_beta_loop.
    rewrite <- (path_universe_V int_succ).
    apply transport_path_universe.
Qed.

Theorem Circle_encode_loopexp (z:Int)
    : Circle_encode base (loopexp loop z) = z.
Proof.
    destruct z as [n | | n]; unfold Circle_encode.
    - induction n using pos_peano_ind; simpl in *.
      + refine (moveR_transport_V _ loop _ _ _).
        by symmetry; apply transport_Circle_code_loop.
      + unfold loopexp_pos.
        rewrite pos_peano_ind_beta_pos_succ.
        rewrite transport_pp.
        refine (moveR_transport_V _ loop _ _ _).
        refine (_ @ (transport_Circle_code_loop _)^).
        refine (IHn @ _^).
        rewrite int_neg_pos_succ.
        by rewrite int_succ_pred.
    - reflexivity.
    - induction n using pos_peano_ind; simpl in *.
      + by apply transport_Circle_code_loop.
      + unfold loopexp_pos.
        rewrite pos_peano_ind_beta_pos_succ.
        rewrite transport_pp.
        refine (moveR_transport_p _ loop _ _ _).
        refine (_ @ (transport_Circle_code_loopV _)^).
        refine (IHn @ _^).
        rewrite <- pos_add_1_r.
        change (int_pred (int_succ (pos n)) = pos n).
        apply int_pred_succ.
Qed.

Theorem p: Circle_encode base (loopexp loop 3) = transport helix (loopexp loop 3) 0.
Proof.
reflexivity.
Qed.

(*
Now we can proof, that winding actually computes the way we proposed.
*)


Definition winding_at_3  : winding (loopexp loop 3) = 3.
Proof.
unfold winding.
rewrite <- p.
rewrite Circle_encode_loopexp.
reflexivity.
Qed.

Definition winding_at_m1 : winding (loop^ @ loop @ loop^) = -1.
Proof.
unfold winding.
rewrite concat_Vp.
rewrite concat_1p.
rewrite transport_helix_loopV.
reflexivity.
Qed.










