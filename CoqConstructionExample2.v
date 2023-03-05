From HoTT Require Import Spaces.Pos Spaces.Int.
From HoTT Require Import Basics Types.
From HoTT Require Import Spaces.Circle.

Local Open Scope int_scope.

Context `{Univalence}.

Definition helix : Circle -> Set 
  := Circle_rec Set Int (path_universe int_succ).

Definition winding (p : (base = base)): Int
  := transport helix p (zero).



(* the functio winding number does not compute*)


Definition h1 : winding (loopexp loop 3) = 3.
Proof.
reflexivity.
Abort.

Definition h2 : winding (loop^ @ loop @ loop^) = -1.
Proof.
reflexivity.
Abort.







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

Definition h3 : winding (loopexp loop 3) = 3.
Proof.
unfold winding.
rewrite <- p.
rewrite Circle_encode_loopexp.
reflexivity.
Qed.

Definition h4 : winding (loop^ @ loop @ loop^) = -1.
Proof.
unfold winding.
rewrite concat_Vp.
rewrite concat_1p.
rewrite transport_helix_loopV.
reflexivity.
Qed.










