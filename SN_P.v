(****************************************************************************)
(****************************************************************************)
(*This file proves SN after embedding Presburger*)
(****************************************************************************)
(****************************************************************************)

Require Import PIntp.
Require Import AbsSNT.

Import PSem PSyn.

Module SNP := Abs_SN_Theory PresburgerTheory PresburgerSem IntpPresburger.

Import SNP.
Import Esub SN_CC_Real.
Import ZF SN CCSN. 
Import PresburgerTheory PresburgerSem IntpPresburger.
Import List SN_NAT GenLemmas ZFind_nat.

Inductive valid_ctxt : (list trm -> Prop) :=
| vcnil : valid_ctxt nil
| vcconsN : forall l, valid_ctxt l -> valid_ctxt (Nat::l)
| vcconsP : forall l P t, valid_ctxt l -> typ l t P -> valid_ctxt (P::l).

Lemma valid_ctxt_wf_clsd : forall e, valid_ctxt e -> wf_clsd_env e.
unfold wf_clsd_env; induction 1; intros.
 exists (fun _ => Lc.Abs (Lc.Ref 0)); split; [red|]; intros.
  destruct n; simpl in H; discriminate.
 
  unfold closed_pure_trm; intros k HF; inversion_clear HF. inversion H0.

 assert (val_ok l (V.shift 1 i) (I.shift 1 j)) as Hvalok.
  unfold val_ok in H0 |- *; intros.
  specialize H0 with (n:=S n) (T:=T) (1:=H1).
  unfold in_int in H0 |- *.
  destruct H0 as (_, H0). split; [discriminate|].
  destruct T; do 2 red in H0 |- *.
   revert H0; apply real_morph. 
    unfold V.shift; simpl; reflexivity.

    simpl; unfold V.shift; simpl. reflexivity.

    unfold I.shift; simpl; reflexivity.

   red in H0 |- *. destruct H0 as (Hko, Hsn). split.
    rewrite kind_ok_lift with (k:=0). rewrite eq_trm_lift_ref_fv by omega. apply Hko.

    apply Hsn.

 specialize IHvalid_ctxt with (1:=Hvalok).
 unfold val_ok in H0.
 assert (nth_error (Nat::l) 0 = value Nat) by trivial.
 specialize H0 with (1:=H1).
 unfold in_int in H0. destruct H0 as (_, H0). do 3 red in H0.
 destruct H0 as (H0, _). unfold inX in H0. simpl in H0. rewrite El_def in H0.
 clear j Hvalok H1.
 destruct IHvalid_ctxt as (j, (Hval, Hclsd)).
 specialize inSAT_n with (1:=H0); intros H1.
 destruct H1 as (t, (HinSAT, Hclsdt)).
 exists (I.cons t j); split.
  apply vcons_add_var with (T:=Nat) (x:= i 0) (t:=t) in Hval.
   unfold val_ok in Hval |- *. intros.
   specialize Hval with (1:=H1).
   revert Hval; apply in_int_morph;[|reflexivity|reflexivity|reflexivity].
    rewrite V.cons_ext with (i':=i); reflexivity.
    
   split.
    unfold inX. simpl; rewrite El_def; apply H0.
    
    rewrite RealNat_eq; trivial.

   discriminate.

  intro n; destruct n; simpl; trivial.

 assert (val_ok l (V.shift 1 i) (I.shift 1 j)).
  unfold val_ok in H1|-*; intros.
  specialize H1 with (n:=S n) (T:=T) (1:=H2).
  unfold in_int in H1 |-*.
  destruct H1 as (_, H1).
  split; [discriminate|].
  destruct T; do 2 red in H1 |- *. 
   apply H1.
   
   red in H1 |- *. destruct H1 as (H1, H3). split; [|apply H3].
    rewrite kind_ok_lift with (k:=0).
    rewrite eq_trm_lift_ref_fv by omega; apply H1.
 

Qed.  

Lemma SN_P : forall e x y,
  (exists hyp a b es, 
    x = app_esub es (intp_fotrm a) /\
    y = app_esub es (intp_fotrm b) /\
    wf_clsd_env (intp_hyp hyp) /\
    typ_esub e es (intp_hyp hyp) /\
    deriv hyp (eq_fotrm a b)) ->
  eq_typ e x y.
Proof. apply SN_T. Qed.