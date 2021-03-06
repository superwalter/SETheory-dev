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
Import List SN_NAT GenLemmas ZFind_nat SATnat.





Lemma prf_irr_set : forall e P, typ e P prop ->
  (forall i j t, val_ok e i j -> t ∈ El (int i P) -> t == empty).
intros e P HP i j t Hok Ht.
apply red_typ with (1:=Hok) in HP; [|discriminate].
destruct HP as (_, (HP, _)). unfold inX in HP. simpl in HP.
rewrite El_props_def in HP. destruct HP as (S, HP).
rewrite HP in Ht. rewrite El_mkProp in Ht. apply singl_elim; trivial.
Qed.

Inductive valid_ctxt : (list trm -> Prop) :=
| vcnil : valid_ctxt nil
| vcconsN : forall l, valid_ctxt l -> valid_ctxt (Nat::l)
| vcconsP : forall l t x y, 
  valid_ctxt l -> typ l x Nat -> typ l y Nat -> 
  (exists i j, val_ok l i j /\ [int i t, tm j t] \real int i (EQ_trm x y)) -> 
  valid_ctxt ((EQ_trm x y)::l).




Lemma valid_ctxt_wf_clsd : forall e, valid_ctxt e -> wf_clsd_env e.
induction 1. Focus 3.


unfold wf_clsd_env; induction 1 as [|l HE IH|l t x y HE IH Hx Hy]; intros i j Hok.
 exists (fun _ => Lc.Abs (Lc.Ref 0)). split; [red; intros n T Hn|intros _].
  destruct n; simpl in Hn; discriminate.
 
  unfold closed_pure_trm; intros k HF; inversion_clear HF. inversion H.

 assert (val_ok l (V.shift 1 i) (I.shift 1 j)) as Hvalok.
  unfold val_ok in Hok |- *; intros.
  specialize Hok with (n:=S n) (T:=T) (1:=H).
  unfold in_int in Hok |- *.
  destruct Hok as (_, Hok). split; [discriminate|].
  destruct T; do 2 red in Hok |- *; [apply Hok|].
   red in Hok |- *. destruct Hok as (Hko, Hsn). split; [|apply Hsn].
    rewrite kind_ok_lift with (k:=0). rewrite eq_trm_lift_ref_fv by omega. apply Hko.

 specialize IH with (1:=Hvalok).
 unfold val_ok in Hok.
 assert (nth_error (Nat::l) 0 = value Nat) by trivial.
 specialize Hok with (1:=H).
 unfold in_int in Hok. destruct Hok as (_, Hok). do 3 red in Hok.
 destruct Hok as (Hok, _). unfold inX in Hok. simpl in Hok. rewrite El_def in Hok.
 clear j Hvalok H.
 destruct IH as (j, (Hval, Hclsd)).
 specialize inSAT_n with (1:=Hok); intros Hclsdj.
 destruct Hclsdj as (t, (HinSAT, Hclsdt)).
 exists (I.cons t j); split.
  apply vcons_add_var with (T:=Nat) (x:= i 0) (t:=t) in Hval.
   unfold val_ok in Hval |- *. intros.
   specialize Hval with (1:=H).
   revert Hval; apply in_int_morph;[|reflexivity|reflexivity|reflexivity].
    rewrite V.cons_ext with (i':=i); reflexivity.
    
   split.
    unfold inX. simpl; rewrite El_def; apply Hok.
    
    rewrite RealNat_eq; trivial.

   discriminate.

  intro n; destruct n; simpl; trivial.

 unfold val_ok in Hok.
 assert (nth_error (EQ_trm x y :: l) 0 = value (EQ_trm x y)) as HEQ0 by trivial.
 apply Hok in HEQ0. unfold in_int in HEQ0. destruct HEQ0 as (_, HEQ0).
 hnf in HEQ0. rewrite int_lift_eq in HEQ0.

 assert (val_ok l (V.shift 1 i) (I.shift 1 j)).
  unfold val_ok in Hok |- *; intros.
  specialize Hok with (n:=S n) (T:=T) (1:=H0).
  unfold in_int in Hok |- *.
  destruct Hok as (_, Hok).
  split; [discriminate|].
  destruct T; do 2 red in Hok |- *; [apply Hok|].
   red in Hok |- *. destruct Hok as (Hko, Hsn). split; [|apply Hsn].
    rewrite kind_ok_lift with (k:=0).
    rewrite eq_trm_lift_ref_fv by omega; apply Hko.
 
 specialize IH with (1:=H0).
 assert (nth_error (EQ_trm x y::l) 0 = value (EQ_trm x y)) by trivial.
 unfold val_ok in Hok; specialize Hok with (1:=H1).
 unfold in_int in Hok; destruct Hok as (_, Hok).
 destruct Hok as (Hi0, _). unfold inX in Hi0.
 rewrite int_lift_eq in Hi0. simpl int in Hi0 at 1.
 
 assert (typ l (EQ_trm x y) prop) as HEQ by (apply EQ_trm_typ; trivial).
 apply (prf_irr_set _ _ HEQ _ _ _ H0) in Hi0. clear H1.
 
 destruct IH as (j', (Hval, Hclsd)).
 exists (I.cons (j 0) j'). split.
  unfold val_ok. intros. rewrite <- V.cons_ext with (x:=i 0) (i:=V.shift 1 i) by reflexivity.
  revert n T H1; fold (val_ok (EQ_trm x y::l) (V.cons (i 0) (V.shift 1 i)) (I.cons (j 0) j')).
  apply vcons_add_var; [trivial|trivial|discriminate].

   intro n. destruct n; simpl; [|apply Hclsd].
   unfold closed_pure_trm in Hclsd |- *. intro k. intro H'.
   apply tm_closed in H. apply H. intro n. apply Hclsd.
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



Lemma EQ_refl_prf : forall e x y t, 
  valid_ctxt e ->
  typ e x sort ->
  typ e y sort ->
  typ e t (EQ_trm x y) ->
  typ e (EQ_refl x) (EQ_trm x y).
intros e x y t ve Hx Hy Ht.
apply EQ_trm_elim in Ht; [|apply valid_ctxt_wf_clsd| |]; trivial.
apply typ_abs; [| |discriminate].
 left. apply typ_prod; [left; trivial|left; apply typ_sort|apply typ_prop].

 apply typ_abs; [| |discriminate].
  right. setoid_replace prop with (subst (lift 1 x) prop) using relation eq_trm at 2; [|
  simpl; split; red; reflexivity].
  apply typ_app with (V:=sort); [| |discriminate|discriminate].
   setoid_replace sort with (lift 1 sort) using relation eq_trm at 2;[
     apply weakening; trivial|simpl; split; red; reflexivity].
   
   setoid_replace (Prod sort prop) with (lift 1 (Prod sort prop)) using relation eq_trm at 2; [
     apply typ_var; trivial|].
    simpl; split; red; reflexivity.

  apply typ_conv with (T:=(App (Ref 1) (lift 2 x))); [| |discriminate|discriminate].
   setoid_replace (App (Ref 1) (lift 2 x)) with (lift 1 (App (Ref 0) (lift 1 x))) using relation eq_trm.
    apply typ_var; trivial.
   
    unfold lift. rewrite red_lift_app. fold (lift 2 x). fold (lift 1 x). fold (lift 1 (lift 1 x)).
    rewrite split_lift. rewrite eq_trm_lift_ref_fv; [reflexivity|omega].

   apply eq_typ_app; [reflexivity|].
   do 2 red; intros.
   assert (val_ok e (V.shift 2 i) (I.shift 2 j)).
    unfold val_ok in H |- *; intros.
     assert (nth_error (App (Ref 0) (lift 1 x) :: Prod sort prop :: e) (S (S n)) = value T) by trivial.
     specialize H with (1:=H1). unfold in_int in H |- *. split; [discriminate|].
      destruct H as (_, H). destruct T; do 2 red in H |- *.
       revert H; apply real_morph.
        unfold V.shift; simpl; reflexivity.
        
        do 2 rewrite split_lift with (n:= S _); rewrite split_lift with (n:= n).
        do 4 rewrite int_lift_eq. rewrite V.shift_split with (n:=1); reflexivity.

        unfold I.shift; trivial.
        
       red in H |- *. destruct H.
       split.
        do 2 rewrite kind_ok_lift with (k:=0).
        do 2 rewrite eq_trm_lift_ref_fv by omega.
        apply H. apply H2.

   apply Ht in H0. red in H0. do 2 rewrite split_lift with (n:=1).
   do 4 rewrite int_lift_eq.
   rewrite V.shift_split with (n:=1) in H0; trivial.
Qed.

 