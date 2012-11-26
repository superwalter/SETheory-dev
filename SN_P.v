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
| vcconsP : forall l t x y, valid_ctxt l -> typ l x Nat ->
  typ l y Nat -> typ l t (EQ_trm x y) -> valid_ctxt ((EQ_trm x y)::l).


Lemma valid_ctxt_wf_clsd : forall e, valid_ctxt e -> wf_clsd_env e.
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
 apply red_typ with (1:=Hval) in H; [|discriminate].
 destruct H as (_, Ht).
 exists (I.cons (tm j' t) j'). split.
  apply vcons_add_var with (x:= int (V.shift 1 i) t) (t:=tm j' t) (T:=EQ_trm x y) 
    in Hval; [|trivial|discriminate].
   destruct Ht as (Ht, _). unfold inX in Ht.
   apply (prf_irr_set _ _ HEQ _ _ _ H0) in Ht.
   unfold val_ok in Hval |- *; intros.
   apply Hval in H. revert H; apply in_int_morph; [|reflexivity|reflexivity|reflexivity].
   rewrite V.cons_ext with (i':=i); [|rewrite Hi0, Ht|]; reflexivity.

   intro n. destruct n; simpl; [|apply Hclsd].
   unfold closed_pure_trm in Hclsd |- *. intro k. intro H.
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