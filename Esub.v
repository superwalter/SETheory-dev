Require Import GenLemmas.

Import SN_CC_Real.
Import ZF SN CCSN.

Record esub := {
  esubi : val->val;
  esubi_morph : Proper (eq_val ==> eq_val) esubi;
  esubj : Lc.intt -> Lc.intt;
  esubj_morph : Proper (Lc.eq_intt ==> Lc.eq_intt) esubj;
  esubj_lift : (forall j k, 
    Lc.eq_intt (esubj (fun n : nat => Lc.lift_rec 1 (j n) k))
    (fun n : nat => Lc.lift_rec 1 (esubj j n) k));
  esubj_sub : (forall j k u, 
    Lc.eq_intt (esubj (fun n : nat => Lc.subst_rec u (j n) k))
    (fun n : nat => Lc.subst_rec u (esubj j n) k))}.

Definition eq_esub (es es' : esub):= 
  forall i i' j j', 
    (eq_val i i' -> eq_val (es.(esubi) i) (es'.(esubi) i')) /\
    (Lc.eq_intt j j' -> Lc.eq_intt (es.(esubj) j) (es'.(esubj) j')).

Definition esub_conv (es : esub) (i : val) (j : Lc.intt): (val * Lc.intt) := 
  ((es.(esubi) i), (es.(esubj) j)).

Definition eq_val_int (x y :(val * Lc.intt)):= eq_val (fst x) (fst y) /\ 
  Lc.eq_intt (snd x) (snd y).

Instance esub_conv_morph : 
  Proper (eq ==> eq_val ==> Lc.eq_intt ==> eq_val_int) esub_conv.
do 5 red; simpl; intros. subst y.
destruct x; simpl. rewrite H0. rewrite H1. split; reflexivity.
Qed.

Definition esub_conv_i (es : esub) (i : val) : val := (es.(esubi) i).

Instance esub_conv_i_morph : 
  Proper (eq ==> eq_val ==> eq_val) esub_conv_i.
do 6 red; simpl; intros. subst y.
destruct x; simpl. apply esubi_morph0; trivial.
Qed.

Definition esub_conv_j (es : esub) (j : Lc.intt) : Lc.intt := (es.(esubj) j).

Instance esub_conv_j_morph : 
  Proper (eq ==> Lc.eq_intt ==> Lc.eq_intt) esub_conv_j.
do 5 red; simpl; intros. subst y.
destruct x; simpl. apply esubj_morph0; trivial.
Qed.

Definition app_esub : esub -> trm -> trm.
intros es t; left.
exists (fun i => int (esub_conv_i es i) t) (fun j => tm (esub_conv_j es j) t).
do 4 red; intros. apply int_morph; try reflexivity.
 apply esub_conv_i_morph; trivial.

do 2 red; intros. apply tm_morph; try reflexivity.
 apply esub_conv_j_morph; trivial.

destruct es as (f, Hmrphf, g, Hmrphg, Hl, Hs); simpl.
red; intros. rewrite Hl.
destruct t; [destruct i; simpl; apply itm_lift0|]; trivial.

destruct es as (f, Hmrphf, g, Hmrphg, Hl, Hs); simpl.
red; intros. rewrite Hs.
destruct t; [destruct i; simpl; apply itm_subst0|]; trivial.
Defined.

Definition id_sub : esub.
exists (fun f => f) (fun f => f).
do 2 red; trivial.

do 4 red; trivial.

reflexivity.

reflexivity.
Defined.

Definition sub_cons : trm -> esub -> esub.
intros t es. 
exists (fun i => V.cons (int i t) (esub_conv_i es i))
  (fun j => I.cons (tm j t) (esub_conv_j es j)).
do 2 red; intros. apply V.cons_morph; 
  [rewrite H; reflexivity| apply esub_conv_i_morph; trivial].

do 4 red; intros; rewrite H; trivial.

do 2 red; intros. destruct es as (f, Hmrphf, g, Hmrphg, Hl, Hs); simpl. rewrite Hl. 
destruct t; [destruct i; simpl; rewrite itm_lift0|]; destruct a; simpl; trivial.

do 2 red; intros. destruct es as (f, Hmrphf, g, Hmrphg, Hl, Hs); simpl. rewrite Hs. 
destruct t; [destruct i; simpl; rewrite itm_subst0|]; destruct a; simpl; trivial.
Defined.

Definition typ_esub env1 es env2 := 
  forall i j, val_ok env1 i j -> 
    val_ok env2 (esub_conv_i es i) (esub_conv_j es j).

Lemma esub_typ_id : forall env, typ_esub env id_sub nil.
do 2 red; intros. destruct n; simpl in H0; discriminate.
Qed.

Lemma esub_typ_cons : forall env1 env2 es t A,
  A <> kind ->
  typ_esub env1 es env2 ->
  typ env1 t (app_esub es A) ->
  typ_esub env1 (sub_cons t es) (A::env2).
red; intros; simpl.
apply vcons_add_var; [apply H0| |]; trivial.
 apply red_typ with (1:=H2) in H1; [|discriminate].
 destruct H1 as (_, H1). simpl int in H1; trivial.
Qed.

Lemma explicit_sub_typ : forall env1 env2 es t A, 
  A <> kind ->
  typ_esub env1 es env2 ->
  typ env2 t A -> 
  typ env1 (app_esub es t) (app_esub es A).
red; intros.
apply H0 in H2.
apply H1 in H2.
apply in_int_not_kind in H2; trivial.
apply in_int_intro; [|discriminate|discriminate].
simpl int; simpl tm in H2 |- *; trivial.
Qed.

Lemma explicit_sub_eq_typ : forall env1 env2 es x y,
  x <> kind ->
  y <> kind ->
  typ_esub env1 es env2 ->
  eq_typ env2 x y ->
  eq_typ env1 (app_esub es x) (app_esub es y).
red; intros. 
apply H1 in H3. 
apply H2 in H3; simpl; trivial.
Qed.