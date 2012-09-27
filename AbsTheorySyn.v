Require Import List.
Require Import Compare_dec.
Require Import Omega.

(******************************************************************************************)
(******************************************************************************************)
(*This file gives the syntax model of the theory*)
(******************************************************************************************)
(******************************************************************************************)



(******************************************************************************************)
(*This model describes the abstract signature of the theory,*)
(*and defines some operations on the signature*)
(******************************************************************************************)
Module Type TheorySig.

(*The set of first-order terms*)
Parameter foterm : Set.

(*Lift term*)
Parameter lift_trm_rec : foterm -> nat -> nat -> foterm.
Definition lift_trm t n := lift_trm_rec t n 0.

(*Substitute term*)
Parameter subst_trm_rec : foterm -> foterm -> nat -> foterm.
Definition subst_trm M N := subst_trm_rec M N 0.

(*Free variables are calculated due to need of definition of well-typed terms*)
(*fv_trm_rec list all free variables in a term with a binder k*)
(*The free variables are used for indexes in a context in which the term is well typed*)
(*So, the free variables are subtracted by the binder k*)
Parameter fv_trm_rec : foterm -> (*k*)nat -> list nat.
Definition fv_trm t := fv_trm_rec t 0.

End TheorySig.


(******************************************************************************************)
(*This model defines the first-order language on top of signatures*)
(*Actually shows possible logic formulas*)
(******************************************************************************************)
Module FoLang (M : TheorySig).

Import M.

Inductive foformula :=
| eq_fotrm : foterm -> foterm -> foformula
| TF   : foformula
| BF   : foformula
| neg : foformula -> foformula
| conj : foformula -> foformula -> foformula
| disj : foformula -> foformula -> foformula
| implf : foformula -> foformula -> foformula
| fall : foformula -> foformula
| exst : foformula -> foformula.

Fixpoint lift_fml_rec f n k:=
  match f with
    | eq_fotrm x y => eq_fotrm (lift_trm_rec x n k) (lift_trm_rec y n k)
    | TF => TF
    | BF => BF
    | neg f' => neg (lift_fml_rec f' n k)
    | conj A B => conj (lift_fml_rec A n k) (lift_fml_rec B n k)
    | disj A B => disj (lift_fml_rec A n k) (lift_fml_rec B n k)
    | implf A B => implf (lift_fml_rec A n k) (lift_fml_rec B n k)
    | fall A => fall (lift_fml_rec A n (S k))
    | exst A => exst (lift_fml_rec A n (S k))
  end.

Definition lift_fml t n := lift_fml_rec t n 0.

Fixpoint subst_fml_rec f N n :=
  match f with
    | eq_fotrm x y => eq_fotrm (subst_trm_rec x N n) (subst_trm_rec y N n)
    | TF => TF
    | BF => BF
    | neg f => neg (subst_fml_rec f N n)
    | conj f1 f2 => conj (subst_fml_rec f1 N n) (subst_fml_rec f2 N n)
    | disj f1 f2 => disj (subst_fml_rec f1 N n) (subst_fml_rec f2 N n)
    | implf f1 f2 => implf (subst_fml_rec f1 N n) (subst_fml_rec f2 N n)
    | fall f => fall (subst_fml_rec f N (S n))
    | exst f => exst (subst_fml_rec f N (S n))
  end.

Definition subst_fml f N := subst_fml_rec f N 0.

Fixpoint fv_fml_rec f k : list nat :=
  match f with
    | eq_fotrm t1 t2 => (fv_trm_rec t1 k) ++ (fv_trm_rec t2 k)
    | TF => nil
    | BF => nil
    | neg f0 => fv_fml_rec f0 k
    | conj f1 f2 => (fv_fml_rec f1 k) ++ (fv_fml_rec f2 k)
    | disj f1 f2 => (fv_fml_rec f1 k) ++ (fv_fml_rec f2 k)
    | implf f1 f2 => (fv_fml_rec f1 k) ++ (fv_fml_rec f2 k)
    | fall f0 => (fv_fml_rec f0 (S k))
    | exst f0 => (fv_fml_rec f0 (S k))
  end.

Definition fv_fml f := fv_fml_rec f 0.

End FoLang.


(*This model defines the axioms of the Theory*)
Module Type TheoryAx (M : TheorySig).

Include (FoLang M).

(*Theory Axioms*)
Parameter ax : list (option foformula) -> foformula -> Prop.

End TheoryAx.


(******************************************************************************************)
(*This model defines the first-order theory with 3 parts :*)
(*1. The first-order language defined above*)
(*2. The axioms*)
(*3. Derivation rules*)
(******************************************************************************************)
Module TheorySyn (M : TheorySig) (MM : TheoryAx M).

Import M MM.

Definition wf_trm (hyp:list (option foformula)) t := 
  forall n, In n (fv_trm t) -> nth_error hyp n = Some None.

Definition wf_fml (hyp:list (option foformula)) f := 
  forall n, In n (fv_fml f) -> nth_error hyp n = Some None.

Inductive deriv : list (option foformula) -> foformula -> Prop :=
| hyp_judge : forall f hyp n, 
  nth_error hyp n = Some (Some f) ->
  wf_fml hyp (lift_fml f (S n)) ->
  deriv hyp (lift_fml f (S n))
| ax_intro : forall f hyp, ax hyp f -> deriv hyp f
| true_intro : forall hyp, deriv hyp TF
| false_elim : forall hyp f, deriv hyp BF -> wf_fml hyp f -> deriv hyp f
| neg_intro : forall hyp f, deriv hyp (implf f BF) -> deriv hyp (neg f)
| neg_elim : forall hyp f, deriv hyp (neg f) -> deriv hyp (implf f BF)
| conj_intro : forall hyp f1 f2, 
  deriv hyp f1 -> deriv hyp f2 -> deriv hyp (conj f1 f2)
| conj_elim1 : forall hyp f1 f2,
  deriv hyp (conj f1 f2) -> deriv hyp f1
| conj_elim2 : forall hyp f1 f2,
  deriv hyp (conj f1 f2) -> deriv hyp f2
| disj_intro1 : forall hyp f1 f2, 
  deriv hyp f1 -> wf_fml hyp f2 -> deriv hyp (disj f1 f2)
| disj_intro2 : forall hyp f1 f2, 
  wf_fml hyp f1 ->
  deriv hyp f2 -> deriv hyp (disj f1 f2)
| disj_elim : forall hyp f1 f2 f3,
  deriv hyp (disj f1 f2) -> deriv (Some f1::hyp) (lift_fml f3 1) -> 
  deriv (Some f2::hyp) (lift_fml f3 1) -> deriv hyp f3
| impl_intro : forall hyp f1 f2,
  wf_fml hyp f1 ->
  deriv ((Some f1)::hyp) (lift_fml f2 1) -> deriv hyp (implf f1 f2)
| impl_elim : forall hyp f1 f2,
  deriv hyp (implf f1 f2) -> deriv hyp f1 -> deriv hyp f2
| fall_intro : forall hyp f,
  deriv (None::hyp) f -> deriv hyp (fall f)
| fall_elim : forall hyp f u, 
  wf_trm hyp u -> deriv hyp (fall f) -> deriv hyp (subst_fml f u)
| exst_intro : forall hyp f N, wf_trm hyp N -> 
  deriv hyp (subst_fml f N) -> deriv hyp (exst f)
| exst_elim : forall hyp f f1, 
  deriv hyp (exst f) -> 
  deriv (Some f::None::hyp) (lift_fml f1 2) -> deriv hyp f1.

(*Any derivable formula should well typed*)
Parameter deriv_well_typed : forall hyp f, deriv hyp f -> wf_fml hyp f.

Parameter wf_weakening : forall hyp t f',
  wf_fml (t :: hyp) (lift_fml f' 1) ->
  wf_fml hyp f'.

End TheorySyn.