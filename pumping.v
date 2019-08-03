Require Import Coq.Lists.List.
Import List.ListNotations.


Inductive reg_exp {T : Type} : Type :=
  | EmptySet
  | EmptyStr
  | Char (t : T)
  | App (r1 r2 : reg_exp)
  | Union (r1 r2 : reg_exp)
  | Star (r : reg_exp).

Inductive exp_match {T} : list T -> reg_exp -> Prop :=
  | MEmpty : exp_match [] EmptyStr
  | MChar x : exp_match [x] (Char x)
  | MApp s1 re1 s2 re2
             (H1 : exp_match s1 re1)
             (H2 : exp_match s2 re2) :
             exp_match (s1 ++ s2) (App re1 re2)
  | MUnionL s1 re1 re2
                (H1 : exp_match s1 re1) :
                exp_match s1 (Union re1 re2)
  | MUnionR re1 s2 re2
                (H2 : exp_match s2 re2) :
                exp_match s2 (Union re1 re2)
  | MStar0 re : exp_match [] (Star re)
  | MStarApp s1 s2 re
                 (H1 : exp_match s1 re)
                 (H2 : exp_match s2 (Star re)) :
                 exp_match (s1 ++ s2) (Star re).

Notation "s =~ re" := (exp_match s re) (at level 80).

Lemma MStar1 :
  forall T s (re : @reg_exp T) ,
    s =~ re ->
    s =~ Star re.
Proof.
  intros T s re H.
  rewrite <- (app_nil_r s).
  apply (MStarApp s [] re).
  - apply H.
  - apply MStar0.
Qed.

Lemma star_app: forall T (s1 s2 : list T) (re : reg_exp),
  s1 =~ Star re ->
  s2 =~ Star re ->
  s1 ++ s2 =~ Star re.
Proof.
  intros T s1 s2 re H1.
  remember (Star re) as re'.
  generalize dependent s2.
  induction H1
    as [|x'|s1 re1 s2' re2 Hmatch1 IH1 Hmatch2 IH2
        |s1 re1 re2 Hmatch IH|re1 s2' re2 Hmatch IH
        |re''|s1 s2' re'' Hmatch1 IH1 Hmatch2 IH2].
  - (* MEmpty *) discriminate.
  - (* MChar *) discriminate Heqre'.
  - (* MApp *) discriminate.
  - (* MUnionL *) discriminate.
  - (* MUnionR *) discriminate.
  - (* MStar0 *)
    injection Heqre'. intros Heqre'' s H. simpl. apply H.
  - (* MStarApp *)
    injection Heqre'. intros H0.
    intros s2 H1. rewrite <- app_assoc.
    apply MStarApp.
    + apply Hmatch1.
    + apply IH2.
      * rewrite H0. reflexivity.
      * apply H1.
Qed.

Fixpoint pumping_constant {T} (re : @reg_exp T) : nat :=
  match re with
  | EmptySet => 0
  | EmptyStr => 1
  | Char _ => 2
  | App re1 re2 =>
      pumping_constant re1 + pumping_constant re2
  | Union re1 re2 =>
      pumping_constant re1 + pumping_constant re2
  | Star _ => 1
  end.

Fixpoint napp {T} (n : nat) (l : list T) : list T :=
  match n with
  | 0 => []
  | S n' => l ++ napp n' l
  end.

Lemma napp_plus: forall T (n m : nat) (l : list T),
  napp (n + m) l = napp n l ++ napp m l.
Proof.
  intros T n m l.
  induction n as [|n IHn].
  - reflexivity.
  - simpl. rewrite IHn, app_assoc. reflexivity.
Qed.


Require Import Coq.omega.Omega.
Require Export Logic.

Lemma sum_le: forall (n1 n2 n3 n4 : nat), n1 + n2 <= n3 + n4 -> n1 <= n3 \/ n2 <= n4.
Proof.
  intros n1 n2 n3 n4 H.
  omega.
Qed.

Lemma sum_le2: forall (n1 n2 n3 : nat), n1 + n2 <= n3 -> n1 <= n3 /\ n2 <= n3.
Proof.    
  intros n1 n2 n3 H. split.
  - omega.
  - omega.
Qed.

Lemma length_le: forall T (s1 s2 : list T), 1 <= length (s1 ++ s2) -> 1 <= length s1 \/ 1 <= length s2.
Proof.
  intros T s1 s2 H.
  rewrite app_length in H.
  omega.
Qed.

Lemma pumping : forall T (re : @reg_exp T) s,
  s =~ re ->
  pumping_constant re <= length s ->
  exists s1 s2 s3,
    s = s1 ++ s2 ++ s3 /\
    s2 <> [] /\
    forall m, s1 ++ napp m s2 ++ s3 =~ re.

Proof.
  intros T re s Hmatch.
  induction Hmatch
    as [ | x | s1 re1 s2 re2 Hmatch1 IH1 Hmatch2 IH2
       | s1 re1 re2 Hmatch IH | re1 s2 re2 Hmatch IH
       | re | s1 s2 re Hmatch1 IH1 Hmatch2 IH2 ].
  - simpl. omega.
  - simpl. omega.
  - simpl. rewrite app_length. intro H.
    apply sum_le in H. destruct H.
    + apply IH1 in H.
      destruct H as [x0 [x1 [x2]]].
      destruct H as [Hs [Hx Happ]]. clear IH1. clear IH2.
      exists x0, x1, (x2 ++ s2). split.
      * rewrite Hs. repeat rewrite <- app_assoc. reflexivity.
      * split.
        ** trivial.
        ** intros m. rewrite app_assoc. rewrite app_assoc. apply MApp.
           *** rewrite <- app_assoc. apply Happ.
           *** apply Hmatch2.
    + apply IH2 in H.
      destruct H as [x0 [x1 [x2]]].
      destruct H as [Hs [Hx Happ]]. clear IH1. clear IH2.
      exists (s1 ++ x0), x1, x2. split.
      * rewrite Hs. repeat rewrite <- app_assoc. trivial.
      * split.
        ** apply Hx.
        ** intros m. repeat rewrite <- app_assoc. apply MApp.
           *** apply Hmatch1.
           *** apply Happ.      
  - simpl. intros H. apply sum_le2 in H. destruct H. apply IH in H. clear IH. clear H0.
    destruct H as [x1 [x2 [x3]]].
    destruct H as [H0 [H1 H2]].
    exists x1, x2, x3. split.
    + apply H0.
    + split.
      * apply H1.
      * intros m. apply MUnionL. apply H2.
  - simpl. intros H. rewrite plus_comm in H. apply sum_le2 in H.
    destruct H. apply IH in H. clear IH. clear H0.
    destruct H as [x1 [x2 [x3]]].
    destruct H as [H0 [H1 H2]].
    exists x1, x2, x3. split.
    + apply H0.
    + split.
      * apply H1.
      * intros m. apply MUnionR.
        apply H2.
  - simpl. omega.
  - simpl in *. intros H. apply length_le in H.
    destruct H.
    * exists [], s1,s2. split.
      ** simpl. trivial.
      ** split.
         *** induction s1.
             **** inversion H.
             **** unfold not. intros HH. inversion HH.
         *** intros m. simpl. apply star_app.
             **** induction m.
                  ***** simpl. apply MStar0.
                  ***** simpl. apply star_app. apply MStar1. apply Hmatch1. apply IHm.
             **** apply Hmatch2.
    * apply IH2 in H.
      destruct H as [x1 [x2 [x3]]].
      destruct H as [H0 [H1 H2]].
      exists (s1 ++ x1), x2, x3.
      split.
      ** rewrite H0. repeat rewrite <- app_assoc. trivial.
      ** split.
        *** apply H1.
        *** intros m. rewrite <- app_assoc.  apply MStarApp.
          **** apply Hmatch1.
          **** apply H2.
Qed.

    
