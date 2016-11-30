Require Import Lists.List.

(******************************************************************************)
(*
Stuff about permutations. Runs under Coq version 8.4p16.

Permutations are useful in stating the correctness of sorting algorithms: the
output must be a sorted permutation of the input.

The main results are that the permutation relation (Perm) is reflexive
(permRefl), symmetric (permSymm), and transitive (permTrans). These seem to
require a lot more mechanism than I had expected. I assume there are less
verbose proofs out there somewhere, but I didn't look for them.
*)

Notation " [ ] " := nil : list_scope.
Notation " [ x ] " := (cons x nil) : list_scope.
Notation " [ x ; .. ; y ] " := (cons x .. (cons y nil) ..) : list_scope.

(******************************************************************************)
(* Useful lemmas about lists **************************************************)

Lemma nilApp: forall {X} (l0 l1: list X),
  l0 ++ l1 = [] ->
  (l0 = [] /\ l1 = []).
Proof.
  destruct l0; destruct l1; intros; split.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - inversion H.
  - rewrite app_nil_r in H. apply H.
  - reflexivity.
  - inversion H.
  - inversion H.
Qed.

Lemma headShift: forall {X} (l0 l1: list X) (x: X),
  (l0 ++ [x]) ++ l1 = l0 ++ x :: l1.
Proof.
  induction l0; intros.
  - reflexivity.
  - specialize (IHl0 l1 x). simpl. rewrite IHl0. reflexivity.
Qed.
                   
Lemma splitInsertLocations: forall {X} (l2 l0 l3 l1: list X) (x: X),
  l0 ++ l1 = l2 ++ x :: l3 ->
  ((l0 = l2 /\ l1 = x :: l3) \/
   (exists l, l0 = l2 ++ x :: l /\ l ++ l1 = l3) \/
   (exists l, l0 ++ l = l2 /\ l1 = l ++ x :: l3)).
Proof.
  induction l2; destruct l0; intros.
  - right. right. exists []. split.
    + reflexivity.
    + simpl in H. rewrite H. reflexivity.
  - inversion H; subst. right. left. exists l0. split.
    + reflexivity.
    + reflexivity.
  - right. right. exists (a :: l2). split.
    + reflexivity.
    + simpl in H. apply H.
  - inversion H. subst. apply IHl2 in H2. inversion H2; inversion H0; subst.
    + left. split.
      * reflexivity.
      * reflexivity.
    + inversion H1 as [l H3]. inversion H3. right. left. exists l. split.
      * rewrite H4. reflexivity.
      * apply H5.
    + inversion H1 as [l H3]. inversion H3. right. right. exists l. split.
      * rewrite <- H4. reflexivity.
      * apply H5.
Qed.

Lemma splitInsertTwoHeads: forall {X} (l0 l1 l2 l3: list X) (x01 x23: X),
  l0 ++ x01 :: l1 = l2 ++ x23 :: l3 ->
  ((x01 = x23 /\ l0 = l2 /\ l1 = l3) \/
   (exists l, l0 = l2 ++ x23 :: l /\ l ++ x01 :: l1 = l3) \/
   (exists l, l0 ++ x01 :: l = l2 /\ l1 = l ++ x23 :: l3)).
Proof.
  intros. apply (splitInsertLocations l2 l0 l3 (x01 :: l1) x23) in H. 
  inversion H.
  - inversion H0. inversion H2. subst. left. split.
    + reflexivity.
    + split; reflexivity.
  - inversion H0. inversion H1 as [l]. inversion H2; subst.
    + right. left. exists l. apply H2.
    + inversion H1 as [l]. destruct l.
      * inversion H2. rewrite app_nil_r in H3. inversion H4; subst.
        left. { split.
        - reflexivity.
        - split; reflexivity.
        }
      * inversion H2. simpl in H4. inversion H4; subst.
        right. right. exists l. split; reflexivity.
Qed.

Lemma in_middle: forall {X} (l0 l1: list X) (x: X),
  In x (l0 ++ x :: l1).
Proof.
  induction l0; intros.
  - simpl. left. reflexivity.
  - simpl. right. apply IHl0.
Qed.
                   
Lemma in_app_iff : forall A l l' (a:A),
  In a (l++l') <-> In a l \/ In a l'.
Proof.
  intros. split; intros; induction l.
  - simpl in H. right. apply H.
  - simpl in H. inversion H.
    + rewrite H0. left. simpl. left. reflexivity.
    + simpl. apply or_assoc. right. apply IHl. apply H0.
  - simpl. inversion H.
    + inversion H0.
    + apply H0.
  - simpl. inversion H.
    + inversion H0.
      * rewrite H1. left. reflexivity.
      * right. apply IHl. left. apply H1.
    + right. apply IHl. right. apply H0.
Qed.

Lemma in_app_insert: forall {X} (l0 l1: list X) (x x0: X),
  In x (l0 ++ l1) -> In x (l0 ++ x0 :: l1).
Proof.
  intros.
  - apply in_app_iff in H. inversion H.
    + apply in_app_iff. left. apply H0.
    + replace (l0 ++ x0 :: l1) with ((l0 ++ [x0]) ++ l1).
      apply in_app_iff. right. apply H0.
      * rewrite <- app_assoc. reflexivity.
Qed.

(******************************************************************************)
(* Permutations ***************************************************************)

Inductive Perm {X}: list X -> list X -> Prop :=
  | permNil:
      Perm [] []
  | permHead: forall (l l0 l1: list X) (x: X),
      Perm l (l0 ++ l1) -> Perm (x :: l) (l0 ++ x :: l1).

Theorem permInsert: forall {X} (l0 l1 l2 l3: list X) (x: X),
  Perm (l0 ++ l1) (l2 ++ l3) -> Perm (l0 ++ x :: l1) (l2 ++ x :: l3).
Proof.
  induction l0; intros.
  - apply permHead. apply H.
  - inversion H. subst.
    symmetry in H3. apply splitInsertLocations in H3.
    inversion H3.
    + inversion H0; subst. simpl.
      replace (l4 ++ x :: a :: l5) with ((l4 ++ [x]) ++ a :: l5).
      apply permHead.
      apply (IHl0 l1 l4 l5 x) in H1.
      replace ((l4 ++ [x]) ++ l5) with (l4 ++ x :: l5).
      apply H1.
      * rewrite headShift. reflexivity.
      * rewrite headShift. reflexivity.
    + inversion H0. inversion H2 as [l6]. inversion H4; subst.
      replace (l4 ++ l6 ++ l3) with ((l4 ++ l6) ++ l3) in H1.
      apply (IHl0 l1 (l4 ++ l6) l3 x) in H1.
      simpl.
      replace ((l4 ++ a :: l6) ++ x :: l3) with (l4 ++ a :: (l6 ++ x :: l3)).
      apply permHead.
      replace (l4 ++ l6 ++ x :: l3) with ((l4 ++ l6) ++ x :: l3).
      apply H1.
      * rewrite app_assoc. reflexivity.
      * rewrite <- app_assoc. simpl. reflexivity.
      * rewrite app_assoc. reflexivity.
      * inversion H2 as [l6]. inversion H4; subst.
        simpl.
        replace (l2 ++ x :: l6 ++ a :: l5) with ((l2 ++ x :: l6) ++ a :: l5).
        apply permHead.
        rewrite <- app_assoc in H1. apply (IHl0 l1 l2 (l6 ++ l5) x) in H1.
        rewrite <- app_assoc. simpl. apply H1.
        rewrite <- app_assoc. simpl. reflexivity.
Qed.
  
Theorem permRefl: forall {X} (l: list X),
  Perm l l.
Proof.
  induction l.
  - apply permNil.
  - replace (a :: l) with ([] ++ a :: l). apply permInsert. apply IHl.
    + reflexivity.
Qed.

Theorem permSymm: forall {X} (l0 l1: list X),
  Perm l0 l1 -> Perm l1 l0.
Proof.
  intros. induction H.
  - apply permNil.
  - replace (x :: l) with ([] ++ x :: l). apply permInsert. apply IHPerm.
    + reflexivity.
Qed.

Lemma permIn: forall {X} (l0 l1: list X) (x: X),
  Perm l0 l1 -> In x l0 -> In x l1.
Proof.
  induction l0; intros.
  - inversion H0.
  - inversion H0; subst.
    + inversion H; subst. apply in_middle.
    + inversion H; subst. apply (IHl0 (l2 ++ l3) x) in H5.
      * apply in_app_insert. apply H5.
      * apply H1.
Qed.

Lemma inPerm: forall {X} (l l0 l1: list X) (x: X),
  Perm l (l0 ++ x :: l1) ->
  In x l.
Proof.
  induction l; intros.
  - inversion H. destruct l0; inversion H0.
  - inversion H; subst. apply splitInsertTwoHeads in H3. inversion H3.
    + inversion H0. inversion H4. subst. unfold In. left. reflexivity.
    + apply in_cons. inversion H0.
      * inversion H2 as [l2]. inversion H4. subst. rewrite <- app_assoc in H1.
        simpl in H1. apply IHl in H1. apply H1.
      * inversion H2 as [l2]. inversion H4. subst.
        rewrite app_assoc in H1. apply IHl in H1. apply H1.
Qed.

Lemma emptyPerm: forall {X} (l: list X),
  Perm l [] -> l = [].
Proof.
  induction l; intros.
  - reflexivity.
  - inversion H; subst.
    + destruct l1; inversion H3.
Qed.

Lemma permMove: forall {X} (l0 l1 l2: list X) (x: X),
  Perm (l0 ++ x :: l1 ++ l2) (l0 ++ l1 ++ x :: l2).
Proof.
  induction l0; intros.
  - simpl. apply permHead. apply permRefl.
  - simpl.
    assert (A: a :: l0 ++ l1 ++ x :: l2 = [] ++ a :: (l0 ++ l1 ++ x :: l2)). {
      reflexivity.
    } rewrite A. apply permHead. simpl. apply IHl0.
Qed.

Lemma permMoveRight: forall {X} (l l0 l1 l2: list X) (x: X),
  Perm l (l0 ++ x :: l1 ++ l2) ->
  Perm l (l0 ++ l1 ++ x :: l2).
Proof.
  induction l; intros; inversion H; subst.
  - destruct l0; inversion H0.
  - apply splitInsertTwoHeads in H3. inversion H3.
    + inversion H0. inversion H4. subst.
      rewrite app_assoc. apply permHead. rewrite <- app_assoc. apply H1.
    + inversion H0.
      * inversion H2 as [l3]. inversion H4. subst.
        symmetry in H6. apply splitInsertLocations in H6. { inversion H6.
        - inversion H5. subst.
          assert (L: l0 ++ l3 ++ x :: a :: l5 = (l0 ++ l3 ++ [x]) ++ a :: l5). {
            rewrite <- app_assoc. rewrite <- app_assoc. reflexivity.
          } rewrite L.
          apply permHead. rewrite <- app_assoc. rewrite <- app_assoc. simpl.
          apply IHl.
          rewrite <- app_assoc in H1. apply H1.
        - inversion H5.
          + inversion H7 as [l4]. inversion H8; subst.
            assert (L:
                l0 ++ (l3 ++ a :: l4) ++ x :: l2 =
                  (l0 ++ l3) ++ a :: (l4 ++ x :: l2)). {
              rewrite <- app_assoc. rewrite <- app_assoc. reflexivity.
            } rewrite L.
            apply permHead.
            assert (LL:
                (l0 ++ l3) ++ l4 ++ x :: l2 = l0 ++ (l3 ++ l4) ++ x :: l2). {
              rewrite <- app_assoc. rewrite <- app_assoc. reflexivity.
            } rewrite LL. apply IHl. rewrite <- app_assoc.
            rewrite <- app_assoc in H1. simpl in H1. apply H1.
          + inversion H7 as [l4]. inversion H8; subst.
            assert (L:
                l0 ++ l1 ++ x :: l4 ++ a :: l5 =
                  (l0 ++ l1 ++ x :: l4) ++ a :: l5). {
              rewrite <- app_assoc. rewrite <- app_assoc. reflexivity.
            } rewrite L. apply permHead.
            rewrite <- app_assoc. rewrite <- app_assoc. simpl.
            rewrite <- app_assoc in H1. simpl in H1.
            rewrite <- app_assoc in H1. apply IHl in H1. apply H1.
        }
      * inversion H2 as [l3]. inversion H4. subst.
        rewrite <- app_assoc. simpl. apply permHead.
        rewrite app_assoc. apply IHl. rewrite <- app_assoc. apply H1.
Qed.

Lemma permMoveLeft: forall {X} (l l0 l1 l2: list X) (x: X),
  Perm l (l0 ++ l1 ++ x :: l2) ->
  Perm l (l0 ++ x :: l1 ++ l2).
Proof.
  induction l; intros l0 l1 l2 x H; inversion H; subst.
  - destruct l0; destruct l1; inversion H0.
  - rewrite app_assoc in H3. apply splitInsertTwoHeads in H3. inversion H3.
    + inversion H0. inversion H4. subst.
      apply permHead. rewrite <- app_assoc in H1. apply H1.
    + inversion H0.
      * inversion H2 as [l3]. inversion H4. subst.
        assert (L:
            l0 ++ x :: l1 ++ l3 ++ a :: l5 =
              (l0 ++ x :: l1 ++ l3) ++ a :: l5). {
          rewrite <- app_assoc. simpl. rewrite <- app_assoc. reflexivity.
        } rewrite L. apply permHead.
        assert (LL:
            ((l0 ++ l1) ++ x :: l3) ++ l5 = l0 ++ l1 ++ x :: (l3 ++ l5)). {
          rewrite <- app_assoc. simpl. rewrite <- app_assoc.
          reflexivity.
        } rewrite LL in H1. apply IHl in H1.
        rewrite <- app_assoc. simpl. rewrite <- app_assoc. apply H1.
      * inversion H2 as [l3]. inversion H4. subst.
        symmetry in H5. apply splitInsertLocations in H5. { inversion H5.
        - inversion H6. subst.
          assert (L:
              l4 ++ x :: (a :: l3) ++ l2 = (l4 ++ [x]) ++ a :: (l3 ++ l2)). {
            simpl. rewrite <- app_assoc. reflexivity.
          } rewrite L. apply permHead. rewrite <- app_assoc. simpl.
          apply IHl in H1. apply H1.
        - inversion H6. inversion H7 as [l5].
          + inversion H8. subst.
            assert (L:
                (l4 ++ a :: l5) ++ x :: l1 ++ l2 =
                  l4 ++ a :: (l5 ++ x :: l1 ++ l2)). {
              rewrite <- app_assoc. reflexivity.
            } rewrite L. apply permHead.
            rewrite <- app_assoc in H1. rewrite app_assoc in H1.
            apply IHl in H1. rewrite <- app_assoc in H1. apply H1.
          + inversion H7 as [l5]. inversion H8. subst.
            assert (L:
                l0 ++ x :: (l5 ++ a :: l3) ++ l2 =
                  (l0 ++ x :: l5) ++ a :: (l3 ++ l2)). {
              rewrite <- app_assoc. rewrite <- app_assoc. reflexivity.
            } rewrite L. apply permHead.
            assert (LL:
                (l0 ++ l5) ++ l3 ++ x :: l2 = l0 ++ (l5 ++ l3) ++ x :: l2). {
              rewrite <- app_assoc. rewrite <- app_assoc. reflexivity.
            } rewrite LL in H1. apply IHl in H1. rewrite <- app_assoc in H1.
            rewrite <- app_assoc. simpl. apply H1.
          }
Qed.

Theorem permUninsert: forall {X} (l0 l1 l2 l3: list X) (x: X),
  Perm (l0 ++ x :: l1) (l2 ++ x :: l3) ->
  Perm (l0 ++ l1) (l2 ++ l3).
Proof.
  induction l0; intros l1 l2 l3 x H; inversion H; subst.
  - apply splitInsertTwoHeads in H3. inversion H3.
    + inversion H0. inversion H4. subst. apply H1.
    + inversion H0.
      * inversion H2 as [l]. inversion H4; subst.
        simpl. rewrite <- app_assoc in H1. simpl in H1.
        apply permMoveRight in H1. apply H1.
      * inversion H2 as [l]. inversion H4; subst.
        simpl. rewrite <- app_assoc. simpl.
        apply permMoveLeft in H1. apply H1.
  - apply splitInsertTwoHeads in H3. inversion H3.
    + inversion H0. inversion H4. subst.
      apply permSymm. simpl.
      assert (L: x :: l0 ++ l1 = [] ++ x :: l0 ++ l1). { reflexivity. }
      rewrite L. apply permMoveLeft. simpl. apply permSymm. apply H1.
    + inversion H0.
      * inversion H2 as [l]. inversion H4. subst. simpl. rewrite app_assoc.
        apply permHead.
        assert (L: (l2 ++ x :: l) ++ l5 = l2 ++ x :: (l ++ l5)). {
          rewrite <- app_assoc. reflexivity.
        } rewrite L in H1. apply IHl0 in H1. 
        rewrite <- app_assoc. apply H1.
      * inversion H2 as [l]. inversion H4. subst. rewrite <- app_assoc. simpl.
        apply permHead.
        rewrite app_assoc in H1. apply IHl0 in H1. rewrite <- app_assoc in H1.
        apply H1.
Qed.

Theorem permTrans: forall {X} (l0 l1 l2: list X),
  Perm l0 l1 -> Perm l1 l2 -> Perm l0 l2.
Proof.
  induction l0; intros l1 l2 H01 H12; inversion H01; subst.
  - apply H12.
  - inversion H12; subst.
    + destruct l3; inversion H0.
    + assert (AL15: In a (l1 ++ x :: l5)). {
        apply permSymm in H12. apply inPerm in H12. apply H12.
      }
      apply in_split in AL15. inversion AL15 as [l2]. inversion H1 as [l6].
      rewrite H3. apply permHead.
      assert (P: Perm (l3 ++ l4) (l2 ++ l6)). {
        rewrite H3 in H12. apply permUninsert in H12. apply H12.
      }
      apply (IHl0 (l3 ++ l4) (l2 ++ l6) H2 P).
Qed.