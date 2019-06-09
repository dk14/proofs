Inductive bin : Type :=
  | Z
  | A (n : bin)
  | B (n : bin).

Fixpoint incr (m:bin) : bin :=
  match m with
  | Z => B Z
  | B x => A (incr x)
  | A x => B x         
  end.

Fixpoint bin_to_nat (m:bin) : nat :=
  match m with
  | Z => O
  | B Z => 1
  | B x => 1 + 2 * (bin_to_nat x)
  | A x => 2 * (bin_to_nat x)
  end.

Theorem test: forall code: bin, bin_to_nat(incr(code)) = 1 + bin_to_nat(code).
Proof.
intros n.
induction n as [|n'1 IHn1|n'2 IHn2].
- simpl. reflexivity.
- destruct n'1; repeat auto.
- destruct n'2.
  * reflexivity.
  * destruct n'2; repeat (simpl; auto).
  * simpl.
    simpl in IHn2.
    rewrite -> IHn2.
    destruct n'2; repeat (simpl; auto).
Qed.



