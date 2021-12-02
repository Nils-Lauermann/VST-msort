Require Import Equations.Equations.
Require Import Coq.Sorting.Sorted.
Require Import Permutation.
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.

 Definition I_cmp op x y :=
  match x, y with
  | Vint x', Vint y' => Int.cmp op x' y' = true
  | _, _ => False
  end.

 Definition I_cmp' op x y := Int.cmp op x y.

 Definition I_min op x y :=
  match x, y with
  | Vint x', Vint y' => if Int.cmp op x' y' then x' else y'
  | _, _ => ((Int.repr 0))
  end.

 Definition sublist := 
  fun {A : Type} (lo hi : nat) (al : list A) =>
    skipn (lo) (firstn (hi) al).

 Lemma append_sorted X (x:X) (L : list X) cmp:
  Sorted cmp L -> Forall (fun a : X => cmp a x) L -> Sorted cmp (L++[x]).
 Proof.
  intros.
  induction L.
  - cbn. repeat constructor.
  - cbn in *. destruct L; cbn.
    + eapply Sorted_cons; repeat constructor.
      dependent elimination H; dependent elimination H0; auto.
    + cbn in *. eapply Sorted_cons.
      { eapply IHL; [dependent elimination H;easy|]. dependent elimination H0. easy. }
      { dependent elimination H. dependent elimination h. eapply HdRel_cons. easy. }
Qed.

 Lemma Exists_nth {X} (A : list X) x y:
  (x < length A)%nat -> {a | nth x A y = a}.
 Proof.
  revert x.
  induction A; [cbn in *;lia|].
  destruct x; [cbn; intros; eauto|].
  intros.
  cbn in *.
  assert (x < Datatypes.length (A))%nat by lia.
  now specialize (IHA x H0).
 Qed.

 Lemma Z_nat_lt_equiv x y:
  (x < y)%nat <-> (Z.of_nat x < Z.of_nat y).
 Proof.
   intros.
   apply conj; lia.
 Qed.

 Lemma Z_nat_ge_equiv x y:
 (x >= y)%nat <-> (Z.of_nat x >= Z.of_nat y).
 Proof.
  intros.
  apply conj; lia.
 Qed.

 Lemma Z_nat_succ x:
  Z.of_nat (S x) = 1 + Z.of_nat x.
 Proof.
   induction x; lia.
 Qed.

 Lemma Zlength_length_eq {X} (L : list X):
  Zlength L = Z.of_nat (length L).
 Proof.
   induction L;  [cbn; easy|].
   cbn -[Z.of_nat Zlength].
   erewrite Z_nat_succ.
   rewrite <- IHL.
   erewrite Zlength_cons.
   lia.
 Qed.

 Lemma Zlength_length_eq2 {X} (L : list X):
  Z.to_nat (Zlength L) = (length L).
 Proof.
  induction L;  [cbn; easy|].
  cbn -[Z.of_nat Zlength].
  rewrite Zlength_length_eq.
  erewrite nat_of_Z_eq.
  reflexivity.
 Qed.

 Lemma Znth_nth_eq {X} (L : list X) n (x : X):
  (n < length L)%nat -> nth n L x = @Znth X x (Z.of_nat n) L.
 Proof.
  unfold Znth.
  destruct (zlt (Z.of_nat n) 0); [induction n; lia|cbn].
  erewrite Nat2Z.id.
  easy.
 Qed.

 Lemma sublist_succ_append {X} (A : list X) n m x:
  (n <= m < length A)%nat -> sublist n (S m) A = sublist n m A ++ [nth m A x].
 Proof.
   revert n m.
   induction A; [cbn in *; lia|].
   destruct m, n; cbn; [easy|cbn in *;lia| |]; intros.
   - f_equal. specialize (IHA 0%nat m).
     assert ((0 <= m < Datatypes.length A)%nat) by lia.
     specialize (IHA H0).
     cbn in *. auto.
   - assert (n <= m < Datatypes.length A)%nat by lia.
     specialize (IHA n m H0).
     unfold sublist in *.
     cbn in *.
     eauto.
 Qed.
   

 Lemma sublist_permutation {X} (A B C : list X) x y:
 (x < length A)%nat -> (Permutation (sublist 0 x A ++ B) (C))
  -> Permutation (sublist 0 (S x) A ++ B) (C ++ [nth x A y]).
 Proof.
   revert x C.
   destruct A; intros; [cbn in H; lia|].
   erewrite sublist_succ_append; [|lia].
   pose (Exists_nth (x::A) x0 y H).
   destruct s.
   rewrite e in *.
   destruct x0.
   - cbn in *. pose (Permutation_cons_append B x1).
     eapply (@Permutation_trans _ (x1 :: B) (B ++ [x1]) _ p).
     now eapply Permutation_app_tail.
   - cbn in H.
     assert ((x0 < Datatypes.length A)%nat) by lia.
     pose (Permutation_app_swap_app (sublist 0 (S x0) (x :: A)) [x1] B).
     erewrite <- app_assoc.
     eapply (@Permutation_trans _ (sublist 0 (S x0) (x :: A) ++ [x1] ++ B)  ([x1] ++ sublist 0 (S x0) (x :: A) ++ B) (C ++ [x1]) p).
     pose (Permutation_app_comm [x1] C).
     refine (@Permutation_trans _ ([x1] ++ sublist 0 (S x0) (x :: A) ++ B) ([x1] ++ C) (C ++ [x1]) _ p0).
     cbn -[sublist].
     eapply perm_skip.
     easy.
 Qed.

 Lemma sublist_permutation2 {X} (A B C : list X) x y:
  (x < length B)%nat -> (Permutation (A ++ sublist 0 x B) (C))
  -> Permutation (A ++ sublist 0 (S x) B) (C ++ [nth x B y]).
 Proof.
  intros.
  epose (sublist_permutation B A C x y H).
  epose (Permutation_app_comm (sublist 0 x B) A ).
  epose (@Permutation_trans _ (sublist 0 x B ++ A) (A ++ sublist 0 x B) C p0 H0).
  specialize (p p1).
  epose (Permutation_app_comm A (sublist 0 (S x) B)).
  eapply (@Permutation_trans _ (A ++ sublist 0 (S x) B) (sublist 0 (S x) B ++ A)  (C ++ [nth x B y]) p2 p).
 Qed.

 Lemma Z_lt_length {X} (A : list X) sizeA x:
  Zlength A = Z.of_nat sizeA -> Z.of_nat x < Z.of_nat sizeA -> (x < length A)%nat.
 Proof.
   intros.
   rewrite <- H in H0.
   rewrite Zlength_length_eq in H0.
   eapply Z_nat_lt_equiv in H0.
   easy.
 Qed.

 Lemma Z_ge_length {X} (A : list X) sizeA x:
  Zlength A = Z.of_nat sizeA -> Z.of_nat x >= Z.of_nat sizeA -> (x >= length A)%nat.
 Proof.
  intros.
  rewrite <- H in H0.
  rewrite Zlength_length_eq in H0.
  eapply Z_nat_ge_equiv in H0.
  easy.
 Qed.

 Lemma list_repeat_length {X} x (k : X):
  (x > 0)%nat -> (length (list_repeat x k) > 0)%nat.
 Proof.
  destruct x; cbn; lia.
 Qed.

 Lemma firstn_length_eq {X} (L : list X) n :
 (n >= length L)%nat -> firstn n L = L.
 Proof.
  revert n.
  induction L; destruct n; [easy|easy|easy|intros].
  cbn in *.
  rewrite (IHL n); [easy|lia].
 Qed.

 Lemma skipn_length_eq {X} (L : list X) n:
  (n >= length L)%nat -> skipn n L = nil.
 Proof.
  revert n.
  induction L; destruct n; [easy|easy|easy|intros].
  cbn in *.
  rewrite (IHL n); [easy|lia].
 Qed.

 Lemma firstn_append {X} (A B : list X) x :
  firstn x (A++B) = firstn x A ++ firstn (x - length A)%nat B.
 Proof.
  revert x.
  induction A; [destruct x; now cbn|].
  destruct x; [now cbn|] .
  cbn.
  now f_equal.
 Qed.

 Lemma skipn_append {X} (A B : list X) x :
  skipn x (A++B) = skipn x A ++ skipn (x - length A)%nat B.
 Proof.
  revert x.
  induction A; [destruct x; now cbn|].
  destruct x; [now cbn|] .
  cbn.
  now f_equal.
 Qed.

 Lemma skipn_repeat {X} x n m:
  @skipn X n (list_repeat m x) = list_repeat (m-n) x.
 Proof.
  revert m.
  induction n; intros; [cbn; f_equal; lia|].
  destruct m; cbn; [easy|].
  now erewrite IHn.
 Qed.

 Lemma list_invariant sizeA sizeB x y cRes A:
   (x < sizeA)%nat -> (y <= sizeB)%nat -> length cRes = (x + y)%nat ->
   (upd_Znth (Z.of_nat x + Z.of_nat y) (cRes ++ list_repeat (sizeA + sizeB - Z.to_nat (Z.of_nat x + Z.of_nat y)) Vundef) (nth x A Vundef)) 
   = (cRes ++ nth x A Vundef :: list_repeat (sizeA + sizeB - (Z.to_nat (Z.of_nat x + Z.of_nat y) + 1)) Vundef).
 Proof.
  intros.
  cbn.
  unfold upd_Znth.
  cbn.
  repeat erewrite  <- Nat2Z.inj_add .
  assert (0 <= Z.of_nat (x + y)) by lia.
  assert (~(0 > Z.of_nat (x + y))) by lia.
  destruct (Sumbool.sumbool_and (0 <= Z.of_nat (x + y)) (0 > Z.of_nat (x + y))
  (Z.of_nat (x + y) <
   Zlength
     (cRes ++
      list_repeat (sizeA + sizeB - Z.to_nat (Z.of_nat (x + y))) Vundef))
  (Z.of_nat (x + y) >=
   Zlength
     (cRes ++
      list_repeat (sizeA + sizeB - Z.to_nat (Z.of_nat (x + y))) Vundef))
  (zle 0 (Z.of_nat (x + y)))
  (zlt (Z.of_nat (x + y))
     (Zlength
        (cRes ++
         list_repeat (sizeA + sizeB - Z.to_nat (Z.of_nat (x + y))) Vundef)))).
  - erewrite firstn_append.
    rewrite <- H1 at 1.
    erewrite Nat2Z.id.
    erewrite (firstn_length_eq _ (length cRes)); [|lia].
    erewrite <- app_assoc.
    f_equal.
    rewrite <- H1 at 1.
    erewrite Nat2Z.id.
    erewrite Nat.sub_diag.
    cbn.
    f_equal.
    unfold sublist.sublist.
    erewrite Zlength_length_eq2.
    erewrite firstn_length_eq; [|lia].
    erewrite skipn_append.
    erewrite Z.add_1_r.
    erewrite Z2Nat.inj_succ; [|lia].
    erewrite Nat2Z.id.
    erewrite (skipn_length_eq _ (S (x + y))); [|lia].
    cbn [app].
    erewrite <- minus_Sn_m; [|lia].
    rewrite H1.
    erewrite Nat.sub_diag.
    erewrite skipn_repeat.
    f_equal.
    lia.
  - destruct o; [easy|].
    erewrite <- Zlength_length_eq2 in H1.
    assert ((Zlength cRes) = Z.of_nat (x + y)).
    { erewrite <- (Z2Nat.id (Zlength cRes)); [now f_equal|]. eapply Zlength_nonneg. }
    rewrite <- H5 in H4.
    repeat erewrite Zlength_length_eq in H4.
    eapply Z_nat_ge_equiv in H4.
    erewrite <- Zlength_length_eq in H4.
    rewrite H1 in H4.
    assert (0 < sizeA + sizeB - (x + y))%nat by lia.
    erewrite app_length in H4.
    epose (list_repeat_length (sizeA + sizeB - (x + y)) Vundef H6).
    lia.
 Qed.

 Lemma list_invariant2 sizeA sizeB x y cRes B:
  (x <= sizeA)%nat -> (y < sizeB)%nat -> length cRes = (x + y)%nat ->
  (upd_Znth (Z.of_nat x + Z.of_nat y)
     (cRes ++ list_repeat (sizeA + sizeB - Z.to_nat (Z.of_nat x + Z.of_nat y)) Vundef) 
     (nth y B Vundef))
  =  (cRes ++ nth y B Vundef :: list_repeat (sizeA + sizeB - (Z.to_nat (Z.of_nat x + Z.of_nat y) + 1)) Vundef).
  Proof.
   intros.
   erewrite (Z.add_comm (Z.of_nat x) (Z.of_nat y)).
   erewrite (Nat.add_comm sizeA sizeB).
   eapply (list_invariant sizeB sizeA y x cRes B); lia.
  Qed.

 Lemma sublist_succ_cons {X} a (A : list X) x y :
  sublist x y A = sublist (S x) (S y) (a::A).
 Proof.
  revert x y A; induction A; destruct x, y; cbn; auto.
 Qed.

 Lemma sublist_nth_eq {X} (A : list X) n m y :
  (n < length A)%nat -> (n < m)%nat -> sublist n m A = (nth n A y) :: sublist (S n) m A.
 Proof.
  revert n m.
  induction A; [cbn; lia|].
  intros.
  destruct n, m; [cbn;lia|cbn;easy|cbn;lia|].
  cbn in *.
  assert (n < Datatypes.length A)%nat by lia; assert (n < m)%nat by lia.
  specialize (IHA n m H1 H2).
  unfold sublist in IHA.
  now rewrite IHA.
 Qed.  

 Lemma skipn_nth_eq {X} (A : list X) n m x :
  (n+m < length A)%nat -> nth n (skipn m A) x = nth (n+m) A x.
 Proof.
  revert n m.
  induction A; cbn; [lia|].
  intros; destruct n, m; try now cbn.
  { cbn; erewrite (IHA 0%nat m); [f_equal|]; lia. }
  { erewrite Nat.add_0_r; now cbn. }
  { cbn. erewrite IHA; [f_equal|]; lia. }
 Qed.

 Corollary sublist_nth_eq2 {X} (A : list X) n m o x :
  (n+m < o <= length A)%nat -> nth n (sublist m o A) x = nth (n+m) A x.
 Proof.
  unfold sublist; intros; erewrite skipn_nth_eq.
  - revert n m A H; induction o; destruct A, n, m; cbn; try easy; cbn; intros.
    { erewrite (IHo 0%nat m); [now cbn|lia]. }
    { erewrite Nat.add_0_r. assert ((n + 0 < o <= Datatypes.length A)%nat) by lia. epose (IHo n 0%nat A H0). now erewrite Nat.add_0_r in e. }
    { now erewrite IHo; [|lia]. }
  - erewrite firstn_length_le; easy.
 Qed.

 Lemma Forall_sublist_cmp_nth {X} cmp x (A : list X) y : 
  (x < length A)%nat ->
  Forall cmp (sublist x (Datatypes.length A) A) 
  <-> Forall cmp (sublist (S x) (Datatypes.length A) A) /\ cmp (nth x A y).
 Proof.
  intros; apply conj; intros.
  - apply conj.
    + unfold sublist in *. erewrite firstn_length_eq in *; [|lia|lia].
      revert x H H0.
      induction A; intros; destruct x; [constructor|constructor|cbn in *|].
      * now eapply (@Forall_inv_tail _ _ a _).
      * erewrite skipn_cons in H0.
        cbn in H; assert (x < Datatypes.length A)%nat by lia.
        specialize (IHA x H1 H0).
        unfold skipn.
        now fold (skipn (S x) A).
    + revert x H H0; induction A; destruct x; [cbn in *; lia|cbn;lia| |]; intros.
      * cbn in *; now dependent elimination H0.
      * eapply IHA; [cbn in *;lia|].
        cbn [length] in H0.
        now erewrite <- sublist_succ_cons in H0.
  - destruct H0.
    erewrite (sublist_nth_eq _ _ _ y); [|easy|easy].
    now eapply Forall_cons.
 Qed. 


 Lemma Forall_sublist_cmp {X} A B cmp x (y : X):
  lt x (length B) -> (Forall (fun a : val => Forall (cmp a) (sublist x (length B) B)) A) -> Forall (fun a : val => cmp a (nth x B y)) A.
 Proof.
  intros.
  eapply Forall_nth; intros.
  do 2 eapply Forall_nth in H0.
  {
    instantiate (2 := 0%nat) in H0.
    erewrite sublist_nth_eq in H0; cbn in H0; [eapply H0|lia|lia].
  }
  {
    unfold sublist; destruct B, x; cbn in *; [lia|lia|lia|].
    rewrite firstn_length_eq; [|lia].
    erewrite skipn_length.
    lia.
  }
  { easy. }
  { now instantiate (1 := i). }
  Grab Existential Variables. all: easy.
 Qed.

 Lemma Forall_skipn_weaken {X} x x' p (A : list X) :
  (x <= x')%nat -> Forall p (skipn x A) -> Forall p (skipn x' A).
 Proof.
  revert x x'.
  induction A; intros; destruct x, x'; try easy.
  - cbn in *.
    eapply (IHA 0%nat); [try lia|cbn].
    now dependent elimination H0.
  - cbn in *.
    eapply (IHA x); [lia|easy].
 Qed.

 Corollary Forall_sublist_weaken_lower {X} x x' y p (A : list X) :
 (x <= x')%nat -> Forall p (sublist x y A) -> Forall p (sublist x' y A).
 Proof.
  unfold sublist.
  eapply Forall_skipn_weaken.
 Qed.

 Lemma le_surrounded x y:
  (x <= y <= (S x))%nat -> y = x \/ y = S x.
 Proof.
  revert y; induction x; destruct y; intros.
  - now left.
  - right; lia.
  - lia.
  - cbn in *.
    assert ((x <= y <= S x)%nat) by lia.
    specialize (IHx y H0); lia.
 Qed.

 Lemma Forall_firstn_weaken {X} x x' p (A : list X) :
  (x' <= x)%nat -> Forall p (firstn x A) -> Forall p (firstn x' A).
 Proof.
  revert x x'.
  induction A; intros; destruct x, x'; try easy.
  - cbn; constructor.
  - cbn in *.
    dependent elimination H0.
    constructor; [easy|].
    eapply (IHA x x'); [lia|easy].
 Qed.

 Lemma le_min_surrounded x y z:
  (x <= y)%nat -> (y <= min (S x) z)%nat -> y = x \/ (y = S x /\ ((S x) <= z)%nat) \/ False.
 Proof.
  intros.
  destruct (Nat.min_spec (S x) z); destruct H1.
  - erewrite H2 in H0. erewrite <- or_assoc; left. destruct (le_surrounded x y); [lia|lia|right;lia].
  - lia.
 Qed.

 Lemma Sublist_empty_ge {X} n m (A : list X) :
  (n >= m)%nat -> sublist n m A = [].
 Proof.
  revert n m; induction A; destruct n, m; cbn; try easy.
  intros.
  eapply (IHA n m); lia.
 Qed.

 Lemma int_id b s (x : val) :
  is_int b s x -> (Vint (force_int (x)) = x).
 Proof.
  destruct x; now cbn.
 Qed.

 Lemma I_cmp_le_trans:
  transitive val (I_cmp Cle).
 Proof.
  intros a b c ? ?.
  destruct a,b; try contradiction.
  destruct c; try contradiction.
  simpl in *.
  unfold Int.lt in *.
  unfold zlt in *.
  destruct (Z_lt_dec (Int.signed i0) (Int.signed i)), (Z_lt_dec (Int.signed i1) (Int.signed i0)), (Z_lt_dec (Int.signed i1) (Int.signed i)); try now cbn in *.
  lia.
 Qed.

 Lemma I_cmp_lt_trans:
  transitive val (I_cmp Clt).
 Proof.
  intros a b c ? ?.
  destruct a,b; try contradiction.
  destruct c; try contradiction.
  simpl in *.
  unfold Int.lt in *.
  unfold zlt in *.
  destruct (Z_lt_dec (Int.signed i) (Int.signed i0)), (Z_lt_dec (Int.signed i) (Int.signed i1)), (Z_lt_dec (Int.signed i0) (Int.signed i1)); try now cbn in *.
  lia.
 Qed.

 Lemma I_cmp_lt_le1 x y:
  Int.cmp Clt x y = true -> Int.cmp Cle x y = true.
 Proof.
  unfold Int.cmp.
  unfold Int.lt.
  destruct (zlt (Int.signed x) (Int.signed y)), (zlt (Int.signed y) (Int.signed x)); cbn; now try lia.
 Qed.

 Lemma I_cmp_lt_le2 x y:
  Int.cmp Clt x y = false -> Int.cmp Cle y x = true.
 Proof.
  unfold Int.cmp.
  unfold Int.lt.
  destruct (zlt (Int.signed x) (Int.signed y)), (zlt (Int.signed y) (Int.signed x)); cbn; now try lia.
 Qed.

 Lemma StronglySorted_app {X} cmp (A B : list X) :
 StronglySorted cmp (A++B) -> StronglySorted cmp B.
Proof.
 induction A; cbn; try easy.
 intros.
 dependent elimination H; auto.
Qed.

 Lemma I_min_comm x y:
  I_min Clt x y = I_min Clt y x.
 Proof.
  destruct x,y; unfold I_min; cbn; try easy; intros.
  unfold Int.lt, Int.signed, Int.unsigned, zlt, Int.half_modulus in *.
  repeat destruct (Z_lt_dec _ _); destruct i0, i; eapply Int.mkint_eq; cbn in *;  try easy; try lia.
 Qed. 
 
 Fact invariant_disj_equiv x y cA cB min:
 (x < Datatypes.length cA)%nat /\
  (y < Datatypes.length cB)%nat /\
  min = I_min Clt (nth x cA Vundef) (nth y cB Vundef) \/
  (x >= Datatypes.length cA)%nat /\
  (y < Datatypes.length cB)%nat /\ min = force_int (nth y cB Vundef) \/
  (x < Datatypes.length cA)%nat /\
  (y >= Datatypes.length cB)%nat /\ min = force_int (nth x cA Vundef)
  <->
 (y < Datatypes.length cB)%nat /\
 (x < Datatypes.length cA)%nat /\
 min = I_min Clt (nth y cB Vundef) (nth x cA Vundef) \/
 (y >= Datatypes.length cB)%nat /\
 (x < Datatypes.length cA)%nat /\ min = force_int (nth x cA Vundef) \/
 (y < Datatypes.length cB)%nat /\
 (x >= Datatypes.length cA)%nat /\ min = force_int (nth y cB Vundef).
 Proof.
  apply conj; intros; destruct H as [(? & ? & ?)|[(? & ? & ?)|(? & ? & ?)]]; auto; erewrite I_min_comm in H1; auto.
 Qed.

 Lemma Forall_min_invariant (x x' y : nat) cA cB cRes' min :
  (x < Datatypes.length cA)%nat  /\ (y < Datatypes.length cB)%nat  /\ min = I_min Clt (nth x cA Vundef) (nth y cB Vundef)
  \/
  (x >= Datatypes.length cA)%nat /\ (y < Datatypes.length cB)%nat  /\ min = force_int (nth y cB Vundef)
  \/
  (x < Datatypes.length cA)%nat  /\ (y >= Datatypes.length cB)%nat /\ min = force_int (nth x cA Vundef)
  ->
  (x <= x')%nat
  ->
  (x' <= NPeano.Nat.min (S x) (Datatypes.length cA))%nat
  ->
  Forall (fun x : val => is_int I32 Signed x) cA
  ->
  Forall (fun x : val => is_int I32 Signed x) cB
  ->
  Sorted (I_cmp Cle) cA
  ->
  Forall (fun a : val => Forall (I_cmp Cle a) (sublist x (Datatypes.length cA) cA)) cRes'
  ->
  Forall (fun a : val => Forall (I_cmp Cle a) (sublist x' (Datatypes.length cA) cA)) (cRes' ++ [Vint min]).
  Proof.
  intros.
  { destruct H as [(?H & ?H & ?H)|[(?H & ?H & ?H)|(?H & ?H & ?H)]].
    { unfold I_min in H4.
      edestruct (Forall_nth (fun x : val => is_int I32 Signed x) cA) as [FF1 _]; specialize (FF1 H2 x Vundef H).
      edestruct (Forall_nth (fun x : val => is_int I32 Signed x) cB) as [FF2 _]; specialize (FF2 H3 y Vundef H6).
      unfold is_int in *. 
      edestruct (@nth_split _ x cA Vundef H) as [?L [?L [?H ?H]]].
      destruct (nth x cA Vundef), (nth y cB Vundef); try easy.
      eapply Forall_app; apply conj.
      { destruct (Nat.le_gt_cases (length cA) x').
        { erewrite Sublist_empty_ge; [|lia]. eapply Forall_nth; intros; constructor. }
        { eapply Forall_nth. intros. eapply (Forall_sublist_cmp_nth _ _ _ Vundef); [easy|apply conj]. 
          { pose Forall_nth as Fnth.
            specialize (Fnth val (fun a : val => Forall (I_cmp Cle a) (sublist x (Datatypes.length cA) cA)) cRes'); destruct Fnth as [Fnth _]; specialize (Fnth H5 i1 d H11).
            eapply (Forall_sublist_weaken_lower x); [lia|easy].
          }
          { 
            edestruct (le_min_surrounded x x' (length cA) H0 H1) as [|[|]].
            { 
              rewrite H12.  
              eapply Forall_nth in H5.
              { erewrite sublist_nth_eq in H5; [|easy|easy]. dependent elimination H5. eapply i2. }
              { easy. }
            }
            {
              destruct H12; rewrite H12.
              eapply Forall_nth in H5. 
              { erewrite sublist_nth_eq in H5; [|easy|easy]. erewrite sublist_nth_eq in H5; [|lia|lia]. dependent elimination H5. dependent elimination f. eapply i3. }
              { easy. } 
              Unshelve. exact Vundef.
            }
            { easy. }
          }
        }
      } 
      {
        repeat constructor.
        unfold sublist.
        erewrite firstn_length_eq; [|lia].
        rewrite H8.
        edestruct (le_min_surrounded x x' (length cA) H0 H1) as [|[(? & ?)|]].
        {
          erewrite skipn_app2; [|lia].
          rewrite H10; rewrite <- H9.
          erewrite Nat.sub_diag; cbn.
          pose (Sorted_StronglySorted I_cmp_le_trans H4).
          rewrite H8 in s.
          eapply StronglySorted_app in s.
          rewrite H7.
          case_eq (Int.cmp Clt i i0); intros; unfold I_cmp; unfold I_min; rewrite H11; cbn.
          { constructor.
            { unfold Int.lt; destruct (zlt (Int.signed i) (Int.signed i)); cbn; [lia|easy]. }
            { now dependent elimination s. }
          }
          { 
            constructor.
            { unfold Int.cmp in *. now rewrite H11. }
            { 
              dependent elimination s.
              eapply I_cmp_lt_le2 in H11.
              pose (I_cmp_le_trans (Vint i0) (Vint i)).
              unfold I_cmp in i1.
              rewrite H11 in i1.
              eapply Forall_nth; intros.
              eapply i1; [easy|].
              epose (Forall_nth  _ cA); destruct i3 as [? _].
              specialize (H13 H2 (S(length L) + i2)%nat d).
              rewrite H8 in H13.
              erewrite app_length in H13.
              cbn in H13.
              assert (S (Datatypes.length L + i2) < Datatypes.length L + S (Datatypes.length l))%nat by lia.
              specialize (H13 H14).
              erewrite plus_n_Sm in H13.
              erewrite app_nth2_plus in H13.
              cbn in H13.
              case_eq (nth i2 l d); intros; rewrite H15 in H13; try contradiction.
              eapply Forall_nth in f;
              now try erewrite H15 in f.
            }
          }
        }
        {
          erewrite skipn_app2; [|lia].
          rewrite H10; rewrite <- H9.
          assert ((S (Datatypes.length L) - Datatypes.length L)%nat = 1%nat) by lia.
          rewrite H12; cbn.
          pose (Sorted_StronglySorted I_cmp_le_trans H4).
          rewrite H8 in s.
          eapply StronglySorted_app in s.
          dependent elimination s.
          case_eq (Int.cmp Clt i i0); intros; unfold I_min in H7; rewrite H13 in H7. 
          { now rewrite H7. }
          { rewrite H7. 
            eapply Forall_nth.
            intros.
            eapply I_cmp_lt_le2 in H13. 
            pose (I_cmp_le_trans (Vint i0) (Vint i) (nth i1 l d)). 
            unfold I_cmp in *; unfold Int.cmp in *. 
            rewrite H13 in i2. 
            eapply Forall_nth in f; [eapply (i2 eq_refl f)|easy].
          }
        }
        { easy. }
      }
    }
    {
      pose (le_trans (length cA) x x' H H0).
      erewrite Sublist_empty_ge; [|easy].
      eapply Forall_nth; intros.
      constructor.
    }
    {
      edestruct (Forall_nth (fun x : val => is_int I32 Signed x) cA) as [FF _]; specialize (FF H2 x Vundef H).
      unfold is_int in *.
      edestruct (@nth_split _ x cA Vundef H) as [?L [?L [?H ?H]]].
      case_eq (nth x cA Vundef); intros; rewrite H10 in FF; try easy. 
      eapply Forall_app; apply conj; [|].
      {
        eapply Forall_nth; intros.
        eapply Forall_sublist_weaken_lower; [exact H0|].
        eapply Forall_nth in H5; [eapply H5|easy].
      }
      {
        repeat constructor.
        rewrite H10 in H7.
        unfold force_int in H7; cbn.
        rewrite H7.
        rewrite <- H10.
        pose (Sorted_StronglySorted I_cmp_le_trans H4).
        rewrite H8 in s.
        unfold sublist.
        erewrite firstn_length_eq; [|lia].
        rewrite H8 at 2.
        erewrite skipn_app2; [|lia].
        rewrite H9.
        assert ((x' = S(x))%nat \/ (x' = x)%nat) by lia; destruct H11.
        {
          rewrite H11.
          assert (S x - x = 1%nat)%nat by lia.
          rewrite H12; cbn.
          eapply StronglySorted_app in s.
          now dependent elimination s.
        }
        {
          rewrite H11; erewrite Nat.sub_diag; cbn.
          constructor; [unfold I_cmp; rewrite H10; unfold Int.cmp; unfold Int.lt; destruct (zlt (Int.signed i) (Int.signed i)); [lia|easy]|].
          eapply StronglySorted_app in s.
          now dependent elimination s.
        }
      }
    }
  }
 Qed.

 Lemma Forall_is_int i s x cA sizeA :
  Forall (fun x : val => is_int i s x) cA -> Zlength cA = Z.of_nat sizeA -> Z.of_nat x < Z.of_nat sizeA
  -> is_int i s (Znth (Z.of_nat x) cA).
 Proof.
  intros.
  eapply Forall_nth in H. 
  erewrite <- Znth_nth_eq; [eapply H|].
  all: erewrite Zlength_length_eq in H0; eapply Nat2Z.inj in H0; eapply Z_nat_lt_equiv in H1; now rewrite <- H0 in H1.
 Qed.

 Lemma Nat_mod2_succ_succ x :
  ((S (S x) mod 2)%nat = ((x) mod 2)%nat).
 Proof.
  assert (S (S x) = x + (1 * 2)%nat)%nat by lia.
  rewrite H.
  erewrite Nat.mod_add; lia.
 Qed.

 Lemma Nat_double_mod2 x:
  (Nat.double x mod 2%nat)%nat = 0%nat.
 Proof.
  induction x.
  cbn; try lia.
  rewrite Div2.double_S.
  now rewrite Nat_mod2_succ_succ.
 Qed.

 Lemma Nat_double_succ_mod2 x:
  (S(Nat.double x) mod 2%nat)%nat = 1%nat.
 Proof.
  change (S(Nat.double x)) with (1 + (Nat.double x))%nat.
  erewrite Nat.add_mod; [|lia].
  erewrite Nat_double_mod2.
  now cbn.
 Qed.

 Lemma Nat_div_2 x:
  (x - (x / 2)%nat)%nat = ((x / 2)%nat + Nat.modulo x 2)%nat.
 Proof.
  induction x; [cbn; lia|].
  destruct (Even.even_odd_dec x).
  { 
    epose (Even.odd_S _ e).
    erewrite <- Nat.div2_div in *.
    erewrite <- Div2.even_div2; [|easy].
    erewrite Nat.sub_succ_l; [|lia].
    rewrite IHx.
    epose (Div2.even_2n _ e); destruct s.
    rewrite e0.
    erewrite Nat_double_mod2.
    erewrite Nat.double_twice in *.
    erewrite Nat.div2_double.
    rewrite e0 in o.
    erewrite <- Nat.double_twice in *.
    erewrite Nat_double_succ_mod2; lia.
  }
  {
    epose (Even.even_S _ o).
    epose (Div2.even_2n _ e); destruct s.
    rewrite e0.
    erewrite Nat.double_twice in *.
    erewrite <- Nat.div2_div.
    erewrite Nat.div2_double.
    erewrite <- Nat.double_twice at 2.
    erewrite Nat_double_mod2; lia.
  }
 Qed.

 Lemma Nat_div_2_lt x : 
  (x > 0)%nat -> (x / 2 < x)%nat.
 Proof.
  destruct x; [cbn; lia|intros].
  eapply (Nat.div_lt (S x) 2); lia.
 Qed.

 Lemma Nat_div_2_le x : 
  (x / 2 <= x)%nat.
 Proof.
  destruct x; [cbn; lia|].
  eapply Nat.lt_le_incl.
  eapply (Nat.div_lt (S x) 2); lia.
 Qed.
 
 Corollary Z_div_2_le x : 
  ((Z.of_nat x) / 2 <= (Z.of_nat x)).
 Proof.
  intros.
  change 2 with (Z.of_nat 2).
  erewrite <- div_Zdiv; [|lia].
  erewrite Z2Nat.inj_le; [|lia|lia].
  repeat erewrite Nat2Z.id.
  eapply Nat_div_2_le.
 Qed.

 Corollary Znonneg_div_2_le x :
  x >= 0 -> (x / 2 <= x).
 Proof.
  intros.
  assert {y | Z.of_nat y = x}.
  {
    exists (Z.to_nat x).
    erewrite Z2Nat.id; lia.
  }
  destruct H0.
  rewrite <- e.
  eapply Z_div_2_le.
 Qed.

 Lemma size_div2_mod2_int_range size :
  Z.of_nat size * 4 <= Int.max_signed -> (size > 0)%nat
  ->  Int.min_signed <=
        Int.signed (Int.divs (Int.repr (Z.of_nat size)) (Int.repr 2)) 
      + Int.signed (Int.mods (Int.repr (Z.of_nat size)) (Int.repr 2))
      <= Int.max_signed.
 Proof.
  intros.
  assert (sizeMax : (Z.of_nat size <= Int.max_signed)) by lia.
  unfold Int.min_signed, Int.max_signed; apply conj.
  {
    unfold Int.divs, Int.mods.
    repeat erewrite Int.signed_repr; unfold Int.min_signed, Int.max_signed; repeat apply conj.
    {
      eapply Z.ge_le_iff.
      eapply (Zge_trans _ 0 _); [|unfold Int.half_modulus, Int.modulus, two_power_nat, shift_nat, Int.wordsize, Wordsize_32.wordsize; cbn; lia].                 
      assert (forall x y, x >= 0 -> y >= 0 -> x + y >= 0) by lia.
      eapply H1.
      erewrite Zbits.Zquot_Zdiv; [|lia].
      destruct (zlt (Z.of_nat size) 0); [lia|].
      eapply Z_div_ge0; lia.
      eapply Z.ge_le_iff.
      eapply Z.rem_nonneg; lia.
    }
    {
      eapply Z.ge_le_iff.
      eapply (Zge_trans _ 0 _); [|unfold Int.half_modulus, Int.modulus, two_power_nat, shift_nat, Int.wordsize, Wordsize_32.wordsize; cbn; lia].
      eapply Z.ge_le_iff.
      eapply Z.rem_nonneg; lia.
    }
    {
      unfold Int.half_modulus, Int.modulus, two_power_nat, shift_nat, Int.wordsize, Wordsize_32.wordsize in *; cbn in *.
      eapply Z.ge_le_iff.
      eapply (Zge_trans _ (Z.of_nat size) _); try lia.
      erewrite Zquot.Zrem_odd.
      destruct (Z.odd (Z.of_nat size)); [|lia].
      destruct size; cbn; lia.
    }
    all: unfold Int.max_signed, Int.half_modulus, Int.modulus in *; cbn in *; try lia.
    all: erewrite Zbits.Zquot_Zdiv.
    2,4: lia.
    all: destruct (zlt (Z.of_nat size) 0); [lia|]; change 2 with (Z.of_nat 2).
    all: erewrite <- div_Zdiv; try lia.
    eapply (Z.le_trans _ (Z.of_nat (size * 4))); [|lia].
    erewrite <- Nat2Z.inj_le.
    eapply (Nat.le_trans _ size); [eapply Nat_div_2_le|].
    lia.
  }
  {
    unfold Int.divs, Int.mods.
    erewrite (Int.signed_repr 2); [|unfold Int.max_signed, Int.half_modulus, Int.modulus in *; cbn in *; try lia].
    erewrite (Int.signed_repr (Z.of_nat size)); [|unfold Int.max_signed, Int.half_modulus, Int.modulus in *; cbn in *; try lia].
    erewrite Zquot.Zrem_even.
    destruct (Z.even (Z.of_nat size)).
    {
      erewrite (Int.signed_repr 0); [|unfold Int.max_signed, Int.half_modulus, Int.modulus in *; cbn in *; try lia].
      erewrite Z.add_0_r.
      erewrite (Int.signed_repr).
      {
        erewrite Zbits.Zquot_Zdiv; [|lia].
        destruct (zlt (Z.of_nat size) 0); [lia|].
        eapply (Z.le_trans _ (Z.of_nat size)); [eapply Z_div_2_le|unfold Int.max_signed in *; lia].
      }
      {
        apply conj; eapply Z.ge_le_iff.
        erewrite Zbits.Zquot_Zdiv; destruct (zlt (Z.of_nat size) 0); [| |lia|lia]; eapply (Zge_trans _ 0).
        2,4: unfold Int.half_modulus, Int.modulus in *; cbn in *; try lia.
        1,2: eapply Z_div_ge0; lia.
        erewrite Zbits.Zquot_Zdiv; [|lia].
        destruct (zlt (Z.of_nat size) 0); [lia|].
        eapply (Zge_trans _ (Z.of_nat size)); [lia|].
        erewrite Z.ge_le_iff; eapply Z_div_2_le.
      }
    }
    {
      assert (Z.sgn (Z.of_nat size) = 1) by lia.
      rewrite H1.
      repeat erewrite (Int.signed_repr); [|unfold Int.max_signed, Int.half_modulus, Int.modulus in *; cbn in *; lia|].
      {
        eapply Z.ge_le_iff; eapply (Zge_trans _ (Z.of_nat size)); [unfold Int.max_signed in *; lia|]. 
        erewrite Zbits.Zquot_Zdiv; [|lia].
        destruct (zlt (Z.of_nat size) 0); [lia|].
        change 2 with (Z.of_nat 2).
        change 1 with (Z.of_nat 1).
        eapply Z.ge_le_iff; erewrite <- div_Zdiv; [|lia].
        erewrite <- Nat2Z.inj_add.
        erewrite Nat.add_1_r; erewrite <- Nat2Z.inj_le.
        eapply Nat_div_2_lt; lia.
        }
        {
        apply conj; eapply Z.ge_le_iff.
        erewrite Zbits.Zquot_Zdiv; destruct (zlt (Z.of_nat size) 0); [| |lia|lia]; eapply (Zge_trans _ 0).
        2,4: unfold Int.half_modulus, Int.modulus in *; cbn in *; try lia.
        1,2: eapply Z_div_ge0; lia.
        erewrite Zbits.Zquot_Zdiv; [|lia].
        destruct (zlt (Z.of_nat size) 0); [lia|].
        eapply (Zge_trans _ (Z.of_nat size)); [lia|].
        erewrite Z.ge_le_iff; eapply Z_div_2_le.
      }
    }  
  }
 Qed.

 Lemma int_nat_div2_eq size :
  Z.of_nat size * 4 <= Int.max_signed -> (size > 0)%nat ->
  Int.divs (Int.repr (Z.of_nat size)) (Int.repr 2) =
  Int.repr (Z.of_nat (size / 2)).
 Proof.
  intros.
  assert (sizeMax : (Z.of_nat size <= Int.max_signed)) by lia.
  unfold Int.divs.
  erewrite Z.quot_div_nonneg.
  {
    repeat f_equal.
    repeat rewrite Int.signed_repr.
    all: unfold Int.max_signed, Int.half_modulus, Int.modulus in *; cbn in *; try lia.
    change 2 with (Z.of_nat 2).
    erewrite <- div_Zdiv; f_equal.
    lia.
  }
  all: erewrite Int.signed_repr; [lia|]; unfold Int.max_signed, Int.half_modulus, Int.modulus in *; cbn in *; lia.
 Qed.

 Lemma int_nat_div2_mod2_eq size :
  Z.of_nat size * 4 <= Int.max_signed -> (size > 0)%nat ->
  Int.add (Int.divs (Int.repr (Z.of_nat size)) (Int.repr 2)) 
         (Int.mods (Int.repr (Z.of_nat size)) (Int.repr 2)) 
   =
  Int.repr (Z.of_nat (size / 2 + size mod 2)).
 Proof.
  intros.
  assert (sizeMax : (Z.of_nat size <= Int.max_signed)) by lia.
  unfold Int.add, Int.divs.
  erewrite Nat2Z.inj_add.
  erewrite div_Zdiv; [|lia].
  erewrite mod_Zmod; [|lia].
  unfold Int.mods.
  erewrite Z.rem_mod_nonneg; try erewrite Int.signed_repr; unfold Int.max_signed, Int.half_modulus, Int.modulus in *; cbn in *; try lia.
  erewrite Z.quot_div_nonneg; try erewrite Int.signed_repr; unfold Int.max_signed, Int.half_modulus, Int.modulus in *; cbn in *; try lia.
  f_equal.
  repeat erewrite Int.unsigned_repr; [easy | |]; apply conj; unfold Int.max_unsigned, Int.modulus in *; cbn in *.
  {
    pose (Z.mod_bound_pos (Z.of_nat size) 2).
    eapply a; lia.
  }
  {
    pose (Z.mod_bound_pos (Z.of_nat size) 2).
    eapply (Z.le_trans _ 1); [|lia].
    eapply Zlt_succ_le; cbn; lia.
  }
  {
    change 2 with (Z.of_nat 2); erewrite <- div_Zdiv; lia.
  }
  {
    eapply (Z.le_trans _ (Z.of_nat size)); [eapply Z_div_2_le|lia].
  }
 Qed.