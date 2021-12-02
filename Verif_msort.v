Require Import Equations.Equations.
Require Import Coq.Sorting.Sorted.
Require Import Permutation.
Require Import Coq.ZArith.Znat Coq.Numbers.NatInt.NZOrder.
Require Import Coq.Arith.PeanoNat.
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.

Require Import msort.
Require Import aux_lemmas.

Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

 (** *** Functional models *)

Definition merge_spec : ident * funspec :=
  DECLARE _merge
    WITH A : val, B : val, res : val, cA : list val, cB : list val, shA : share, shB : share, sizeA : nat, sizeB : nat
    PRE [ tptr tint, tptr tint, tptr tint, tint, tint ]
      PROP   (readable_share shA; readable_share shB;
              Sorted (I_cmp Cle) cA; Sorted (I_cmp Cle) cB;
              1 <= Z.of_nat sizeA <= Int.max_signed; 1 <= Z.of_nat sizeB <= Int.max_signed;
              2 <= Z.of_nat sizeA + Z.of_nat sizeB <= Int.max_signed;
              Forall (fun x => is_int I32 Signed x) cA; Forall (fun x => is_int I32 Signed x) cB)
      PARAMS (A; B; res; Vint (Int.repr (Z.of_nat sizeA)); Vint (Int.repr (Z.of_nat sizeB)))
      SEP    (data_at shA (tarray tint (Z.of_nat sizeA)) cA A; data_at shB (tarray tint (Z.of_nat sizeB)) cB B;
              data_at Ews (tarray tint (Z.of_nat sizeA + Z.of_nat sizeB)) (list_repeat (sizeA + sizeB) Vundef) res)
    POST [ tvoid ]
      EX cRes : list val,
        PROP   (Permutation (cA ++ cB) cRes; Sorted (I_cmp Cle) cRes)
        RETURN ()
        SEP    (data_at shA (tarray tint (Z.of_nat sizeA)) cA A; data_at shB (tarray tint (Z.of_nat sizeB)) cB B;
                data_at Ews (tarray tint (Z.of_nat sizeA + Z.of_nat sizeB)) cRes res).

Definition msort_spec : ident * funspec :=
  DECLARE _msort
    WITH array : val, contents : list val, sh : share, size : nat, gv: globals 
    PRE [ tptr tint, tint ]
      PROP    (readable_share sh; Forall (fun x => is_int I32 Signed x) contents; (Z.of_nat size * 4 <= Int.max_signed); (size > 0)%nat)
      PARAMS  (array; Vint (Int.repr (Z.of_nat size)))
      GLOBALS (gv)
      SEP     (data_at sh (tarray tint (Z.of_nat size)) contents array; mem_mgr gv)
    POST [ tptr tint ]
      EX res : val, EX cRes : list val,
        PROP   (Permutation contents cRes; StronglySorted (I_cmp Cle) cRes; res <> nullval)
        RETURN (res)
        SEP    (data_at sh (tarray tint (Z.of_nat size)) contents array;
                malloc_token Ews (tarray tint (Z.of_nat (Datatypes.length contents))) res * data_at Ews (tarray tint (Z.of_nat size)) cRes res; mem_mgr gv).
  
Definition Gprog : funspecs := ltac:(with_library prog [msort_spec; merge_spec]).

 (** *** Proof of merge *)

Lemma body_merge: semax_body Vprog Gprog f_merge merge_spec.
Proof.
start_function. 
VST.floyd.forward.forward.
VST.floyd.forward.forward.
forward_for_simple_bound (Z.of_nat sizeA + Z.of_nat sizeB)
 (EX i : Z, EX x : nat, EX y : nat, EX cRes' : list val, (* i is the index in the loop and x/y are the positions in the respective array *)
   PROP (i <= (Z.of_nat sizeA + Z.of_nat sizeB); i = (Z.add (Z.of_nat x) (Z.of_nat y)); le x sizeA; le y sizeB;
        Zlength cRes' = i;
        Forall (fun a => Forall (I_cmp Cle a) (sublist x (length cA) cA)) cRes'; Forall (fun a => Forall (I_cmp Cle a) (sublist y (length cB) cB)) cRes';
        Sorted (I_cmp Cle) cRes';
        Forall (fun x => is_int I32 Signed x) cA; Forall (fun x => is_int I32 Signed x) cB;
        Permutation (sublist 0 x cA ++ sublist 0 y cB) cRes')
   LOCAL (temp _a (Vint (Int.repr (Z.of_nat sizeA)));
          temp _b (Vint (Int.repr (Z.of_nat sizeB)));
          temp _A A;
          temp _B B;
          temp _res res;
          temp _x (Vint (Int.repr (Z.of_nat x)));
          temp _y (Vint (Int.repr (Z.of_nat y))))
   SEP (data_at shA (tarray tint (Z.of_nat sizeA)) cA A; data_at shB (tarray tint (Z.of_nat sizeB)) cB B; 
        data_at Ews (tarray tint (Z.of_nat sizeA + Z.of_nat sizeB)) (cRes' ++ (list_repeat (sizeA + sizeB - Z.to_nat i) Vundef)) res)).
   - (* initially the loop invariant is satisfied *)
     Exists 0%nat 0%nat (@nil val).
     entailer!.
     cbn.
     erewrite Coq.Arith.PeanoNat.Nat.sub_0_r.
     entailer!.
   - (* the loop body preserves the loop invariant *)
     Intros.
     forward_if 
      (EX min : int, EX x' : nat, EX y' : nat, (* min is the minimum of the values at the current positions the in the two arrays. x' and y' are the new indices after the if  *)
        PROP (Sorted (I_cmp Cle) (cRes' ++ [Vint min]);
              Forall (fun x => is_int I32 Signed x) cA; Forall (fun x => is_int I32 Signed x) cB;
              Permutation (sublist 0 x' cA ++ sublist 0 y' cB) (cRes'++[Vint min]);
              (x' + y')%nat = ((x + y) + 1)%nat;
              (x <= x')%nat; (x' <= (NPeano.Nat.min (S x) (length cA)))%nat; (y <= y')%nat; (y' <= (NPeano.Nat.min (S y) (length cB)))%nat;
                 ((x < (length cA))%nat  /\ (y < (length cB))%nat  /\ min = I_min (Clt) (nth x cA Vundef) (nth y cB Vundef)) 
              \/ ((x >= (length cA))%nat /\ (y < (length cB))%nat  /\ min = force_int (nth y cB Vundef)) 
              \/ ((x < (length cA))%nat  /\ (y >= (length cB))%nat /\ min = force_int (nth x cA Vundef)))
        LOCAL (temp _a (Vint (Int.repr (Z.of_nat sizeA)));
                temp _b (Vint (Int.repr (Z.of_nat sizeB)));
                temp _A A;
                temp _B B;
                temp _res res;
                temp _x (Vint (Int.repr (Z.of_nat x')));
                temp _y (Vint (Int.repr (Z.of_nat y')));
                temp _i (Vint (Int.repr i)))
        SEP (data_at shA (tarray tint (Z.of_nat sizeA)) cA A; data_at shB (tarray tint (Z.of_nat sizeB)) cB B;
             data_at Ews (tarray tint ((Z.of_nat sizeA) + (Z.of_nat sizeB))) (cRes' ++ [Vint min] ++ list_repeat (sizeA + sizeB - (Z.to_nat i + 1)) Vundef) res)).
      + (* The end of A is not reached yet *)
        forward_if.
        * (* The end of B is not reached yet *)
          VST.floyd.forward.forward.
          { entailer!. eapply (Forall_is_int _ _ _ _ _ H4 H19 H16). }
          { 
            VST.floyd.forward.forward.
            { entailer!. eapply (Forall_is_int _ _ _ _ _ H5 H23 H17). }
            {
              forward_if.
              { (* The current minimum is in A *)
                VST.floyd.forward.forward.
                VST.floyd.forward.forward.
                VST.floyd.forward.forward.
                Exists (force_int (nth x cA Vundef)) (S x) y.
                entailer!.
                {
                  repeat apply conj.
                  { 
                    eapply append_sorted; [auto|].
                    erewrite int_id.
                    2: eapply (Forall_nth _ _); [eapply H4| eapply (Z_lt_length cA sizeA x H22 H16)].
                    eapply (Forall_sublist_cmp cRes' cA (I_cmp Cle) x Vundef).
                    { eapply (Z_lt_length cA sizeA x H22 H16). }
                    { auto. }
                  }
                  { 
                    erewrite int_id.
                    2: eapply (Forall_nth _ _); [eapply H4| eapply (Z_lt_length cA sizeA x H22 H16)].
                    eapply sublist_permutation; [|easy].
                    eapply (Z_lt_length cA sizeA x H22 H16).
                  }
                  { epose (Z_lt_length cA sizeA x H22 H16). erewrite min_l; now easy. }
                  { epose (Z_lt_length cB sizeB y H25 H17). erewrite min_l; [lia|assumption]. }
                  { 
                    left.
                    repeat apply conj. 
                      { eapply (Z_lt_length cA sizeA x H22 H16). }
                      { eapply (Z_lt_length cB sizeB y H25 H17). }
                      { 
                        do 2 erewrite <- Znth_nth_eq in H18.
                        unfold force_int.
                        destruct (nth x cA Vundef), (nth y cB Vundef); cbn in H18; try now auto.
                        { unfold I_min. cbn in *. destruct (Int.lt i i0); easy. } 
                        { eapply (Z_lt_length cB sizeB y H25 H17). }
                        all: eapply (Z_lt_length cA sizeA x H22 H16).
                      }
                  }
                  { do 2 f_equal. lia. }
                }      
                { 
                  erewrite int_id.
                  2: eapply (Forall_nth _ _); [eapply H4| eapply (Z_lt_length cA sizeA x H22 H16)].
                  cbn.
                  erewrite <- Znth_nth_eq; [|eapply (Z_lt_length cA sizeA x H22 H16)].
                  erewrite list_invariant; [entailer!|lia|lia|].
                  erewrite <- Nat2Z.inj_add in H11.
                  erewrite Zlength_length_eq in H11.
                  lia.
                }
              }
              { (* The current minimum is in B *)
                VST.floyd.forward.forward.
                VST.floyd.forward.forward.
                VST.floyd.forward.forward.
                Exists (force_int (nth y cB Vundef)) (x) (S y).
                entailer!.
                { 
                  erewrite int_id. 2: eapply (Forall_nth _ _); [eapply H5| eapply (Z_lt_length cB sizeB y H25 H17)].
                  repeat apply conj.
                  {
                    eapply append_sorted; [auto|].
                    eapply (Forall_sublist_cmp cRes' cB (I_cmp Cle) y Vundef).
                    { eapply (Z_lt_length cB sizeB y H25 H17). }
                    { auto. }
                  }
                  { eapply sublist_permutation2; [|easy]. eapply (Z_lt_length cB sizeB y H25 H17). }
                  { epose (Z_lt_length cA sizeA x H22 H16). erewrite min_l; [lia|assumption]. }
                  { epose (Z_lt_length cB sizeB y H25 H17). erewrite min_l ; now easy. }
                  {
                    left; repeat apply conj. 
                      { eapply (Z_lt_length cA sizeA x H22 H16). }
                      { eapply (Z_lt_length cB sizeB y H25 H17). }
                      { 
                        do 2 erewrite <- Znth_nth_eq in H18.
                        2: eapply (Z_lt_length cB sizeB y H25 H17).
                        2,3: eapply (Z_lt_length cA sizeA x H22 H16).
                        unfold force_int.
                        destruct (nth x cA Vundef), (nth y cB Vundef); cbn in H18; try now auto.
                        unfold I_min.
                        cbn in *.
                        destruct (Int.lt i i0); easy.
                      }
                  }
                  { do 2 f_equal. lia. }
                }      
                { 
                  erewrite int_id.
                  2: eapply (Forall_nth _ _); [eapply H5| eapply (Z_lt_length cB sizeB y H25 H17)].
                  cbn.
                  erewrite <- Znth_nth_eq; [|eapply (Z_lt_length cB sizeB y H25 H17)].
                  erewrite list_invariant2; [entailer!|lia|lia|].
                  erewrite <- Nat2Z.inj_add in H11.
                  erewrite Zlength_length_eq in H11.
                  lia.
                } 
              } 
            }
          }
        * (* The end of B has been reached *)
          VST.floyd.forward.forward.
          { entailer!. eapply (Forall_is_int _ _ _ _ _ H4 H19 H16). }
          { 
            VST.floyd.forward.forward.
            VST.floyd.forward.forward.
            Exists (force_int (nth x cA Vundef)) (S x) y.
            entailer!.
            { 
              erewrite int_id. 2: eapply (Forall_nth _ _); [eapply H4|eapply (Z_lt_length cA sizeA x H20 H16)].
              repeat apply conj.
              {
                eapply append_sorted; [auto|].
                eapply (Forall_sublist_cmp cRes' cA (I_cmp Cle) x Vundef).
                { eapply (Z_lt_length cA sizeA x H20 H16). }
                { auto. }
              }
              { eapply sublist_permutation; [|easy]. eapply (Z_lt_length cA sizeA x H20 H16). }
              { epose (Z_lt_length cA sizeA x H20 H16). erewrite min_l; now easy. }
              { 
                epose (Z_ge_length cB sizeB y H23 H17).
                pose H23.
                erewrite Zlength_length_eq in e.
                eapply Nat2Z.inj in e.
                rewrite <- e in H10.
                erewrite min_r; [easy|lia].
              }
              { 
                do 2 right. repeat apply conj. 
                  { eapply (Z_lt_length cA sizeA x H20 H16). }
                  { eapply (Z_ge_length cB sizeB y H23 H17). }
                  { easy. }
              }
              { do 2 f_equal. lia. }
            }
            { 
              erewrite int_id.
              2: eapply (Forall_nth _ _); [eapply H4|eapply (Z_lt_length cA sizeA x H20 H16)].
              cbn.
              erewrite <- Znth_nth_eq; [|eapply (Z_lt_length cA sizeA x H20 H16)].
              erewrite list_invariant; [entailer!|lia|lia|].
              erewrite <- Nat2Z.inj_add in H11.
              erewrite Zlength_length_eq in H11.
              lia. 
            }
          }
      + (* The end of A has been reached *)
        forward_if.
        * (* The end of B is not reached yet *)
          VST.floyd.forward.forward. 
          { entailer!. eapply (Forall_is_int _ _ _ _ _ H5 H22 H17). } 
          { 
            VST.floyd.forward.forward.
            VST.floyd.forward.forward.
            Exists (force_int (nth y cB Vundef)) (x) (S y).
            entailer!.
            { 
              erewrite int_id.
              2: eapply (Forall_nth _ _); [eapply H5|eapply (Z_lt_length cB sizeB y H23 H17)].
              repeat apply conj.
              { 
                eapply append_sorted; [auto|].
                eapply (Forall_sublist_cmp cRes' cB (I_cmp Cle) y Vundef).
                { eapply (Z_lt_length cB sizeB y H23 H17). }
                { auto. }
              }
              { eapply sublist_permutation2; [|easy]. eapply (Z_lt_length cB sizeB y H23 H17). }
              {
                epose (Z_ge_length cA sizeA x H20 H16).
                pose H20.
                erewrite Zlength_length_eq in e.
                eapply Nat2Z.inj in e.
                rewrite <- e in H9.
                erewrite min_r; [easy|lia].
              }
              { epose (Z_lt_length cB sizeB y H23 H17). erewrite min_l; now easy. }
              { 
                right. left. repeat apply conj. 
                { eapply (Z_ge_length cA sizeA x H20 H16). }
                { eapply (Z_lt_length cB sizeB y H23 H17). }
                { easy. }
              }
              { do 2 f_equal. lia. }
            }
            { 
              erewrite int_id.
              2: eapply (Forall_nth _ _); [eapply H5|eapply (Z_lt_length cB sizeB y H23 H17)].
              cbn.
              erewrite <- Znth_nth_eq; [|eapply (Z_lt_length cB sizeB y H23 H17)].
              erewrite list_invariant2; [entailer!|lia|lia|].
              erewrite <- Nat2Z.inj_add in H11.
              erewrite Zlength_length_eq in H11.
              lia.
            }
          }
        * (* The end of B has been reached, too. This case will not be reached in the loop because then i >= sizeA + size B *)
          VST.floyd.forward.forward.
          lia.
      + Intros min x' y'.
        Exists x' y' (cRes' ++ [Vint min]).
        entailer!.
        { repeat apply conj.
          { erewrite Zlength_length_eq in H25. erewrite <- (Nat2Z.inj (length cA)); [lia|easy]. }
          { erewrite Zlength_length_eq in H28. erewrite <- (Nat2Z.inj (length cB)); [lia|easy]. }
          {
            erewrite Zlength_length_eq.
            erewrite <- Nat2Z.inj_add.
            erewrite app_length; cbn.
            erewrite Nat2Z.inj_add; cbn.
            f_equal.
            erewrite <- Zlength_length_eq.
            lia.
          }
          { now apply (Forall_min_invariant x x' y cA cB cRes' min H23 H19 H20 H4 H5 H). }
          { 
            destruct (invariant_disj_equiv x y cA cB min) as [? _].
            apply (Forall_min_invariant y y' x cB cA cRes' min (H8 H23) H21 H22 H5 H4 H0 H13).
          }
        }
        { 
          assert (((sizeA + sizeB)%nat - (Z.to_nat (Z.of_nat x + Z.of_nat y) + 1))%nat 
                  = ((sizeA + sizeB)%nat - Z.to_nat (Z.of_nat x + Z.of_nat y + 1))%nat) by lia.
          rewrite H8.
          rewrite app_assoc.
          entailer!.
        }
 - Intros x y cRes'.
   Exists cRes'.
   entailer!.
    {
      assert (x = sizeA)%nat by lia; assert (y = sizeB)%nat by lia.
      rewrite H23 in H13; rewrite H24 in H13.
      unfold sublist in H13.
      erewrite Zlength_length_eq in H15; erewrite Zlength_length_eq in H18.
      eapply Nat2Z.inj in H15; eapply Nat2Z.inj in H18.
      rewrite <- H15 in H13; rewrite <- H18 in H13.
      do 2 erewrite firstn_length_eq in H13; [now cbn in H13|constructor|constructor|constructor].
    }
    {
      assert (sizeA + sizeB - Z.to_nat (Z.of_nat sizeA + Z.of_nat sizeB) = 0)%nat by lia.
      rewrite H23; cbn.
      erewrite app_nil_r.
      entailer!.
    }
Qed.

 (** *** Proof of msort *)

Lemma body_msort: semax_body Vprog Gprog f_msort msort_spec.
Proof.
start_function.
assert (sizeMax : (Z.of_nat size <= Int.max_signed)) by lia.
rename H1 into sizePos.
forward_if.
{
  (* The array has size 1 -> already sorted *)
  forward_call (tarray tint 1, gv).
  {
    repeat apply conj; destruct size; cbn; now try lia.
  }
  {
    Intros res.
    destruct (eq_dec res nullval).
    {
      rewrite e.
      forward_if (
        (PROP (res <> nullval)
        LOCAL (temp _res res)
        SEP ())).
      { forward_call 1; easy. }
      { contradiction. }
      { now Intros. }
    }
    {
      forward_if (
        (PROP (res <> nullval; length contents = size)
        LOCAL (temp _res res; gvars gv; temp _array array; temp _size (Vint (Int.repr (Z.of_nat size))))
        SEP (mem_mgr gv;
             malloc_token Ews (tarray tint (Z.of_nat size)) res * data_at_ Ews (tarray tint (Z.of_nat size)) res;
             data_at sh (tarray tint (Z.of_nat size)) contents array))).
        { forward_call 1; contradiction. }
        { 
          VST.floyd.forward.forward.
          entailer!. 
          { erewrite Zlength_length_eq in H6. now eapply Nat2Z.inj in H6. }
          {
            rewrite H1.
            entailer!.
          }
        }
        {
          Intros.
          VST.floyd.forward.forward.
          {
            entailer!.
            unfold Znth.
            destruct (zlt 0 0); [lia|].
            now dependent elimination H; cbn in *; [lia|].
          }
          {
            VST.floyd.forward.forward.
            VST.floyd.forward.forward.
            Exists res contents.
            entailer!.
            {
              destruct contents as [|]; cbn in *; [cbn in H1; lia|destruct contents; cbn in *; [|lia]].
              repeat constructor.
            }
            {
              destruct contents as [|]; cbn in *; [cbn in H1; lia|destruct contents; cbn in *; [|lia]].
              entailer!.
            }
          }
        }
    }
  }
}
{
  (* The array has size > 1 *)
  forward_call (tarray tint (Z.of_nat size), gv).
  {
    entailer!; cbn.
    erewrite Z.mul_comm.
    repeat f_equal.
    lia.
  }
  {
    repeat apply conj; destruct size; cbn; try lia; try reflexivity.
    unfold Int.max_signed, Int.half_modulus, Int.modulus in *; cbn in *.
    lia. 
  }
  {
    Intros res.
    destruct (eq_dec res nullval).
    {
      rewrite e.
      forward_if (
        (PROP (res <> nullval)
        LOCAL (temp _res res)
        SEP ())
      ).
        { forward_call 1; easy. }
        { contradiction. }
        { now Intros. }
    }
    {
      forward_if (
        (PROP (res <> nullval; length contents = size)
         LOCAL (temp _res__1 res; gvars gv; temp _array array;
                temp _size (Vint (Int.repr (Z.of_nat size))))
         SEP (mem_mgr gv;
              malloc_token Ews (tarray tint (Z.of_nat size)) res *
              data_at_ Ews (tarray tint (Z.of_nat size)) res;
              data_at sh (tarray tint (Z.of_nat size)) contents array))). 
        { forward_call 1; contradiction. }
        { VST.floyd.forward.forward. entailer!. erewrite Zlength_length_eq in H6. now eapply Nat2Z.inj in H6. }
        {
          Intros.
          forward_call (array, sublist 0 (size/2) contents, sh, (size / 2)%nat, gv).
          {
            unfold Int.mone in H2; destruct H2.
            assert (2 <> -1) by lia.
            apply H9.
            eapply (repr_inj_signed 2 (-1)); unfold repable_signed, Int.min_signed, Int.max_signed; easy.
          }
          {
            entailer!. cbn -[Nat.div Nat.modulo]. repeat f_equal.
            now eapply int_nat_div2_eq.
          }
          {
            entailer!.
            erewrite <- (firstn_length_eq contents (length contents)) at 4; [|lia].
            pose (le_plus_minus (length contents / 2) (length contents)).
            erewrite e at 4.
            {
              erewrite <- firstn_app.
              erewrite (split2_data_at_Tarray_app (Z.of_nat (length contents / 2))); [entailer!| |]; rewrite Zlength_length_eq; f_equal.
              1: rewrite firstn_length_le; try easy; eapply Nat_div_2_le.
              erewrite <- Nat2Z.inj_sub; [|eapply Nat_div_2_le].
              f_equal.
              erewrite firstn_length_le; [easy|].
              erewrite List.skipn_length; lia.
            }
            {
              eapply Nat_div_2_le.
            }
          }
          {
            repeat apply conj; [easy| | |].
            eapply (Forall_firstn_weaken (length contents)); [rewrite H2; eapply Nat_div_2_le|].
            rewrite firstn_length_eq; [easy|lia].
            eapply (Z.le_trans (Z.of_nat (size / 2) * 4) (Z.of_nat size * 4)); [|easy].
            eapply Z.mul_le_mono_nonneg; try lia.
            eapply Nat2Z.inj_le.
            eapply Nat_div_2_le.
            destruct size as [|[|]]; [lia|lia|].
            unfold gt, lt.
            assert (2 / 2 = 1)%nat; [now cbn|].
            rewrite <- H3 at 1.
            eapply Nat2Z.inj_le.
            repeat erewrite div_Zdiv; [|lia|lia].
            eapply Z.ge_le_iff; eapply Z_div_ge; lia.
          }
          {
            Intros vret0; destruct vret0 as [A cA].
            (* The first argument is the address of the second half of the input array *)
            forward_call ((field_address0 (tarray tint (Z.of_nat (Datatypes.length contents))) [ArraySubsc (Z.of_nat (Datatypes.length contents / 2))] array),
                          sublist (size/2) (length contents) contents, sh, (size / 2 + Nat.modulo size 2)%nat, gv).
            {
              repeat apply conj. 1,2,3: intros ?; unfold Int.mone;
              destruct H2 as [_ H20];
              assert (2 <> -1) by lia;
              apply H2;
              eapply (repr_inj_signed 2 (-1)); unfold repable_signed, Int.min_signed, Int.max_signed; easy.
              all: now eapply size_div2_mod2_int_range.
            }
            {
              entailer!. cbn -[Nat.div Nat.modulo]. repeat f_equal. 
              {
                unfold Int.divs.
                repeat erewrite Int.signed_repr; unfold Int.max_signed, Int.half_modulus, Int.modulus in *; cbn in *; try lia.
                change ((fst (Nat.divmod (Datatypes.length contents) 1 0 1))) with ((length contents) / 2)%nat in *.
                rewrite Z.quot_div_nonneg; [|lia|lia]. Search Cop.sem_add_ptr_int field_address0.
                unfold field_address0 in *.
                unfold Cop.sem_add_ptr_int; cbn in *.
                destruct array; try easy; cbn in *. 
                {
                  unfold field_compatible in *; cbn in *; easy.
                }
                {
                  unfold field_address0. 
                  destruct (field_compatible0_dec _ _).
                  {
                    cbn; repeat f_equal.
                    unfold Ptrofs.mul.
                    f_equal.
                    autorewrite with norm.
                    erewrite Int.signed_repr.
                    unfold Ptrofs.unsigned.
                    repeat erewrite Ptrofs.unsigned_repr.
                    f_equal.
                    change ((fst (Nat.divmod (Datatypes.length contents) 1 0 1))) with ((length contents) / 2)%nat.
                    change 2 with (Z.of_nat 2).
                    now erewrite div_Zdiv; lia.
                    {
                      apply conj; eapply Z.ge_le_iff; [eapply Z_div_ge0; lia|].
                      unfold Ptrofs.max_unsigned, Ptrofs.modulus; cbn.
                      eapply (Zge_trans _  (Z.of_nat (Datatypes.length contents))); [lia|erewrite Z.ge_le_iff; eapply Z_div_2_le].
                    }
                    {
                      apply conj; unfold Ptrofs.max_unsigned, Ptrofs.modulus; cbn; lia.
                    }
                    {
                      apply conj; unfold Int.half_modulus, Int.modulus in *; cbn in *.
                      change 2 with (Z.of_nat 2); erewrite <- div_Zdiv; try lia.
                      eapply Z.ge_le_iff; eapply (Zge_trans _  (Z.of_nat (Datatypes.length contents))); [lia|eapply Z.ge_le_iff; eapply Z_div_2_le].
                    }
                  }
                  {
                    unfold field_compatible, isptr in H16.
                    easy.
                  }
                }
              }
              { now eapply int_nat_div2_mod2_eq. }
            }
            {
              entailer!.
              erewrite <- skipn_firstn.
              erewrite firstn_length_eq at 1; [|lia].
              erewrite <- Nat2Z.inj_sub; [|eapply Nat_div_2_le].
              erewrite <- Nat_div_2.
              entailer!.
              unfold sublist.
              erewrite (firstn_length_eq contents (Datatypes.length contents)); [|lia].
              entailer!.
            }
            {
              repeat apply conj; [easy| | |].
              {
                unfold sublist.
                erewrite firstn_length_eq; [|lia].
                change contents with (skipn 0 contents) in H.
                eapply Forall_skipn_weaken in H; [eapply H|lia].
              }
              {
                eapply (Z.le_trans _ (Z.of_nat size * 4)); [|easy].
                erewrite <- Nat_div_2.
                lia.
              }
              {
                unfold gt.
                erewrite <- Nat_div_2.
                eapply ArithProp.lt_minus_O_lt.
                eapply Nat_div_2_lt; lia.
              }
            }
            {
              Intros vret; destruct vret as [B cB].
              forward_call (A,B,res,cA,cB,Ews,Ews,(Nat.div size 2),(Nat.div size 2 + Nat.modulo size 2)%nat).
              {
                repeat apply conj. 1,2,5: intros ?; unfold Int.mone;
                destruct H2 as [_ ?];
                assert (2 <> -1) by lia;
                try apply H2;
                try eapply (repr_inj_signed 2 (-1)); unfold repable_signed, Int.min_signed, Int.max_signed; easy.
                all: now eapply size_div2_mod2_int_range.
              }
              {
                entailer!. cbn -[Nat.div Nat.modulo]. repeat f_equal.
                { now eapply int_nat_div2_eq. }
                { now eapply int_nat_div2_mod2_eq. }
              }
              {
                erewrite <- Nat_div_2.
                erewrite <- Nat2Z.inj_add.
                erewrite <- le_plus_minus; [|eapply Nat_div_2_le].
                unfold data_at_, field_at_. cbn.
                erewrite Nat2Z.id.
                entailer!.
              }
              {
                assert (1 <= Z.of_nat (size / 2 + size mod 2)).
                {
                  eapply Z2Nat.inj_le; [lia|lia|].
                  cbn -[Nat.div Nat.modulo].
                  erewrite Nat2Z.id.
                  erewrite <- Nat_div_2.
                  eapply ArithProp.lt_minus_O_lt.
                  eapply Nat_div_2_lt; lia.
                }
                assert (1 <= Z.of_nat (size / 2)).
                {
                  assert (1 = 2 / 2) by (cbn; lia).
                  rewrite H10.
                  erewrite div_Zdiv; [cbn -[Z.div]|lia].
                  eapply Z_div_le; lia.
                }
                repeat apply conj; try easy; auto; try lia; cbn [snd] in *.
                1,2: now eapply StronglySorted_Sorted.
                {
                  erewrite div_Zdiv; [cbn|lia].
                  eapply (Z.le_trans _ (Z.of_nat size)); [eapply Z_div_2_le|unfold Int.max_signed, Int.half_modulus, Int.modulus in *; cbn in *; lia].
                }
                {
                  eapply (Z.le_trans _ (Z.of_nat size * 4)); [|easy].
                  erewrite <- Nat_div_2.
                  lia.
                }
                {
                  erewrite <- Nat_div_2.
                  erewrite <- Nat2Z.inj_add.
                  erewrite <- le_plus_minus; [lia|eapply Nat_div_2_le].
                }
                all: eapply Permutation_Forall.
                1: exact H3.
                2: exact H6.
                { unfold sublist; cbn; now eapply Forall_firstn. }
                { unfold sublist; cbn; eapply Forall_skipn; erewrite firstn_length_eq; [easy|lia]. }
              }
              {
                Intros merged.
                forward_call (tarray tint (Z.of_nat (Datatypes.length (firstn (fst (Nat.divmod (Datatypes.length contents) 1 0 1)) contents))), A, gv).
                {
                  cbn [fst] in *.
                  destruct (eq_dec A nullval); [easy|].
                  erewrite firstn_length_le; [|eapply Nat_div_2_le].
                  entailer!.
                }
                {
                  forward_call (tarray tint (Z.of_nat (Datatypes.length contents / 2 + Datatypes.length contents mod 2)), B, gv).
                  {
                    cbn [fst] in *.
                    destruct (eq_dec B nullval); [easy|].
                    entailer!.
                    erewrite <- Nat_div_2.
                    erewrite firstn_length_eq; [|lia].
                    erewrite List.skipn_length.
                    change (fst (Nat.divmod (Datatypes.length contents) 1 0 1)) with (length contents / 2)%nat.
                    entailer!.
                  }
                  {
                    VST.floyd.forward.forward.
                    Exists res merged.
                    entailer!.
                    {
                      apply conj.
                      {
                        cbn [snd] in *; unfold sublist in *.
                        erewrite firstn_length_eq in H6.
                        cbn [skipn] in H3.
                        epose (Permutation_app H3 H6).
                        erewrite firstn_skipn in p.
                        eapply (Permutation_trans p H9).
                        lia.
                      }
                      {
                        now eapply (Sorted_StronglySorted I_cmp_le_trans).
                      }
                    }
                    {
                      erewrite <- Nat2Z.inj_add.
                      erewrite <- le_plus_minus; [|eapply Nat_div_2_le].
                      entailer!.
                      erewrite sepcon_comm.
                      erewrite Nat2Z.inj_sub; [|eapply Nat_div_2_le].
                      erewrite <- (split2_data_at_Tarray_app (Z.of_nat (length contents / 2)) (Z.of_nat (Datatypes.length contents)) sh tint _ _ array).
                      {
                        erewrite firstn_skipn.
                        entailer!.
                      }
                      {
                        erewrite Zlength_length_eq; f_equal.
                        erewrite firstn_length_le; [easy|eapply Nat_div_2_le].
                      }
                      {
                        erewrite Zlength_length_eq.
                        erewrite <- Nat2Z.inj_sub; [f_equal|eapply Nat_div_2_le].
                        now erewrite skipn_length. 
                      }
                    }
                  }
                }
              }
            }
          }
        }
    }
  }
}
Qed.