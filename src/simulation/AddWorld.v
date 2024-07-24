From sflib Require Import sflib.
Require Import Coq.Classes.RelationClasses.
From Fairness Require Import Axioms NatStructsLarge.
From Fairness Require Import PCM World.
From Fairness Require Import Mod.
Require Import String Lia Program.

Set Implicit Arguments.

Section THREADS_RA_DEF.

  Inductive threadsRA_car : Type :=
  | global_local
      (ths_ctx ths_usr : TIdSet.t)
      (ths_ctx' ths_usr' : TIdSet.t)
  | local (ths_ctx' ths_usr' : TIdSet.t)
  | boom
  .

  Inductive threadsRA_wf : threadsRA_car -> Prop :=
  | wf_global_local ths_ctx ths_usr ths_ctx' ths_usr'
      (DISJOINT : NatMapP.Disjoint ths_ctx ths_usr)
      (LE_CTX : KeySetLE ths_ctx' ths_ctx)
      (LE_USR : KeySetLE ths_usr' ths_usr)
    : threadsRA_wf (global_local ths_ctx ths_usr ths_ctx' ths_usr')
  | wf_local ths_ctx' ths_usr'
    : threadsRA_wf (local ths_ctx' ths_usr')
  .

  Definition add (r1 r2 : threadsRA_car) : threadsRA_car :=
    match r1, r2 with
    | global_local ths_ctx ths_usr ths_ctx' ths_usr', global_local _ _ _ _      => boom
    | global_local ths_ctx ths_usr ths_ctx' ths_usr', local ths_ctx'' ths_usr'' =>
        if (disjoint ths_ctx' ths_ctx'' && disjoint ths_usr' ths_usr'')%bool
        then global_local ths_ctx ths_usr (NatMapP.update ths_ctx' ths_ctx'') (NatMapP.update ths_usr' ths_usr'')
        else boom
    | global_local ths_ctx ths_usr ths_ctx' ths_usr', boom                      => boom
    | local ths_ctx' ths_usr', global_local ths_ctx ths_usr ths_ctx'' ths_usr'' =>
        if (disjoint ths_ctx' ths_ctx'' && disjoint ths_usr' ths_usr'')%bool
        then global_local ths_ctx ths_usr (NatMapP.update ths_ctx' ths_ctx'') (NatMapP.update ths_usr' ths_usr'')
        else boom
    | local ths_ctx' ths_usr', local ths_ctx'' ths_usr''                        =>
        if (disjoint ths_ctx' ths_ctx'' && disjoint ths_usr' ths_usr'')%bool
        then local (NatMapP.update ths_ctx' ths_ctx'') (NatMapP.update ths_usr' ths_usr'')
        else boom
    | local ths_ctx' ths_usr', boom                                             => boom
    | boom, _                                                                   => boom
    end.
  Program Instance threadsRA: URA.t :=
    {|
      URA.car := threadsRA_car;
      URA.unit := local NatSet.empty NatSet.empty;
      URA._wf := threadsRA_wf;
      URA._add := add;
      URA.core := fun _ => local NatSet.empty NatSet.empty;
    |}.
  Next Obligation.
    destruct a, b; ss.
    all: rewrite disjoint_comm with (x := ths_ctx').
    all: rewrite disjoint_comm with (x := ths_usr').
    all: rewrite union_comm with (x := ths_ctx').
    all: rewrite union_comm with (x := ths_usr').
    all: ss.
  Qed.
  Next Obligation.
    destruct a, b, c; try (ss; des_ifs; fail).
    all: unfold add; des_ifs; try (rewrite 2 union_assoc; ss); solve_disjoint!.
  Qed.
  Next Obligation.
    unseal "ra". destruct a; try easy.
    all:
      unfold add; des_ifs; try (do 2 rewrite union_comm, union_empty; ss);
      unfold NatSet.empty in Heq; solve_disjoint!.
  Qed.
  Next Obligation.
    unseal "ra". econs.
  Qed.
  Next Obligation.
    unseal "ra". destruct a, b; inv H; unfold add; des_ifs; econs; ss.
    - assert (KeySetLE ths_ctx' (NatMapP.update ths_ctx' ths_ctx'0)) by eapply union_KeySetLE.
      unfold KeySetLE in *. auto.
    - assert (KeySetLE ths_usr' (NatMapP.update ths_usr' ths_usr'0)) by eapply union_KeySetLE.
      unfold KeySetLE in *. auto.
  Qed.
  Next Obligation.
    unseal "ra". destruct a; ss.
    - f_equal; rewrite union_comm; ss.
    - f_equal; rewrite union_comm; ss.
  Qed.
  Next Obligation.
    exists (local NatSet.empty NatSet.empty). unseal "ra". ss.
  Qed.

End THREADS_RA_DEF.

Section THREADS_RA.

  Definition global_th (ths_ctx ths_usr : TIdSet.t) : threadsRA := global_local ths_ctx ths_usr TIdSet.empty TIdSet.empty.

  Definition local_th_context (tid: thread_id): threadsRA := local (TIdSet.add tid TIdSet.empty) TIdSet.empty.

  Definition local_th_user (tid: thread_id): threadsRA := local TIdSet.empty (TIdSet.add tid TIdSet.empty).

  Lemma local_th_context_in_context ths_ctx ths_usr tid r_ctx
        (VALID: URA.wf (global_th ths_ctx ths_usr ⋅ local_th_context tid ⋅ r_ctx))
    :
    TIdSet.In tid ths_ctx.
  Proof.
    eapply URA.wf_mon in VALID. unfold URA.add, URA.wf in VALID. unseal "ra".
    unfold global_th, local_th_context in *. ss.
    inv VALID. eapply LE_CTX. (do 3 econs); ss.
  Qed.

  Lemma local_th_user_in_user ths_ctx ths_usr tid r_ctx
        (VALID: URA.wf (global_th ths_ctx ths_usr ⋅ local_th_user tid ⋅ r_ctx))
    :
    TIdSet.In tid ths_usr.
    eapply URA.wf_mon in VALID. unfold URA.add, URA.wf in VALID. unseal "ra".
    inv VALID. eapply LE_USR. (do 3 econs); ss.
  Qed.

  Lemma initial_global_th_valid
    :
    URA.wf (global_th TIdSet.empty TIdSet.empty).
  Proof.
    unfold URA.wf. unseal "ra". econs; eauto using Disjoint_empty, KeySetLE_empty.
  Qed.

  Lemma global_th_alloc_context ths_ctx0 ths_usr r_ctx
        tid ths_ctx1
        (VALID: URA.wf (global_th ths_ctx0 ths_usr ⋅ r_ctx))
        (ADD: TIdSet.add_new tid ths_ctx0 ths_ctx1)
        (NONE: ~ TIdSet.In tid ths_usr)
    :
    URA.wf (global_th ths_ctx1 ths_usr ⋅ local_th_context tid ⋅ r_ctx).
  Proof.
    unfold URA.wf, URA.add in *. unseal "ra". destruct r_ctx; ss.
    rewrite ! union_empty in *. unfold union, NatMap.fold; ss. inv VALID. inv ADD. des_ifs.
    - econs; ss.
      + ii. des. eapply NatMapP.F.add_in_iff in H. des.
        * subst. eauto.
        * eapply DISJOINT. eauto.
      + ii. eapply NatMapP.F.add_in_iff. rewrite union_comm in H. eapply NatMapP.F.add_in_iff in H. des; eauto.
    - eapply NatMapP.F.not_find_in_iff in NEW. solve_andb.
      + eapply disjoint_false_iff' in H. des.
        eapply NatMapP.F.add_in_iff in H. rewrite NatMapP.F.empty_in_iff in H.
        des; ss; subst. firstorder.
      + unfold TIdSet.empty in H. solve_disjoint.
  Qed.

  Lemma global_th_alloc_user ths_ctx ths_usr0 r_ctx
        tid ths_usr1
        (VALID: URA.wf (global_th ths_ctx ths_usr0 ⋅ r_ctx))
        (ADD: TIdSet.add_new tid ths_usr0 ths_usr1)
        (NONE: ~ TIdSet.In tid ths_ctx)
    :
    URA.wf (global_th ths_ctx ths_usr1 ⋅ local_th_user tid ⋅ r_ctx).
  Proof.
    unfold URA.wf, URA.add in *. unseal "ra". destruct r_ctx; ss.
    rewrite ! union_empty in *. unfold union, NatMap.fold; ss. inv VALID. inv ADD. des_ifs.
    - econs; ss.
      + ii. des. eapply NatMapP.F.add_in_iff in H0. des.
        * subst. eauto.
        * eapply DISJOINT. eauto.
      + ii. eapply NatMapP.F.add_in_iff. rewrite union_comm in H. eapply NatMapP.F.add_in_iff in H. des; eauto.
    - eapply NatMapP.F.not_find_in_iff in NEW.
      eapply disjoint_false_iff' in Heq. des.
      eapply NatMapP.F.add_in_iff in Heq. rewrite NatMapP.F.empty_in_iff in Heq.
      des; ss; subst. firstorder.
  Qed.

  Lemma global_th_dealloc_context ths_ctx0 ths_usr r_ctx
        tid ths_ctx1
        (VALID: URA.wf (global_th ths_ctx0 ths_usr ⋅ local_th_context tid ⋅ r_ctx))
        (REMOVE: TIdSet.remove tid ths_ctx0 = ths_ctx1)
    :
    URA.wf (global_th ths_ctx1 ths_usr ⋅ URA.unit ⋅ r_ctx).

  Proof.
    rewrite URA.unit_id. unfold URA.wf, URA.add in *. unseal "ra". destruct r_ctx; ss.
    rewrite ! union_empty in *. unfold union, NatMap.fold in VALID; ss. des_ifs; inv VALID.
    econs; ss.
    - ii. des. eapply NatMapP.F.remove_in_iff in H; des. firstorder.
    - unfold TIdSet.empty, TIdSet.add in *. solve_andb; solve_disjoint.
      ii. eapply NatMapP.F.remove_in_iff. assert (tid = k \/ tid <> k) by lia; des.
      + subst. tauto.
      + unfold KeySetLE in LE_CTX. rewrite union_comm in LE_CTX. setoid_rewrite NatMapP.F.add_in_iff in LE_CTX. eauto.
  Qed.

  Lemma global_th_dealloc_user ths_ctx ths_usr0 r_ctx
        tid ths_usr1
        (VALID: URA.wf (global_th ths_ctx ths_usr0 ⋅ local_th_user tid ⋅ r_ctx))
        (REMOVE: TIdSet.remove tid ths_usr0 = ths_usr1)
    :
    URA.wf (global_th ths_ctx ths_usr1 ⋅ URA.unit ⋅ r_ctx).
  Proof.
    rewrite URA.unit_id. unfold URA.wf, URA.add in *. unseal "ra". destruct r_ctx; ss.
    rewrite ! union_empty in *. unfold union, NatMap.fold in VALID; ss. des_ifs; inv VALID.
    unfold TIdSet.empty, TIdSet.add in *. solve_disjoint.
    unfold KeySetLE in LE_USR. rewrite union_comm in LE_USR. setoid_rewrite NatMapP.F.add_in_iff in LE_USR.
    econs; ss.
    - ii. des. eapply NatMapP.F.remove_in_iff in H1. firstorder.
    - ii. rewrite NatMapP.F.remove_in_iff. split.
      + ii. subst. tauto.
      + firstorder.
  Qed.

End THREADS_RA.
