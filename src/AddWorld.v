From sflib Require Import sflib.
Require Import Coq.Classes.RelationClasses.
From Fairness Require Import Axioms NatStructs.
From Fairness Require Import PCM World.
From Fairness Require Import Mod.
Require Import String.

Set Implicit Arguments.

Definition ths_merge (ths0 ths1 ths_sum: TIdSet.t): Prop. Admitted.

Lemma ths_merge_empty
  :
  ths_merge TIdSet.empty TIdSet.empty TIdSet.empty.
Admitted.

Lemma ths_merge_add_l ths0 ths1 ths_sum
      tid ths_sum'
      (MERGE: ths_merge ths0 ths1 ths_sum)
      (ADD: TIdSet.add_new tid ths_sum ths_sum')
  :
  exists ths0',
    (<<MERGE: ths_merge ths0' ths1 ths_sum'>>) /\
      (<<ADD: TIdSet.add_new tid ths0 ths0'>>).
Admitted.

Lemma ths_merge_add_r ths0 ths1 ths_sum
      tid ths_sum'
      (MERGE: ths_merge ths0 ths1 ths_sum)
      (ADD: TIdSet.add_new tid ths_sum ths_sum')
  :
  exists ths1',
    (<<MERGE: ths_merge ths0 ths1' ths_sum'>>) /\
      (<<ADD: TIdSet.add_new tid ths1 ths1'>>).
Admitted.

Lemma ths_merge_remove_l ths0 ths1 ths_sum
      tid ths0'
      (MERGE: ths_merge ths0 ths1 ths_sum)
      (REMOVE: TIdSet.remove tid ths0 = ths0')
      (IN: TIdSet.In tid ths0)
  :
  exists ths_sum',
    (<<MERGE: ths_merge ths0' ths1 ths_sum'>>) /\
      (<<REMOVE: TIdSet.remove tid ths_sum = ths_sum'>>).
Admitted.

Lemma ths_merge_remove_r ths0 ths1 ths_sum
      tid ths1'
      (MERGE: ths_merge ths0 ths1 ths_sum)
      (REMOVE: TIdSet.remove tid ths1 = ths1')
      (IN: TIdSet.In tid ths1)
  :
  exists ths_sum',
    (<<MERGE: ths_merge ths0 ths1' ths_sum'>>) /\
      (<<REMOVE: TIdSet.remove tid ths_sum = ths_sum'>>).
Admitted.



Definition threadsRA: URA.t. Admitted.

Definition global_th (ths_ctx ths_usr: TIdSet.t): threadsRA. Admitted.

Definition local_th_context (tid: thread_id): threadsRA. Admitted.

Definition local_th_user (tid: thread_id): threadsRA. Admitted.

Lemma local_th_context_in_context ths_ctx ths_usr tid r_ctx
      (VALID: URA.wf (global_th ths_ctx ths_usr ⋅ local_th_context tid ⋅ r_ctx))
  :
  TIdSet.In tid ths_ctx.
Admitted.

Lemma local_th_user_in_context ths_ctx ths_usr tid r_ctx
      (VALID: URA.wf (global_th ths_ctx ths_usr ⋅ local_th_user tid ⋅ r_ctx))
  :
  TIdSet.In tid ths_usr.
Admitted.

Lemma initial_global_th_valid
  :
  URA.wf (global_th TIdSet.empty TIdSet.empty).
Admitted.

Lemma glboal_th_alloc_context ths_ctx0 ths_usr r_ctx
      tid ths_ctx1
      (VALID: URA.wf (global_th ths_ctx0 ths_usr))
      (ADD: TIdSet.add_new tid ths_ctx0 ths_ctx1)
      (NONE: ~ TIdSet.In tid ths_usr)
  :
  URA.wf (global_th ths_ctx1 ths_usr ⋅ local_th_context tid ⋅ r_ctx).
Admitted.

Lemma glboal_th_alloc_user ths_ctx ths_usr0 r_ctx
      tid ths_usr1
      (VALID: URA.wf (global_th ths_ctx ths_usr0))
      (ADD: TIdSet.add_new tid ths_usr0 ths_usr1)
      (NONE: ~ TIdSet.In tid ths_ctx)
  :
  URA.wf (global_th ths_ctx ths_usr1 ⋅ local_th_user tid ⋅ r_ctx).
Admitted.

Lemma glboal_th_dealloc_context ths_ctx0 ths_usr r_ctx
      tid ths_ctx1
      (VALID: URA.wf (global_th ths_ctx0 ths_usr ⋅ local_th_context tid ⋅ r_ctx))
      (REMOVE: TIdSet.remove tid ths_ctx0 = ths_ctx1)
  :
  URA.wf (global_th ths_ctx1 ths_usr ⋅ URA.unit ⋅ r_ctx).
Admitted.

Lemma glboal_th_dealloc_user ths_ctx ths_usr0 r_ctx
      tid ths_usr1
      (VALID: URA.wf (global_th ths_ctx ths_usr0 ⋅ local_th_context tid ⋅ r_ctx))
      (REMOVE: TIdSet.remove tid ths_usr0 = ths_usr1)
  :
  URA.wf (global_th ths_ctx ths_usr1 ⋅ URA.unit ⋅ r_ctx).
Admitted.
