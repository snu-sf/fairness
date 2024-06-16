From Coq.QArith Require Import Qcanon.
From Fairness Require Import view gmap frac dfrac cmra.
From Fairness Require Import updates local_updates proofmode_classes big_op.
From iris.prelude Require Import prelude options.

Local Open Scope iris_algebra_scope.

(** * CMRA for a "view of a gmap".

The authoritative element [gmap_view_auth] is any [gmap K V].  The fragments
[gmap_view_frag] represent ownership of a single key in that map.  Ownership is
governed by a discardable fraction, which provides the possibiltiy to obtain
persistent read-only ownership of a key.

The key frame-preserving updates are [gmap_view_alrloc] to allocate a new key,
[gmap_view_update] to update a key given full ownership of the corresponding
fragment, and [gmap_view_persist] to make a key read-only by discarding any
fraction of the corresponding fragment. Crucially, the latter does not require
owning the authoritative element.

NOTE: The API surface for [gmap_view] is experimental and subject to change.  We
plan to add notations for authoritative elements and fragments, and hope to
support arbitrary maps as fragments. *)

Local Definition gmap_view_fragUR (K : Type) `{Countable K} (V : cmra) : ucmra :=
  gmapUR K (prodR dfracR V).

(** View relation. *)
Section rel.
  Context (K : Type) `{Countable K} (V : cmra).
  Implicit Types (m : gmap K V) (k : K) (v : V).
  Implicit Types (f : gmap K (dfrac * V)).

  (* If we exactly followed [auth], we'd write something like [f ≼ m ∧ ✓ m],
  which is equivalent to:
  [map_Forall (λ k fv, ∃ v, m !! k = Some v ∧ Some fv ≼ Some v ∧ ✓ v) f].
  (Note the use of [Some] in the inclusion; the elementwise RA might not have a
  unit and we want a reflexive relation!) However, [f] and [m] do not have the
  same type, so this definition does not type-check: the fractions have been
  erased from the authoritative [m]. So we additionally quantify over the erased
  fraction [dq] and [(dq, v)] becomes the authoritative value.

  An alternative definition one might consider is to replace the erased fraction
  by a hard-coded [DfracOwn 1], the biggest possible fraction. That would not
  work: we would end up with [Some dv ≼ Some (DfracOwn 1, v)] but that cannot
  be satisfied if [dv.1 = DfracDiscarded], a case that we definitely want to
  allow!

  It is possible that [∀ k, ∃ dq, let auth := (pair dq) <$> m !! k in ✓ auth
  ∧ f !! k ≼ auth] would also work, but now the proofs are all done already.  ;)
  The two are probably equivalent, with a proof similar to [lookup_includedN]? *)
  Local Definition gmap_view_rel_raw m f :=
    map_Forall (λ k fv,
      ∃ v dq, m !! k = Some v ∧ ✓ (dq, v) ∧ (Some fv ≼ Some (dq, v))) f.

  Local Lemma gmap_view_rel_raw_mono m1 m2 f1 f2 :
    gmap_view_rel_raw m1 f1 →
    m1 = m2 →
    f2 ≼ f1 →
    gmap_view_rel_raw m2 f2.
  Proof.
    intros Hrel Hm Hf k [dqa va] Hk.
    (* For some reason applying the lemma in [Hf] does not work... *)
    destruct (lookup_included f2 f1) as [Hf' _].
    specialize (Hf' Hf k). clear Hf. rewrite Hk in Hf'.
    destruct (Some_included_is_Some _ _ Hf') as [[q' va'] Heq]. rewrite Heq in Hf'.
    specialize (Hrel _ _ Heq) as (v & dq & Hm1 & [Hvval Hdqval] & Hvincl). simpl in *.
    apply (f_equal (fun m => m !! k)) in Hm.
    rewrite Hm in Hm1.
    eexists. exists dq. split; first done. split.
    { split; first done. simpl. done. }
    etrans; first exact Hf'. done.
  Qed.

  Local Lemma gmap_view_rel_raw_valid m f :
    gmap_view_rel_raw m f → ✓ f.
  Proof.
    intros Hrel k. destruct (f !! k) as [[dqa va]|] eqn:Hf; rewrite Hf; last done.
    specialize (Hrel _ _ Hf) as (v & dq & Hmval & Hvval & Hvincl). simpl in *.
    eapply cmra_valid_included. 2:done. done.
  Qed.

  Local Lemma gmap_view_rel_raw_unit :
    ∃ m, gmap_view_rel_raw m ε.
  Proof. exists ∅. apply: map_Forall_empty. Qed.

  Local Canonical Structure gmap_view_rel : view_rel (gmap K V) (gmap_view_fragUR K V) :=
    ViewRel gmap_view_rel_raw gmap_view_rel_raw_mono
            gmap_view_rel_raw_valid gmap_view_rel_raw_unit.

  Local Lemma gmap_view_rel_exists f :
    (∃ m, gmap_view_rel m f) ↔ ✓ f.
  Proof.
    split.
    { intros [m Hrel]. eapply gmap_view_rel_raw_valid, Hrel. }
    intros Hf.
    cut (∃ m, gmap_view_rel m f ∧ ∀ k, f !! k = None → m !! k = None).
    { naive_solver. }
    induction f as [|k [dq v] f Hk' IH] using map_ind.
    { exists ∅. split; [|done]. apply: map_Forall_empty. }
    move: (Hf k). rewrite lookup_insert=> -[/= ??].
    destruct IH as (m & Hm & Hdom).
    { intros k'. destruct (decide (k = k')) as [->|?]; [by rewrite Hk'|].
      move: (Hf k'). by rewrite lookup_insert_ne. }
    exists (<[k:=v]> m).
    rewrite /gmap_view_rel /= /gmap_view_rel_raw map_Forall_insert //=. split_and!.
    - exists v, dq. split; first by rewrite lookup_insert.
      split; first by split. done.
    - eapply map_Forall_impl; [apply Hm|]; simpl.
      intros k' [dq' ag'] (v'&?&?&?). exists v'.
      rewrite lookup_insert_ne; naive_solver.
    - intros k'. rewrite !lookup_insert_None. naive_solver.
  Qed.

  Local Lemma gmap_view_rel_unit m : gmap_view_rel m ε.
  Proof. apply: map_Forall_empty. Qed.

  (* Local Lemma gmap_view_rel_discrete :
    CmraDiscrete V → ViewRelDiscrete gmap_view_rel.
  Proof.
    intros ? m f Hrel k [df va] Hk.
    destruct (Hrel _ _ Hk) as (v & dq & Hm & Hvval & Hvincl).
    exists v, dq. split; first done.
    split; first by apply cmra_discrete_valid_iff_0.
    rewrite -cmra_discrete_included_iff_0. done.
  Qed. *)
End rel.

(* Local Existing Instance gmap_view_rel_discrete. *)

(** [gmap_view] is a notation to give canonical structure search the chance
to infer the right instances (see [auth]). *)
Notation gmap_view K V := (view (@gmap_view_rel_raw K _ _ V)).
(* Definition gmap_viewO (K : Type) `{Countable K} (V : cmra) : Type :=
  viewO (gmap_view_rel K V). *)
Definition gmap_viewR (K : Type) `{Countable K} (V : cmra) : cmra :=
  viewR (gmap_view_rel K V).
Definition gmap_viewUR (K : Type) `{Countable K} (V : cmra) : ucmra :=
  viewUR (gmap_view_rel K V).

Section definitions.
  Context {K : Type} `{Countable K} {V : cmra}.

  Definition gmap_view_auth (dq : dfrac) (m : gmap K V) : gmap_viewR K V :=
    ●V{dq} m.
  Definition gmap_view_frag (k : K) (dq : dfrac) (v : V) : gmap_viewR K V :=
    ◯V {[k := (dq, v)]}.
End definitions.

Section lemmas.
  Context {K : Type} `{Countable K} {V : cmra}.
  Implicit Types (m : gmap K V) (k : K) (q : Qp) (dq : dfrac) (v : V).

  Global Instance : Params (@gmap_view_auth) 5 := {}.
  (* Global Instance gmap_view_auth_ne dq : NonExpansive (gmap_view_auth (K:=K) (V:=V) dq).
  Proof. solve_proper. Qed. *)
  Global Instance gmap_view_auth_proper dq : Proper ((=) ==> (=)) (gmap_view_auth (K:=K) (V:=V) dq).
  Proof. solve_proper. Qed.

  Global Instance : Params (@gmap_view_frag) 6 := {}.
  (* Global Instance gmap_view_frag_ne k oq : NonExpansive (gmap_view_frag (V:=V) k oq).
  Proof. solve_proper. Qed. *)
  Global Instance gmap_view_frag_proper k oq : Proper ((=) ==> (=)) (gmap_view_frag (V:=V) k oq).
  Proof. solve_proper. Qed.

  (* Helper lemmas *)
  Local Lemma gmap_view_rel_lookup m k dq v :
    gmap_view_rel K V m {[k := (dq, v)]} ↔
    ∃ v' dq', m !! k = Some v' ∧ ✓ (dq', v') ∧ Some (dq, v) ≼ Some (dq', v').
  Proof.
    split.
    - intros Hrel.
      edestruct (Hrel k) as (v' & dq' & Hlookup & Hval & Hinc).
      { rewrite lookup_singleton. done. }
      simpl in *. eexists _, _. split_and!; done.
    - intros (v' & dq' & Hlookup & Hval & ?) j [df va].
      destruct (decide (k = j)) as [<-|Hne]; last by rewrite lookup_singleton_ne.
      rewrite lookup_singleton. intros [= <- <-]. simpl.
      exists v', dq'. split_and!; by rewrite ?Hv'.
  Qed.

  (** Composition and validity *)
  Lemma gmap_view_auth_dfrac_op dp dq m :
    gmap_view_auth (dp ⋅ dq) m =
    gmap_view_auth dp m ⋅ gmap_view_auth dq m.
  Proof. by rewrite /gmap_view_auth view_auth_dfrac_op. Qed.
  Global Instance gmap_view_auth_dfrac_is_op dq dq1 dq2 m :
    IsOp dq dq1 dq2 → IsOp' (gmap_view_auth dq m) (gmap_view_auth dq1 m) (gmap_view_auth dq2 m).
  Proof. rewrite /gmap_view_auth. apply _. Qed.

  Lemma gmap_view_auth_dfrac_op_inv dp m1 dq m2 :
    ✓ (gmap_view_auth dp m1 ⋅ gmap_view_auth dq m2) → m1 = m2.
  Proof. apply view_auth_dfrac_op_inv. Qed.

  Lemma gmap_view_auth_dfrac_valid m dq : ✓ gmap_view_auth dq m ↔ ✓ dq.
  Proof.
    rewrite view_auth_dfrac_valid. intuition eauto using gmap_view_rel_unit.
  Qed.
  Lemma gmap_view_auth_valid m : ✓ gmap_view_auth (DfracOwn 1) m.
  Proof. rewrite gmap_view_auth_dfrac_valid. done. Qed.

  Lemma gmap_view_auth_dfrac_op_valid dq1 dq2 m1 m2 :
    ✓ (gmap_view_auth dq1 m1 ⋅ gmap_view_auth dq2 m2) ↔ ✓ (dq1 ⋅ dq2) ∧ m1 = m2.
  Proof.
    rewrite view_auth_dfrac_op_valid. intuition eauto using gmap_view_rel_unit.
  Qed.

  Lemma gmap_view_auth_op_valid m1 m2 :
    ✓ (gmap_view_auth (DfracOwn 1) m1 ⋅ gmap_view_auth (DfracOwn 1) m2) ↔ False.
  Proof. apply view_auth_op_valid. Qed.

  Lemma gmap_view_frag_valid k dq v : ✓ gmap_view_frag k dq v ↔ ✓ dq ∧ ✓ v.
  Proof.
    rewrite view_frag_valid gmap_view_rel_exists singleton_valid pair_valid.
    naive_solver.
  Qed.

  Lemma gmap_view_frag_op k dq1 dq2 v1 v2 :
    gmap_view_frag k (dq1 ⋅ dq2) (v1 ⋅ v2) =
      gmap_view_frag k dq1 v1 ⋅ gmap_view_frag k dq2 v2.
  Proof. rewrite -view_frag_op singleton_op -pair_op //. Qed.
  Lemma gmap_view_frag_add k q1 q2 v1 v2 :
    gmap_view_frag k (DfracOwn (q1 + q2)) (v1 ⋅ v2) =
      gmap_view_frag k (DfracOwn q1) v1 ⋅ gmap_view_frag k (DfracOwn q2) v2.
  Proof. rewrite -gmap_view_frag_op. done. Qed.

  Lemma gmap_view_frag_op_valid k dq1 dq2 v1 v2 :
    ✓ (gmap_view_frag k dq1 v1 ⋅ gmap_view_frag k dq2 v2) ↔
      ✓ (dq1 ⋅ dq2) ∧ ✓ (v1 ⋅ v2).
  Proof.
    rewrite view_frag_valid gmap_view_rel_exists singleton_op singleton_valid.
    by rewrite -pair_op pair_valid.
  Qed.

  Lemma gmap_view_both_dfrac_valid dp m k dq v :
    ✓ (gmap_view_auth dp m ⋅ gmap_view_frag k dq v) ↔
      ∃ v' dq', ✓ dp ∧ m !! k = Some v' ∧ ✓ (dq', v') ∧
                Some (dq, v) ≼ Some (dq', v').
  Proof.
    rewrite /gmap_view_auth /gmap_view_frag.
    rewrite view_both_dfrac_valid gmap_view_rel_lookup. naive_solver.
  Qed.
  Lemma gmap_view_both_valid dp m k v :
    ✓ (gmap_view_auth dp m ⋅ gmap_view_frag k (DfracOwn 1) v) ↔
      ✓ dp ∧ ✓ v ∧ m !! k = Some v.
  Proof.
    rewrite gmap_view_both_dfrac_valid. split.
    - intros [Hdp (v' & dq' & Hlookup & Hvalid & Hincl)].
      split; first done. rewrite Hlookup.
      assert ((DfracOwn 1,v) = (v', Hdp)) as Heq by apply (Some_included_exclusive _ _ Hincl Hvalid).
      injection Heq as <- <-.
      rewrite pair_valid in Hvalid. naive_solver.
    - intros (Hdp & Hval & Hlookup).
      exists v, (DfracOwn 1). do 2 (split; [done|]). split.
      + rewrite pair_valid. done.
      + by apply: Some_included_refl.
  Qed.
  (** The backwards direction here does not hold: if [dq = DfracOwn 1] but
  [v ≠ v'], we have to find a suitable erased fraction [dq'] to satisfy the view
  relation, but there is no way to satisfy [Some (DfracOwn 1, v) ≼ Some (dq', v')]
  for any [dq']. The "if and only if" version of this lemma would have to
  involve some extra condition like [dq = DfracOwn 1 → v = v'], or phrased
  more like the view relation itself: [∃ dq', ✓ dq' ∧ Some (v, dq) ≼ Some (v', dq')]. *)
  Lemma gmap_view_both_dfrac_valid_total `{!CmraTotal V} dp m k dq v :
    ✓ (gmap_view_auth dp m ⋅ gmap_view_frag k dq v) →
    ∃ v', ✓ dp ∧ ✓ dq ∧ m !! k = Some v' ∧ ✓ v' ∧ v ≼ v'.
  Proof.
    rewrite gmap_view_both_dfrac_valid.
    intros (v' & dq' & Hdp & Hlookup & Hvalid & Hincl).
    exists v'. split; first done. split.
    - eapply (cmra_valid_Some_included dq'); first by apply Hvalid.
      eapply Some_pair_included_l. done.
    - split; first done. split; first apply Hvalid.
      move:Hincl=> /Some_pair_included_r /Some_included_total. done.
  Qed.

  (** Without [CmraDiscrete], we cannot do much better than [∀, <same as above>].
  This is because both the [dq'] and the witness for the [≼] can be different for
  each step-index. It is totally possible that at low step-indices, [v] has a frame
  (and [dq' > dq]) while at higher step-indices, [v] has no frame (and [dq' = dq]). *)
  Lemma gmap_view_both_dfrac_valid_discrete dp m k dq v :
    ✓ (gmap_view_auth dp m ⋅ gmap_view_frag k dq v) ↔
      ∃ v' dq', ✓ dp ∧ m !! k = Some v' ∧
                ✓ (dq', v') ∧
                Some (dq, v) ≼ Some (dq', v').
  Proof.
    setoid_rewrite gmap_view_both_dfrac_valid. split.
    - intros Hvalid.
      destruct Hvalid as (v' & dq' & Hdp & Hlookup & Hvalid & Hincl).
      exists v', dq'. do 2 (split; first done). done.
    - intros (v' & dq' & Hdp & Hlookup & Hvalid & Hincl).
      exists v', dq'. do 2 (split; first done).
      done.
  Qed.
  (** The backwards direction here does not hold: if [dq = DfracOwn 1] but
  [v ≠ v'], we have to find a suitable erased fraction [dq'] to satisfy the view
  relation, but there is no way to satisfy [Some (DfracOwn 1, v) ≼ Some (dq', v')]
  for any [dq']. The "if and only if" version of this lemma would have to
  involve some extra condition like [dq = DfracOwn 1 → v = v'], or phrased
  more like the view relation itself: [∃ dq', ✓ dq' ∧ Some (v, dq) ≼ Some (v', dq')]. *)
  Lemma gmap_view_both_dfrac_valid_discrete_total
      `{!CmraTotal V} dp m k dq v :
    ✓ (gmap_view_auth dp m ⋅ gmap_view_frag k dq v) →
    ∃ v', ✓ dp ∧ ✓ dq ∧ m !! k = Some v' ∧ ✓ v' ∧ v ≼ v'.
  Proof.
    rewrite gmap_view_both_dfrac_valid_discrete.
    intros (v' & dq' & Hdp & Hlookup & Hvalid & Hincl).
    exists v'. split; first done. split.
    - eapply (cmra_valid_Some_included dq'); first by apply Hvalid.
      eapply Some_pair_included_l. done.
    - split; first done. split; first apply Hvalid.
      move:Hincl=> /Some_pair_included_r /Some_included_total. done.
  Qed.

  (** Frame-preserving updates *)
  Lemma gmap_view_alloc m k dq v :
    m !! k = None →
    ✓ dq →
    ✓ v →
    gmap_view_auth (DfracOwn 1) m ~~>
      gmap_view_auth (DfracOwn 1) (<[k := v]> m) ⋅ gmap_view_frag k dq v.
  Proof.
    intros Hfresh Hdq Hval. apply view_update_alloc=> bf Hrel j [df va] /=.
    rewrite lookup_op. destruct (decide (j = k)) as [->|Hne].
    - assert (bf !! k = None) as Hbf.
      { destruct (bf !! k) as [[df' va']|] eqn:Hbf; last done.
        specialize (Hrel _ _ Hbf). destruct Hrel as (v' & dq' & Hm & _).
        exfalso. rewrite Hm in Hfresh. done. }
      rewrite lookup_singleton Hbf right_id.
      intros [= <- <-]. eexists _, _.
      rewrite lookup_insert. split; first done.
      split; last by apply: Some_included_refl.
      done.
    - rewrite lookup_singleton_ne; last done.
      rewrite left_id=>Hbf.
      specialize (Hrel _ _ Hbf). destruct Hrel as (v' & ? & Hm & ?).
      eexists _, _. split; last done.
      rewrite lookup_insert_ne //.
  Qed.

  Lemma gmap_view_alloc_big m m' dq :
    m' ##ₘ m →
    ✓ dq →
    map_Forall (λ k v, ✓ v) m' →
    gmap_view_auth (DfracOwn 1) m ~~>
      gmap_view_auth (DfracOwn 1) (m' ∪ m) ⋅
      ([^op map] k↦v ∈ m', gmap_view_frag k dq v).
  Proof.
    intros ?? Hm'.
    induction m' as [|k v m' ? IH] using map_ind; decompose_map_disjoint.
    { rewrite big_opM_empty left_id_L right_id. done. }
    rewrite IH //.
    2:{ by eapply map_Forall_insert_1_2. }
    rewrite big_opM_insert // assoc.
    apply cmra_update_op; last done.
    rewrite -insert_union_l. apply (gmap_view_alloc _ k dq); [|done|].
    - by apply lookup_union_None.
    - eapply Hm'. erewrite lookup_insert. done.
  Qed.

  Lemma gmap_view_delete m k v :
    gmap_view_auth (DfracOwn 1) m ⋅ gmap_view_frag k (DfracOwn 1) v ~~>
    gmap_view_auth (DfracOwn 1) (delete k m).
  Proof.
    apply view_update_dealloc=> bf Hrel j [df va] Hbf /=.
    destruct (decide (j = k)) as [->|Hne].
    - edestruct (Hrel k) as (v' & dq' & ? & Hval & Hincl).
      { rewrite lookup_op Hbf lookup_singleton -Some_op. done. }
      eapply (cmra_valid_Some_included _ _ Hval) in Hincl as Hval'.
      exfalso. clear Hval Hincl.
      rewrite pair_valid /= in Hval'.
      apply: dfrac_full_exclusive. apply Hval'.
    - edestruct (Hrel j) as (v' & ? & ? & ?).
      { rewrite lookup_op lookup_singleton_ne // Hbf. done. }
      eexists v', _. split; last done.
      rewrite lookup_delete_ne //.
  Qed.

  Lemma gmap_view_delete_big m m' :
    gmap_view_auth (DfracOwn 1) m ⋅
    ([^op map] k↦v ∈ m', gmap_view_frag k (DfracOwn 1) v) ~~>
      gmap_view_auth (DfracOwn 1) (m ∖ m').
  Proof.
    induction m' as [|k v m' ? IH] using map_ind.
    { rewrite right_id_L big_opM_empty right_id //. }
    rewrite big_opM_insert //.
    rewrite [gmap_view_frag _ _ _ ⋅ _]comm assoc IH gmap_view_delete.
    rewrite -delete_difference. done.
  Qed.

  (** We do not use [local_update] ([~l~>]) in the premise because we also want
  to expose the role of the fractions. *)
  Lemma gmap_view_update m k dq v mv' v' dq' :
    (∀ mv f,
      m !! k = Some mv →
      ✓ ((dq, v) ⋅? f) →
      mv = v ⋅? (snd <$> f) →
      ✓ ((dq', v') ⋅? f) ∧ mv' = v' ⋅? (snd <$> f)) →
    gmap_view_auth (DfracOwn 1) m ⋅ gmap_view_frag k dq v ~~>
      gmap_view_auth (DfracOwn 1) (<[k := mv']> m) ⋅ gmap_view_frag k dq' v'.
  Proof.
    intros Hup. apply view_update=> bf Hrel j [df va].
    rewrite lookup_op.
    destruct (decide (j = k)) as [->|Hne]; last first.
    { (* prove that other keys are unaffected *)
      simplify_map_eq. rewrite lookup_singleton_ne //.
      (* FIXME simplify_map_eq should have done this *)
      rewrite left_id. intros Hbf.
      edestruct (Hrel j) as (mva & mdf & Hlookup & Hval & Hincl).
      { rewrite lookup_op lookup_singleton_ne // left_id //. }
      naive_solver. }
    simplify_map_eq. rewrite lookup_singleton.
    (* FIXME simplify_map_eq should have done this *)
    intros Hbf.
    edestruct (Hrel k) as (mv & mdf & Hlookup & Hval & Hincl).
    { rewrite lookup_op lookup_singleton // Some_op_opM //. }
    rewrite Some_included_opM in Hincl.
    destruct Hincl as [f' Hincl]. rewrite cmra_opM_opM_assoc in Hincl.
    set f := bf !! k ⋅ f'. (* the complete frame *)
    change (bf !! k ⋅ f') with f in Hincl.
    specialize (Hup mv f). destruct Hup as (Hval' & Hincl').
    { done. }
    { rewrite -Hincl. done. }
    { destruct f as [c|]; simpl in *.
      - destruct c. rewrite -pair_op in Hincl. injection Hincl as ? ->. done.
      - injection Hincl as ? ->. done.
    }
    eexists mv', (dq' ⋅? (fst <$> f)). split; first done.
    rewrite -Hbf. clear Hbf. split.
    - rewrite Hincl'. destruct Hval'. by destruct f.
    - rewrite Some_op_opM. rewrite Some_included_opM.
      exists f'. rewrite Hincl'.
      rewrite cmra_opM_opM_assoc. change (bf !! k ⋅ f') with f.
      by destruct f.
  Qed.

  (** This derived version cannot exploit [dq = DfracOwn 1]. *)
  Lemma gmap_view_update_local m k dq mv v mv' v' :
    m !! k = Some mv →
    (mv, v) ~l~> (mv', v') →
    gmap_view_auth (DfracOwn 1) m ⋅ gmap_view_frag k dq v ~~>
    gmap_view_auth (DfracOwn 1) (<[k := mv']> m) ⋅ gmap_view_frag k dq v'.
  Proof.
    intros Hlookup Hup. apply gmap_view_update.
    intros mv0 f Hmv0 Hval Hincl.
    rewrite Hlookup in Hmv0. injection Hmv0 as [= <-].
    specialize (Hup (snd <$> f)). destruct Hup as (Hval' & Hincl').
    { rewrite Hincl. destruct Hval. by destruct f. }
    { simpl. done. }
    split; last done. split.
    - destruct Hval. by destruct f.
    - simpl in *. replace (((dq, v') ⋅? f).2) with (v' ⋅? (snd <$> f)).
      2:{ by destruct f. }
      rewrite -Hincl'. done.
  Qed.

  Lemma gmap_view_replace m k v v' :
    ✓ v' →
    gmap_view_auth (DfracOwn 1) m ⋅ gmap_view_frag k (DfracOwn 1) v ~~>
      gmap_view_auth (DfracOwn 1) (<[k := v']> m) ⋅ gmap_view_frag k (DfracOwn 1) v'.
  Proof.
    (* There would be a simple proof via delete-then-insert... but we use this as a
       sanity check to make sure the update lemma is strong enough. *)
    intros Hval'. apply gmap_view_update.
    intros mv f Hlookup Hval Hincl.
    destruct f; simpl.
    { apply exclusive_l in Hval; first done. apply _. }
    split; last done.
    split; first done. simpl. done.
  Qed.

  Lemma gmap_view_replace_big m m0 m1 :
    dom m0 = dom m1 →
    map_Forall (λ k v, ✓ v) m1 →
    gmap_view_auth (DfracOwn 1) m ⋅
    ([^op map] k↦v ∈ m0, gmap_view_frag k (DfracOwn 1) v) ~~>
      gmap_view_auth (DfracOwn 1) (m1 ∪ m) ⋅
      ([^op map] k↦v ∈ m1, gmap_view_frag k (DfracOwn 1) v).
  Proof.
    intros Hdom%eq_sym. revert m1 Hdom.
    induction m0 as [|k v m0 Hnotdom IH] using map_ind; intros m1 Hdom Hval.
    { rewrite dom_empty_L in Hdom.
      apply dom_empty_iff_L in Hdom as ->.
      rewrite left_id_L big_opM_empty. done. }
    rewrite dom_insert_L in Hdom.
    assert (k ∈ dom m1) as Hindom by set_solver.
    apply elem_of_dom in Hindom as [v' Hlookup].
    rewrite big_opM_insert //.
    rewrite [gmap_view_frag _ _ _ ⋅ _]comm assoc.
    rewrite (IH (delete k m1)); last first.
    { by apply map_Forall_delete. }
    { rewrite dom_delete_L Hdom.
      apply not_elem_of_dom in Hnotdom. set_solver -Hdom. }
    rewrite -assoc [_ ⋅ gmap_view_frag _ _ _]comm assoc.
    rewrite (gmap_view_replace _ _ _ v').
    2:{ eapply Hval. done. }
    rewrite (big_opM_delete _ m1 k v') // -assoc.
    rewrite insert_union_r; last by rewrite lookup_delete.
    rewrite union_delete_insert //.
  Qed.

  Lemma gmap_view_auth_persist dq m :
    gmap_view_auth dq m ~~> gmap_view_auth DfracDiscarded m.
  Proof. apply view_update_auth_persist. Qed.

  Lemma gmap_view_auth_unpersist m :
    gmap_view_auth DfracDiscarded m ~~>: λ a, ∃ q, a = gmap_view_auth (DfracOwn q) m.
  Proof. apply view_updateP_auth_unpersist. Qed.

  Local Lemma gmap_view_frag_dfrac k dq P v :
    dq ~~>: P →
    gmap_view_frag k dq v ~~>: λ a, ∃ dq', a = gmap_view_frag k dq' v ∧ P dq'.
  Proof.
    intros Hdq.
    eapply cmra_updateP_weaken;
      [apply view_updateP_frag
         with (P := λ b', ∃ dq', ◯V b' = gmap_view_frag k dq' v ∧ P dq')
      |naive_solver].
    intros m bf Hrel.
    destruct (Hrel k ((dq, v) ⋅? bf !! k)) as (v' & dq' & Hlookup & Hval & Hincl).
    { by rewrite lookup_op lookup_singleton Some_op_opM. }
    rewrite Some_included_opM in Hincl.
    destruct Hincl as [f' Hincl]. rewrite cmra_opM_opM_assoc in Hincl.
    set f := bf !! k ⋅ f'. (* the complete frame *)
    change (bf !! k ⋅ f') with f in Hincl.
    destruct (Hdq (option_map fst f)) as (dq'' & HPdq'' & Hvdq'').
    { destruct f as [[c1 c2]|]; simpl in *; [rewrite -pair_op in Hincl|].
      all: injection Hincl as -> ->; rewrite pair_valid in Hval; naive_solver.
    }
    eexists. split; first by exists dq''.
    intros j [df va] Heq.
    destruct (decide (k = j)) as [->|Hne].
    - rewrite lookup_op lookup_singleton in Heq.
      eexists v', (dq'' ⋅? (fst <$> f)).
      split; first done. split.
      + split; last by apply Hval. simpl. done.
      + rewrite -Heq. exists f'.
        rewrite -assoc. change (bf !! j ⋅ f') with f.
        destruct f as [[c1 c2]|]; simpl in *; [rewrite -pair_op in Hincl|].
        all: injection Hincl as -> ->; rewrite pair_valid in Hval; naive_solver.
    - rewrite lookup_op lookup_singleton_ne // left_id in Heq.
      eapply Hrel. rewrite lookup_op lookup_singleton_ne // left_id Heq //.
  Qed.

  Lemma gmap_view_frag_persist k dq v :
    gmap_view_frag k dq v ~~> gmap_view_frag k DfracDiscarded v.
  Proof.
    eapply (cmra_update_lift_updateP (λ dq, gmap_view_frag k dq v)).
    - intros. by apply gmap_view_frag_dfrac.
    - apply dfrac_discard_update.
  Qed.

  Lemma gmap_view_frag_unpersist k v :
    gmap_view_frag k DfracDiscarded v ~~>:
      λ a, ∃ q, a = gmap_view_frag k (DfracOwn q) v.
  Proof.
    eapply cmra_updateP_weaken.
    { apply gmap_view_frag_dfrac, dfrac_undiscard_update. }
    naive_solver.
  Qed.

  (** Typeclass instances *)
  Global Instance gmap_view_frag_core_id k dq v :
    CoreId dq → CoreId v → CoreId (gmap_view_frag k dq v).
  Proof. apply _. Qed.

  (* Global Instance gmap_view_cmra_discrete :
    CmraDiscrete V → CmraDiscrete (gmap_viewR K V).
  Proof. apply _. Qed. *)

  Global Instance gmap_view_frag_mut_is_op dq dq1 dq2 k v v1 v2 :
    IsOp dq dq1 dq2 →
    IsOp v v1 v2 →
    IsOp' (gmap_view_frag k dq v) (gmap_view_frag k dq1 v1) (gmap_view_frag k dq2 v2).
  Proof. rewrite /IsOp' /IsOp => -> ->. apply gmap_view_frag_op. Qed.
End lemmas.

(** Functor *)
(* Program Definition gmap_viewURF (K : Type) `{Countable K} (F : rFunctor) : urFunctor := {|
  urFunctor_car A _ B _ := gmap_viewUR K (rFunctor_car F A B);
  urFunctor_map A1 _ A2 _ B1 _ B2 _ fg :=
    viewO_map (rel:=gmap_view_rel K (rFunctor_car F A1 B1))
              (rel':=gmap_view_rel K (rFunctor_car F A2 B2))
              (gmapO_map (K:=K) (rFunctor_map F fg))
              (gmapO_map (K:=K) (prodO_map cid (rFunctor_map F fg)))
|}.
Next Obligation.
  intros K ?? F A1 ? A2 ? B1 ? B2 ? f g Hfg.
  apply viewO_map_ne.
  - apply gmapO_map_ne, rFunctor_map_ne. done.
  - apply gmapO_map_ne. apply prodO_map_ne; first done.
    apply rFunctor_map_ne. done.
Qed.
Next Obligation.
  intros K ?? F A ? B ? x; simpl in *. rewrite -{2}(view_map_id x).
  apply (view_map_ext _ _ _ _)=> y.
  - rewrite /= -{2}(map_fmap_id y).
    apply map_fmap_equiv_ext=>k ??.
    apply rFunctor_map_id.
  - rewrite /= -{2}(map_fmap_id y).
    apply map_fmap_equiv_ext=>k [df va] ?.
    split; first done. simpl.
    apply rFunctor_map_id.
Qed.
Next Obligation.
  intros K ?? F A1 ? A2 ? A3 ? B1 ? B2 ? B3 ? f g f' g' x; simpl in *.
  rewrite -view_map_compose.
  apply (view_map_ext _ _ _ _)=> y.
  - rewrite /= -map_fmap_compose.
    apply map_fmap_equiv_ext=>k ??.
    apply rFunctor_map_compose.
  - rewrite /= -map_fmap_compose.
    apply map_fmap_equiv_ext=>k [df va] ?.
    split; first done. simpl.
    apply rFunctor_map_compose.
Qed.
Next Obligation.
  intros K ?? F A1 ? A2 ? B1 ? B2 ? fg; simpl.
  (* [apply] does not work, probably the usual unification probem (Coq #6294) *)
  apply: view_map_cmra_morphism; [apply _..|]=> m f.
  intros Hrel k [df va] Hf. move: Hf.
  rewrite !lookup_fmap.
  destruct (f !! k) as [[df' va']|] eqn:Hfk; rewrite Hfk; last done.
  simpl=>[= <- <-].
  specialize (Hrel _ _ Hfk). simpl in Hrel.
  destruct Hrel as (v & dq & Hlookup & Hval & Hincl).
  eexists (rFunctor_map F fg v), dq.
  rewrite Hlookup. split; first done. split.
  - split; first by apply Hval. simpl. apply: cmra_morphism_valid. apply Hval.
  - destruct Hincl as [[[fdq fv]|] Hincl].
    + apply: Some_includedN_mono. rewrite -Some_op in Hincl.
      apply (inj _) in Hincl. rewrite -pair_op in Hincl.
      exists (fdq, rFunctor_map F fg fv). rewrite -pair_op.
      split; first apply Hincl. rewrite -cmra_morphism_op.
      simpl. f_equiv. apply Hincl.
    + exists None. rewrite right_id in Hincl. apply (inj _) in Hincl.
      rewrite right_id. f_equiv. split; first apply Hincl.
      simpl. f_equiv. apply Hincl.
Qed.

Global Instance gmap_viewURF_contractive (K : Type) `{Countable K} F :
  rFunctorContractive F → urFunctorContractive (gmap_viewURF K F).
Proof.
  intros ? A1 ? A2 ? B1 ? B2 ? f g Hfg.
  apply viewO_map_ne.
  - apply gmapO_map_ne. apply rFunctor_map_contractive. done.
  - apply gmapO_map_ne. apply prodO_map_ne; first done.
    apply rFunctor_map_contractive. done.
Qed.

Program Definition gmap_viewRF (K : Type) `{Countable K} (F : rFunctor) : rFunctor := {|
  rFunctor_car A _ B _ := gmap_viewR K (rFunctor_car F A B);
  rFunctor_map A1 _ A2 _ B1 _ B2 _ fg :=
    viewO_map (rel:=gmap_view_rel K (rFunctor_car F A1 B1))
              (rel':=gmap_view_rel K (rFunctor_car F A2 B2))
              (gmapO_map (K:=K) (rFunctor_map F fg))
              (gmapO_map (K:=K) (prodO_map cid (rFunctor_map F fg)))
|}.
Solve Obligations with apply gmap_viewURF.

Global Instance gmap_viewRF_contractive (K : Type) `{Countable K} F :
  rFunctorContractive F → rFunctorContractive (gmap_viewRF K F).
Proof. apply gmap_viewURF_contractive. Qed. *)

Global Typeclasses Opaque gmap_view_auth gmap_view_frag.
