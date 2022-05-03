From sflib Require Import sflib.
From ITree Require Export ITree.
From Paco Require Import paco.

Export ITreeNotations.

Require Import Coq.Classes.RelationClasses.
Require Import Program.

From Fairness Require Import ITreeLib.
From Fairness Require Import FairBeh.

Set Implicit Arguments.

Section SIM.

  Context {Ident: ID}.

  Definition stuck_idx (m: imap) (j: id) := le (m j) 0.

  Inductive _sim
            (sim: forall R0 R1 (RR: R0 -> R1 -> Prop),
                bool -> imap -> bool  -> imap -> (@state _ R0) -> (@state _ R1) -> Prop)
            {R0 R1} (RR: R0 -> R1 -> Prop) (p_src: bool) (m_src: imap) (p_tgt: bool) (m_tgt: imap) :
    (@state _ R0) -> (@state _ R1) -> Prop :=
  | sim_ret
      r_src r_tgt
      (SIM: RR r_src r_tgt)
    :
    _sim sim RR p_src m_src p_tgt m_tgt (Ret r_src) (Ret r_tgt)
  | sim_obs
      m_src0 m_tgt0 ktr_src0 ktr_tgt0 fn args
      (SIM: forall r_src r_tgt (EQ: r_src = r_tgt),
          sim _ _ RR true m_src0 true m_tgt0 (ktr_src0 r_src) (ktr_tgt0 r_tgt))
      (ISRC: soft_update m_src m_src0)
      (ITGT: soft_update m_tgt m_tgt0)
    :
    _sim sim RR p_src m_src p_tgt m_tgt (Vis (Observe fn args) ktr_src0) (Vis (Observe fn args) ktr_tgt0)

  | sim_tauL
      m_src0 itr_src0 itr_tgt0
      (SIM: @_sim sim _ _ RR true m_src0 p_tgt m_tgt itr_src0 itr_tgt0)
      (ISRC: soft_update m_src m_src0)
    :
    _sim sim RR p_src m_src p_tgt m_tgt (Tau itr_src0) itr_tgt0
  | sim_tauR
      m_tgt0 itr_src0 itr_tgt0
      (SIM: @_sim sim _ _ RR p_src m_src true m_tgt0 itr_src0 itr_tgt0)
      (ITGT: soft_update m_tgt m_tgt0)
    :
    _sim sim RR p_src m_src p_tgt m_tgt itr_src0 (Tau itr_tgt0)
  | sim_chooseL
      m_src0 X ktr_src0 itr_tgt0
      (SIM: exists x, _sim sim RR true m_src0 p_tgt m_tgt (ktr_src0 x) itr_tgt0)
      (ISRC: soft_update m_src m_src0)
    :
    _sim sim RR p_src m_src p_tgt m_tgt (trigger (Choose X) >>= ktr_src0) itr_tgt0
  | sim_chooseR
      m_tgt0 X itr_src0 ktr_tgt0
      (SIM: forall x, _sim sim RR p_src m_src true m_tgt0 itr_src0 (ktr_tgt0 x))
      (ITGT: soft_update m_tgt m_tgt0)
    :
    _sim sim RR p_src m_src p_tgt m_tgt itr_src0 (trigger (Choose X) >>= ktr_tgt0)

  | sim_fairL
      f_src ktr_src0 itr_tgt0
      (SIM: exists m_src0, (<<FAIR: fair_update m_src m_src0 f_src>>) /\
                        (<<SIM: _sim sim RR true m_src0 p_tgt m_tgt (ktr_src0 tt) itr_tgt0>>))
    :
    _sim sim RR p_src m_src p_tgt m_tgt (trigger (Fair f_src) >>= ktr_src0) itr_tgt0
  | sim_fairR
      f_tgt itr_src0 ktr_tgt0
      (SIM: forall m_tgt0 (FAIR: fair_update m_tgt m_tgt0 f_tgt),
          _sim sim RR p_src m_src true m_tgt0 itr_src0 (ktr_tgt0 tt))
    :
    _sim sim RR p_src m_src p_tgt m_tgt itr_src0 (trigger (Fair f_tgt) >>= ktr_tgt0)

  | sim_progress
      itr_src0 itr_tgt0 m_src0 m_tgt0
      (SIM: sim _ _ RR false m_src0 false m_tgt0 itr_src0 itr_tgt0)
      (PSRC: p_src = true)
      (PTGT: p_tgt = true)
      (IMAP: forall i, (<<SSRC: stuck_idx m_src i>>) -> (<<STGT: stuck_idx m_tgt i>>))
    :
    _sim sim RR p_src m_src p_tgt m_tgt itr_src0 itr_tgt0
  (* | sim_weak_progress *)
  (*     itr_src0 itr_tgt0 m_tgt0 idx *)
  (*     (SIM: sim _ _ RR p_src m_src false m_tgt0 itr_src0 itr_tgt0) *)
  (*     (* (SIM: forall m_tgt0 (FILL: forall j (NEQ: j <> idx), le (m_tgt0 j) (m_tgt j)), *) *)
  (*     (*     sim _ _ RR p_src m_src false m_tgt0 itr_src0 itr_tgt0) *) *)
  (*     (PTGT: p_tgt = true) *)
  (*     (ITGT: stuck_idx m_tgt idx) *)
  (*     (FILL: forall j (NEQ: j <> idx), le (m_tgt0 j) (m_tgt j)) *)
  (*   : *)
  (*   _sim sim RR p_src m_src p_tgt m_tgt itr_src0 itr_tgt0 *)
  .

  Lemma _sim_ind2 (r: forall R0 R1 (RR: R0 -> R1 -> Prop), bool -> imap  -> bool -> imap -> (@state _ R0) -> (@state _ R1) -> Prop)
        R0 R1 (RR: R0 -> R1 -> Prop)
        (P: bool -> imap  -> bool -> imap -> (@state _ R0) -> (@state _ R1) -> Prop)
        (RET: forall
            p_src m_src p_tgt m_tgt
            r_src r_tgt
            (SIM: RR r_src r_tgt),
            P p_src m_src p_tgt m_tgt (Ret r_src) (Ret r_tgt))
        (OBS: forall
            p_src m_src p_tgt m_tgt m_src0 m_tgt0 ktr_src0 ktr_tgt0
            fn args
            (SIM: forall r_src r_tgt (EQ: r_src = r_tgt), r _ _ RR true m_src0 true m_tgt0 (ktr_src0 r_src) (ktr_tgt0 r_tgt))
            (ISRC: soft_update m_src m_src0)
            (ITGT: soft_update m_tgt m_tgt0),
            P p_src m_src p_tgt m_tgt (Vis (Observe fn args) ktr_src0) (Vis (Observe fn args) ktr_tgt0))
        (TAUL: forall 
            p_src m_src p_tgt m_tgt m_src0 itr_src0 itr_tgt0
            (SIM: _sim r RR true m_src0 p_tgt m_tgt itr_src0 itr_tgt0)
            (IH: P true m_src0 p_tgt m_tgt itr_src0 itr_tgt0)
            (ISRC: soft_update m_src m_src0),
            P p_src m_src p_tgt m_tgt (Tau itr_src0) itr_tgt0)
        (TAUR: forall 
            p_src m_src p_tgt m_tgt m_tgt0 itr_src0 itr_tgt0
            (SIM: _sim r RR p_src m_src true m_tgt0 itr_src0 itr_tgt0)
            (IH: P p_src m_src true m_tgt0 itr_src0 itr_tgt0)
            (ITGT: soft_update m_tgt m_tgt0),
            P p_src m_src p_tgt m_tgt itr_src0 (Tau itr_tgt0))
        (CHOOSEL: forall
            p_src m_src p_tgt m_tgt m_src0 X ktr_src0 itr_tgt0
            (SIM: exists x,
                (<<SIM: _sim r RR true m_src0 p_tgt m_tgt (ktr_src0 x) itr_tgt0>>) /\
                  (<<IH: P true m_src0 p_tgt m_tgt (ktr_src0 x) itr_tgt0>>))
            (ISRC: soft_update m_src m_src0),
            P p_src m_src p_tgt m_tgt (ITree.bind (trigger (Choose X)) ktr_src0) itr_tgt0)
        (CHOOSER: forall
            p_src m_src p_tgt m_tgt m_tgt0 X itr_src0 ktr_tgt0
            (SIM: forall x,
                (<<SIM: _sim r RR p_src m_src true m_tgt0 itr_src0 (ktr_tgt0 x)>>) /\
                  (<<IH: P p_src m_src true m_tgt0 itr_src0 (ktr_tgt0 x)>>))
            (ITGT: soft_update m_tgt m_tgt0),
            P p_src m_src p_tgt m_tgt itr_src0 (ITree.bind (trigger (Choose X)) ktr_tgt0))
        (FAIRL: forall
            p_src m_src p_tgt m_tgt f_src ktr_src0 itr_tgt0
            (SIM: exists m_src0,
                (<<FAIR: fair_update m_src m_src0 f_src>>) /\
                  (<<SIM: _sim r RR true m_src0 p_tgt m_tgt (ktr_src0 tt) itr_tgt0>>) /\
                  (<<IH: P true m_src0 p_tgt m_tgt (ktr_src0 tt) itr_tgt0>>)),
            P p_src m_src p_tgt m_tgt (ITree.bind (trigger (Fair f_src)) ktr_src0) itr_tgt0)
        (FAIRR: forall
            p_src m_src p_tgt m_tgt f_tgt itr_src0 ktr_tgt0
            (SIM: forall m_tgt0 (FAIR: fair_update m_tgt m_tgt0 f_tgt),
                (<<SIM: _sim r RR p_src m_src true m_tgt0 itr_src0 (ktr_tgt0 tt)>>) /\
                  (<<IH: P p_src m_src true m_tgt0 itr_src0 (ktr_tgt0 tt)>>)),
            P p_src m_src p_tgt m_tgt itr_src0 (ITree.bind (trigger (Fair f_tgt)) ktr_tgt0))
        (PROGRESS: forall
            p_src m_src p_tgt m_tgt m_src0 m_tgt0 itr_src0 itr_tgt0
            (SIM: r _ _ RR false m_src0 false m_tgt0 itr_src0 itr_tgt0)
            (PSRC: p_src = true)
            (PTGT: p_tgt = true)
            (IMAP: forall i, (<<SSRC: stuck_idx m_src i>>) -> (<<STGT: stuck_idx m_tgt i>>)),
            P p_src m_src p_tgt m_tgt itr_src0 itr_tgt0)
        (* (WPROGRESS: forall *)
        (*     p_src m_src p_tgt m_tgt idx itr_src0 itr_tgt0 *)
        (*     (SIM: forall m_tgt0 (FILL: forall j (NEQ: j <> idx), le (m_tgt0 j) (m_tgt j)), *)
        (*         r _ _ RR p_src m_src false m_tgt0 itr_src0 itr_tgt0) *)
        (*     (PTGT: p_tgt = true) *)
        (*     (ITGT: stuck_idx m_tgt idx), *)
        (*     P p_src m_src p_tgt m_tgt itr_src0 itr_tgt0) *)
    :
    forall p_src m_src p_tgt m_tgt itr_src itr_tgt
      (SIM: _sim r RR p_src m_src p_tgt m_tgt itr_src itr_tgt),
      P p_src m_src p_tgt m_tgt itr_src itr_tgt.
  Proof.
    fix IH 7. i. inv SIM.
    { eapply RET; eauto. }
    { eapply OBS; eauto. }
    { eapply TAUL; eauto. }
    { eapply TAUR; eauto. }
    { eapply CHOOSEL; eauto. des. esplits; eauto. }
    { eapply CHOOSER; eauto. }
    { eapply FAIRL; eauto. des. esplits; eauto. }
    { eapply FAIRR; eauto. i. esplits; eauto. }
    { eapply PROGRESS; eauto. }
    (* { eapply WPROGRESS; eauto. } *)
  Qed.

  Definition sim: forall R0 R1 (RR: R0 -> R1 -> Prop), bool -> imap  -> bool -> imap -> (@state _ R0) -> (@state _ R1) -> Prop := paco9 _sim bot9.

  Lemma sim_mon: monotone9 _sim.
  Proof.
    ii. induction IN using _sim_ind2.
    { econs 1; eauto. }
    { econs 2; eauto. }
    { econs 3; eauto. }
    { econs 4; eauto. }
    { econs 5; eauto. des. esplits; eauto. }
    { econs 6; eauto. i. hexploit SIM. i; des. eauto. }
    { econs 7; eauto. des. esplits; eauto. }
    { econs 8; eauto. i. hexploit SIM. eauto. i; des. eauto. }
    { econs 9; eauto. }
    (* { econs 10; eauto. } *)
  Qed.

  Hint Resolve sim_mon: paco.
  Hint Resolve cpn9_wcompat: paco.

End SIM.



Section EX.

  Instance Ident : ID := mk nat.

  (* Definition uunit := prod unit unit. *)

  Definition while_itree (step: unit -> itree eventE (unit + unit)) : itree eventE unit :=
    ITree.iter step tt.

  Lemma unfold_iter_eq A E B
     : forall (f : A -> itree E (A + B)) (x : A),
       ITree.iter f x = lr <- f x;; match lr with
                                    | inl l => Tau (ITree.iter f l)
                                    | inr r0 => Ret r0
                                   end.
  Proof.
    i. eapply bisim_is_eq. eapply unfold_iter.
  Qed.

  Lemma unfold_while_itree
        itr
    :
    while_itree (fun u => ITree.bind itr (fun r => Ret (inl r))) =
      itr;; tau;; (while_itree (fun u => ITree.bind itr (fun r => Ret (inl r)))).
  Proof.
    unfold while_itree. rewrite unfold_iter_eq at 1. ired.
    f_equal. extensionality u. destruct u. ired. auto.
  Qed.
    (* unfold while_itree. eapply bisim_is_eq. revert1. ginit. gcofix CIH. i. *)
    (* rewrite unfold_iter_eq. ired. guclo eqit_clo_bind. econs. reflexivity. *)
    (* i; subst. ired. gstep. econs. gfinal. left. *)
    (* specialize (CIH itr). destruct u2. *)
    (* match goal with *)
    (* | _: r _ ?x |- r _ ?y => replace y with x *)
    (* end; eauto. *)
    (* rewrite unfold_iter_eq. ired. *)
    (* f_equal. extensionality a. destruct a. ired. f_equal. f_equal. *)
    (* rewrite unfold_iter_eq. ired. auto. *)

  Definition RR := @eq nat.
  Definition ndec := PeanoNat.Nat.eq_dec.

  Definition src1: @state _ nat := Ret 0.
  Definition tgt1: @state _ nat :=
    while_itree (fun u => (trigger (Fair (fun id => (if ndec 0 id then Flag.fail else Flag.emp)))) >>= (fun r => Ret (inl r)));; Ret 0.

  Definition imsrc1: imap := fun id => (if ndec 0 id then 100 else 0).
  Definition imtgt1: imap := fun id => (if ndec 0 id then 100 else 0).

  Goal sim RR false imsrc1 false imtgt1 src1 tgt1.
  Proof.
    unfold src1, tgt1.
    pcofix CIH. pfold. rewrite unfold_while_itree. ired.
    econs 8. i.
    econs.
    { rewrite unfold_while_itree. ired. econs 8. i.
      instantiate (1:= fun id => 0) in FAIR0.
      exfalso. unfold fair_update in FAIR0. specialize FAIR0 with 0. ss. inv FAIR0.
    }
    ii. apply PeanoNat.Nat.le_0_l.
  Qed.

End EX.
