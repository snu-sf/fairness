From sflib Require Import sflib.
From ITree Require Export ITree.
From Paco Require Import paco.

Require Import Coq.Classes.RelationClasses.
Require Import Program.
Require Import Permutation.

Export ITreeNotations.

From Fairness Require Import Axioms.
From Fairness Require Export ITreeLib FairBeh FairSim NatStructs.
From Fairness Require Import pind PCM World WFLib.
From Fairness Require Export Mod ModSimNoSync ModSimStutter.

Set Implicit Arguments.

(* Section GENORDER. *)
(*   Context `{M: URA.t}. *)

(*   Variable state_src: Type. *)
(*   Variable state_tgt: Type. *)

(*   Variable _ident_src: ID. *)
(*   Definition ident_src := sum_tid _ident_src. *)
(*   Variable _ident_tgt: ID. *)
(*   Definition ident_tgt := sum_tid _ident_tgt. *)

(*   Variable wf_src: WF. *)
(*   Variable wf_tgt: WF. *)

(*   Let srcE := ((@eventE _ident_src +' cE) +' sE state_src). *)
(*   Let tgtE := ((@eventE _ident_tgt +' cE) +' sE state_tgt). *)

(*   Let shared := *)
(*     (TIdSet.t * *)
(*        (@imap ident_src wf_src) * *)
(*        (@imap ident_tgt wf_tgt) * *)
(*        state_src * *)
(*        state_tgt * *)
(*        URA.car)%type. *)

(*   Let shared_rel: Type := shared -> Prop. *)

(*   Variable I: shared_rel. *)

(*   Let A R0 R1 := (bool * bool * URA.car * (itree srcE R0) * (itree tgtE R1) * shared)%type. *)
(*   Let wf_ot {R0 R1} := @ord_tree_WF (A R0 R1). *)
(*   Let wf_stt {R0 R1} := sum_WF (@wf_ot R0 R1) (@wf_ot R0 R1). *)

(*   Variant _geno *)
(*           (tid: thread_id) *)
(*           (geno: forall R_src R_tgt (RR: R_src -> R_tgt -> URA.car -> shared_rel), bool -> bool -> URA.car -> ((@wf_stt R_src R_tgt).(T) * itree srcE R_src) -> itree tgtE R_tgt -> shared_rel) *)
(*           R_src R_tgt (RR: R_src -> R_tgt -> URA.car -> shared_rel) *)
(*     : *)
(*     bool -> bool -> URA.car -> ((@wf_stt R_src R_tgt).(T) * itree srcE R_src) -> itree tgtE R_tgt -> shared_rel := *)
(*   | geno_ret *)
(*       f_src f_tgt r_ctx o *)
(*       ths im_src im_tgt st_src st_tgt r_shared *)
(*       r_src r_tgt *)
(*       ol or ol0 or0 *)
(*       (FL: f_src = false -> o = inl ol) *)
(*       (TR: f_src = true -> o = inr or) *)
(*       (LTL: wf_ot.(lt) ol0 ol) *)
(*       (LTR: wf_ot.(lt) or0 or) *)
(*       (GENO: RR r_src r_tgt r_ctx (ths, im_src, im_tgt, st_src, st_tgt, r_shared)) *)
(*     : *)
(*     _geno tid geno RR f_src f_tgt r_ctx (o, Ret r_src) (Ret r_tgt) (ths, im_src, im_tgt, st_src, st_tgt, r_shared) *)

(*   | geno_tauL *)
(*       f_src f_tgt r_ctx o *)
(*       ths im_src im_tgt st_src st_tgt r_shared *)
(*       itr_src itr_tgt *)
(*       ol or *)
(*       (FL: f_src = false -> o = inl ol) *)
(*       (TR: f_src = true -> o = inr or) *)
(*       o1 (GENO: geno _ _ RR true f_tgt r_ctx (inr o1, itr_src) itr_tgt (ths, im_src, im_tgt, st_src, st_tgt, r_shared)) *)
(*     : *)
(*     _geno tid geno RR f_src f_tgt r_ctx (o, Tau itr_src) itr_tgt (ths, im_src, im_tgt, st_src, st_tgt, r_shared) *)
(*   | geno_chooseL *)
(*       f_src f_tgt r_ctx o *)
(*       ths im_src im_tgt st_src st_tgt r_shared *)
(*       X ktr_src itr_tgt *)
(*       ol or *)
(*       (FL: f_src = false -> o = inl ol) *)
(*       (TR: f_src = true -> o = inr or) *)
(*       o1 (GENO: exists x, geno _ _ RR true f_tgt r_ctx (inr o1, ktr_src x) itr_tgt (ths, im_src, im_tgt, st_src, st_tgt, r_shared)) *)
(*     : *)
(*     _geno tid geno RR f_src f_tgt r_ctx (o, trigger (Choose X) >>= ktr_src) itr_tgt (ths, im_src, im_tgt, st_src, st_tgt, r_shared) *)
(*   | geno_putL *)
(*       f_src f_tgt r_ctx o *)
(*       ths im_src im_tgt st_src st_tgt r_shared *)
(*       st ktr_src itr_tgt *)
(*       ol or *)
(*       (FL: f_src = false -> o = inl ol) *)
(*       (TR: f_src = true -> o = inr or) *)
(*       o1 (GENO: geno _ _ RR true f_tgt r_ctx (inr o1, ktr_src tt) itr_tgt (ths, im_src, im_tgt, st, st_tgt, r_shared)) *)
(*     : *)
(*     _geno tid geno RR f_src f_tgt r_ctx (o, trigger (Put st) >>= ktr_src) itr_tgt (ths, im_src, im_tgt, st_src, st_tgt, r_shared) *)
(*   | geno_getL *)
(*       f_src f_tgt r_ctx o *)
(*       ths im_src im_tgt st_src st_tgt r_shared *)
(*       ktr_src itr_tgt *)
(*       ol or *)
(*       (FL: f_src = false -> o = inl ol) *)
(*       (TR: f_src = true -> o = inr or) *)
(*       o1 (GENO: geno _ _ RR true f_tgt r_ctx (inr o1, ktr_src st_src) itr_tgt (ths, im_src, im_tgt, st_src, st_tgt, r_shared)) *)
(*     : *)
(*     _geno tid geno RR f_src f_tgt r_ctx (o, trigger (@Get _) >>= ktr_src) itr_tgt (ths, im_src, im_tgt, st_src, st_tgt, r_shared) *)
(*   | geno_tidL *)
(*       f_src f_tgt r_ctx o *)
(*       ths im_src im_tgt st_src st_tgt r_shared *)
(*       ktr_src itr_tgt *)
(*       ol or *)
(*       (FL: f_src = false -> o = inl ol) *)
(*       (TR: f_src = true -> o = inr or) *)
(*       o1 (GENO: geno _ _ RR true f_tgt r_ctx (inr o1, ktr_src tid) itr_tgt (ths, im_src, im_tgt, st_src, st_tgt, r_shared)) *)
(*     : *)
(*     _geno tid geno RR f_src f_tgt r_ctx (o, trigger (GetTid) >>= ktr_src) itr_tgt (ths, im_src, im_tgt, st_src, st_tgt, r_shared) *)
(*   | geno_UB *)
(*       f_src f_tgt r_ctx o *)
(*       ths im_src im_tgt st_src st_tgt r_shared *)
(*       ktr_src itr_tgt *)
(*       ol or *)
(*       (FL: f_src = false -> o = inl ol) *)
(*       (TR: f_src = true -> o = inr or) *)
(*     : *)
(*     _geno tid geno RR f_src f_tgt r_ctx (o, trigger (Undefined) >>= ktr_src) itr_tgt (ths, im_src, im_tgt, st_src, st_tgt, r_shared) *)
(*   | geno_fairL *)
(*       f_src f_tgt r_ctx o *)
(*       ths im_src0 im_tgt st_src st_tgt r_shared *)
(*       f ktr_src itr_tgt *)
(*       ol or *)
(*       (FL: f_src = false -> o = inl ol) *)
(*       (TR: f_src = true -> o = inr or) *)
(*       o1 (GENO: exists im_src1, *)
(*              (<<FAIR: fair_update im_src0 im_src1 (sum_fmap_r f)>>) /\ *)
(*                (<<GENO: geno _ _ RR true f_tgt r_ctx (inr o1, ktr_src tt) itr_tgt (ths, im_src1, im_tgt, st_src, st_tgt, r_shared)>>)) *)
(*     : *)
(*     _geno tid geno RR f_src f_tgt r_ctx (o, trigger (Fair f) >>= ktr_src) itr_tgt (ths, im_src0, im_tgt, st_src, st_tgt, r_shared) *)

(*   | geno_tauR *)
(*       f_src f_tgt r_ctx o *)
(*       ths im_src im_tgt st_src st_tgt r_shared *)
(*       itr_src itr_tgt *)
(*       ol or *)
(*       (FL: f_src = false -> o = inl ol) *)
(*       (TR: f_src = true -> o = inr or) *)
(*       (GENO: geno _ _ RR f_src true r_ctx (o, itr_src) itr_tgt (ths, im_src, im_tgt, st_src, st_tgt, r_shared)) *)
(*     : *)
(*     _geno tid geno RR f_src f_tgt r_ctx (o, itr_src) (Tau itr_tgt) (ths, im_src, im_tgt, st_src, st_tgt, r_shared) *)
(*   | geno_chooseR *)
(*       f_src f_tgt r_ctx o *)
(*       ths im_src im_tgt st_src st_tgt r_shared *)
(*       X itr_src ktr_tgt *)
(*       ol or *)
(*       (FL: f_src = false -> o = inl ol) *)
(*       (TR: f_src = true -> o = inr or) *)
(*       (GENO: forall x, geno _ _ RR f_src true r_ctx (o, itr_src) (ktr_tgt x) (ths, im_src, im_tgt, st_src, st_tgt, r_shared)) *)
(*     : *)
(*     _geno tid geno RR f_src f_tgt r_ctx (o, itr_src) (trigger (Choose X) >>= ktr_tgt) (ths, im_src, im_tgt, st_src, st_tgt, r_shared) *)
(*   | geno_putR *)
(*       f_src f_tgt r_ctx o *)
(*       ths im_src im_tgt st_src st_tgt r_shared *)
(*       st itr_src ktr_tgt *)
(*       ol or *)
(*       (FL: f_src = false -> o = inl ol) *)
(*       (TR: f_src = true -> o = inr or) *)
(*       (GENO: geno _ _ RR f_src true r_ctx (o, itr_src) (ktr_tgt tt) (ths, im_src, im_tgt, st_src, st, r_shared)) *)
(*     : *)
(*     _geno tid geno RR f_src f_tgt r_ctx (o, itr_src) (trigger (Put st) >>= ktr_tgt) (ths, im_src, im_tgt, st_src, st_tgt, r_shared) *)
(*   | geno_getR *)
(*       f_src f_tgt r_ctx o *)
(*       ths im_src im_tgt st_src st_tgt r_shared *)
(*       itr_src ktr_tgt *)
(*       ol or *)
(*       (FL: f_src = false -> o = inl ol) *)
(*       (TR: f_src = true -> o = inr or) *)
(*       (GENO: geno _ _ RR f_src true r_ctx (o, itr_src) (ktr_tgt st_tgt) (ths, im_src, im_tgt, st_src, st_tgt, r_shared)) *)
(*     : *)
(*     _geno tid geno RR f_src f_tgt r_ctx (o, itr_src) (trigger (@Get _) >>= ktr_tgt) (ths, im_src, im_tgt, st_src, st_tgt, r_shared) *)
(*   | geno_tidR *)
(*       f_src f_tgt r_ctx o *)
(*       ths im_src im_tgt st_src st_tgt r_shared *)
(*       itr_src ktr_tgt *)
(*       ol or *)
(*       (FL: f_src = false -> o = inl ol) *)
(*       (TR: f_src = true -> o = inr or) *)
(*       (GENO: geno _ _ RR f_src true r_ctx (o, itr_src) (ktr_tgt tid) (ths, im_src, im_tgt, st_src, st_tgt, r_shared)) *)
(*     : *)
(*     _geno tid geno RR f_src f_tgt r_ctx (o, itr_src) (trigger (GetTid) >>= ktr_tgt) (ths, im_src, im_tgt, st_src, st_tgt, r_shared) *)
(*   | geno_fairR *)
(*       f_src f_tgt r_ctx o *)
(*       ths im_src im_tgt0 st_src st_tgt r_shared *)
(*       f itr_src ktr_tgt *)
(*       ol or *)
(*       (FL: f_src = false -> o = inl ol) *)
(*       (TR: f_src = true -> o = inr or) *)
(*       (GENO: forall im_tgt1 *)
(*                    (FAIR: fair_update im_tgt0 im_tgt1 (sum_fmap_r f)), *)
(*           (<<GENO: geno _ _ RR f_src true r_ctx (o, itr_src) (ktr_tgt tt) (ths, im_src, im_tgt1, st_src, st_tgt, r_shared)>>)) *)
(*     : *)
(*     _geno tid geno RR f_src f_tgt r_ctx (o, itr_src) (trigger (Fair f) >>= ktr_tgt) (ths, im_src, im_tgt0, st_src, st_tgt, r_shared) *)

(*   | geno_observe *)
(*       f_src f_tgt r_ctx o *)
(*       ths im_src im_tgt st_src st_tgt r_shared *)
(*       fn args ktr_src ktr_tgt *)
(*       ol or *)
(*       (FL: f_src = false -> o = inl ol) *)
(*       (TR: f_src = true -> o = inr or) *)
(*       o1 (GENO: forall ret, *)
(*              geno _ _ RR true true r_ctx (inr o1, ktr_src ret) (ktr_tgt ret) (ths, im_src, im_tgt, st_src, st_tgt, r_shared)) *)
(*     : *)
(*     _geno tid geno RR f_src f_tgt r_ctx (o, trigger (Observe fn args) >>= ktr_src) (trigger (Observe fn args) >>= ktr_tgt) (ths, im_src, im_tgt, st_src, st_tgt, r_shared) *)

(*   | geno_yieldR *)
(*       f_src f_tgt r_ctx0 o0 *)
(*       ths0 im_src0 im_tgt0 st_src0 st_tgt0 r_shared0 *)
(*       r_own r_shared *)
(*       ktr_src ktr_tgt *)
(*       ol0 or0 *)
(*       (FL: f_src = false -> o0 = inl ol0) *)
(*       (TR: f_src = true -> o0 = inr or0) *)
(*       (INV: I (ths0, im_src0, im_tgt0, st_src0, st_tgt0, r_shared)) *)
(*       (VALID: URA.wf (r_shared ⋅ r_own ⋅ r_ctx0)) *)
(*       (GENOF: (f_src = false) -> *)
(*               forall ths1 im_src1 im_tgt1 st_src1 st_tgt1 r_shared1 r_ctx1 *)
(*                 (INV: I (ths1, im_src1, im_tgt1, st_src1, st_tgt1, r_shared1)) *)
(*                 (VALID: URA.wf (r_shared1 ⋅ r_own ⋅ r_ctx1)) *)
(*                 im_tgt2 *)
(*                 (TGT: fair_update im_tgt1 im_tgt2 (sum_fmap_l (tids_fmap tid ths1))), *)
(*               exists ol1, *)
(*                 (<<GENO: geno _ _ RR f_src true r_ctx1 (inl ol1, trigger (Yield) >>= ktr_src) (ktr_tgt tt) (ths1, im_src1, im_tgt2, st_src1, st_tgt1, r_shared1)>>) /\ *)
(*                   (<<STUTTER: wf_ot.(lt) ol1 ol0>>)) *)
(*       (GENOT: (f_src = true) -> *)
(*               forall ths1 im_src1 im_tgt1 st_src1 st_tgt1 r_shared1 r_ctx1 *)
(*                 (INV: I (ths1, im_src1, im_tgt1, st_src1, st_tgt1, r_shared1)) *)
(*                 (VALID: URA.wf (r_shared1 ⋅ r_own ⋅ r_ctx1)) *)
(*                 im_tgt2 *)
(*                 (TGT: fair_update im_tgt1 im_tgt2 (sum_fmap_l (tids_fmap tid ths1))), *)
(*               exists or1, *)
(*                 (<<GENO: geno _ _ RR f_src true r_ctx1 (inr or1, trigger (Yield) >>= ktr_src) (ktr_tgt tt) (ths1, im_src1, im_tgt2, st_src1, st_tgt1, r_shared1)>>) /\ *)
(*                   (<<STUTTER: wf_ot.(lt) or1 or0>>)) *)
(*     : *)
(*     _geno tid geno RR f_src f_tgt r_ctx0 (o0, trigger (Yield) >>= ktr_src) (trigger (Yield) >>= ktr_tgt) (ths0, im_src0, im_tgt0, st_src0, st_tgt0, r_shared0) *)

(*   | geno_yieldL *)
(*       f_src f_tgt r_ctx o0 *)
(*       ths im_src0 im_tgt st_src st_tgt r_shared *)
(*       ktr_src itr_tgt *)
(*       ol0 or0 *)
(*       (FL: f_src = false -> o0 = inl ol0) *)
(*       (TR: f_src = true -> o0 = inr or0) *)
(*       (GENO: exists im_src1 o1, *)
(*           (<<FAIR: fair_update im_src0 im_src1 (sum_fmap_l (tids_fmap tid ths))>>) /\ *)
(*             (<<GENO: geno _ _ RR true f_tgt r_ctx (inr o1, ktr_src tt) itr_tgt (ths, im_src1, im_tgt, st_src, st_tgt, r_shared)>>)) *)
(*     : *)
(*     _geno tid geno RR f_src f_tgt r_ctx (o0, trigger (Yield) >>= ktr_src) itr_tgt (ths, im_src0, im_tgt, st_src, st_tgt, r_shared) *)

(*   | geno_progress *)
(*       r_ctx o *)
(*       ths im_src im_tgt st_src st_tgt r_shared *)
(*       itr_src itr_tgt *)
(*       (GENO: ModSimNoSync.lsim I tid RR false false r_ctx itr_src itr_tgt (ths, im_src, im_tgt, st_src, st_tgt, r_shared)) *)
(*     : *)
(*     _geno tid geno RR true true r_ctx (inr o, itr_src) itr_tgt (ths, im_src, im_tgt, st_src, st_tgt, r_shared) *)
(*   . *)

(*   Definition geno (tid: thread_id) *)
(*              R_src R_tgt (RR: R_src -> R_tgt -> URA.car -> shared_rel): *)
(*     bool -> bool -> URA.car -> (wf_stt.(T) * itree srcE R_src) -> itree tgtE R_tgt -> shared_rel := *)
(*     pind9 (_geno tid) top9 R_src R_tgt RR. *)

(*   Lemma geno_mon tid: monotone9 (_geno tid). *)
(*   Proof. *)
(*     ii. inv IN; try (econs; eauto; fail). *)
(*     { des. econs; eauto. } *)
(*     { des. econs; eauto. } *)
(*     { econs; eauto. i. eapply LE. eapply GENO. eauto. } *)
(*     { econs; eauto. *)
(*       - clear GENOT. i. specialize (GENOF H _ _ _ _ _ _ _ INV0 VALID0 _ TGT). des. esplits; eauto. *)
(*       - clear GENOF. i. specialize (GENOT H _ _ _ _ _ _ _ INV0 VALID0 _ TGT). des. esplits; eauto. *)
(*     } *)
(*     { des. econs; esplits; eauto. } *)
(*   Qed. *)

(*   Local Hint Constructors _geno: core. *)
(*   Local Hint Unfold geno: core. *)
(*   Local Hint Resolve geno_mon: paco. *)

(*   (* Properties *) *)
(*   Lemma geno_sfalse_oright *)
(*         tid R0 R1 (RR: R0 -> R1 -> URA.car -> shared_rel) *)
(*         pt r_ctx src tgt shr o *)
(*     : *)
(*     ~ (geno tid RR false pt r_ctx (inr o, src) tgt shr). *)
(*   Proof. *)
(*     intros GENO. *)
(*     match goal with | GENO: geno _ _ ?_ps _ _ ?_osrc _ _ |- _ => remember _ps as ps; remember _osrc as osrc end. *)
(*     move GENO before tid. revert_until GENO. *)
(*     pattern R0, R1, RR, ps, pt, r_ctx, osrc, tgt, shr. *)
(*     revert R0 R1 RR ps pt r_ctx osrc tgt shr GENO. apply pind9_acc. *)
(*     intros rr DEC IH. clear DEC. intros R0 R1 RR ps pt r_ctx osrc tgt shr GENO. *)
(*     i; clarify. *)
(*     eapply pind9_unfold in GENO; eauto with paco. *)
(*     inv GENO; try (hexploit FL; ss; fail). *)
(*   Qed. *)

(*   Lemma geno_strue_oleft *)
(*         tid R0 R1 (RR: R0 -> R1 -> URA.car -> shared_rel) *)
(*         pt r_ctx src tgt shr o *)
(*     : *)
(*     ~ (geno tid RR true pt r_ctx (inl o, src) tgt shr). *)
(*   Proof. *)
(*     intros GENO. *)
(*     match goal with | GENO: geno _ _ ?_ps _ _ ?_osrc _ _ |- _ => remember _ps as ps; remember _osrc as osrc end. *)
(*     move GENO before tid. revert_until GENO. *)
(*     pattern R0, R1, RR, ps, pt, r_ctx, osrc, tgt, shr. *)
(*     revert R0 R1 RR ps pt r_ctx osrc tgt shr GENO. apply pind9_acc. *)
(*     intros rr DEC IH. clear DEC. intros R0 R1 RR ps pt r_ctx osrc tgt shr GENO. *)
(*     i; clarify. *)
(*     eapply pind9_unfold in GENO; eauto with paco. *)
(*     inv GENO; try (hexploit TR; ss; fail). *)
(*   Qed. *)

(*   Lemma geno_ord_weak_left *)
(*         tid R0 R1 (LRR: R0 -> R1 -> URA.car -> shared_rel) *)
(*         ps pt r_ctx src tgt (shr: shared) o0 o1 *)
(*         (LT: wf_ot.(lt) o0 o1) *)
(*         (GENO: geno tid LRR ps pt r_ctx (inl o0, src) tgt shr) *)
(*     : *)
(*     geno tid LRR ps pt r_ctx (inl o1, src) tgt shr. *)
(*   Proof. *)
(*     remember (inl o0, src) as osrc. *)
(*     move GENO before tid. revert_until GENO. *)
(*     pattern R0, R1, LRR, ps, pt, r_ctx, osrc, tgt, shr. *)
(*     revert R0 R1 LRR ps pt r_ctx osrc tgt shr GENO. apply pind9_acc. *)
(*     intros rr DEC IH. clear DEC. intros R0 R1 LRR ps pt r_ctx osrc tgt shr GENO. *)
(*     i; clarify. *)
(*     eapply pind9_unfold in GENO; eauto with paco. *)
(*     inv GENO. *)

(*     { eapply pind9_fold. econs 1; eauto. i. apply TR in H; ss. } *)
(*     { eapply pind9_fold. econs 2; eauto. i. apply TR in H; ss. *)
(*       eapply upind9_mon; eauto. ss. *)
(*       Unshelve. exact o2. *)
(*     } *)
(*     { eapply pind9_fold. econs 3; eauto. i. apply TR in H; ss. *)
(*       des. exists x. *)
(*       eapply upind9_mon; eauto. ss. *)
(*       Unshelve. exact o2. *)
(*     } *)
(*     { eapply pind9_fold. econs 4; eauto. i. apply TR in H; ss. *)
(*       eapply upind9_mon; eauto. ss. *)
(*       Unshelve. exact o2. *)
(*     } *)
(*     { eapply pind9_fold. econs 5; eauto. i. apply TR in H; ss. *)
(*       eapply upind9_mon; eauto. ss. *)
(*       Unshelve. exact o2. *)
(*     } *)
(*     { eapply pind9_fold. econs 6; eauto. i. apply TR in H; ss. *)
(*       eapply upind9_mon; eauto. ss. *)
(*       Unshelve. exact o2. *)
(*     } *)
(*     { eapply pind9_fold. econs 7; eauto. i. apply TR in H; ss. *)
(*       Unshelve. exact o0. *)
(*     } *)
(*     { eapply pind9_fold. econs 8; eauto. i. apply TR in H; ss. *)
(*       des. esplits; eauto. *)
(*       eapply upind9_mon; eauto. ss. *)
(*       Unshelve. exact o2. *)
(*     } *)

(*     { eapply pind9_fold. econs 9; eauto. i. apply TR in H; ss. *)
(*       split; ss. destruct GENO0 as [GENO IND]. eapply IH in IND; eauto. *)
(*       Unshelve. exact o1. *)
(*     } *)
(*     { eapply pind9_fold. econs 10; eauto. i. apply TR in H; ss. *)
(*       i. specialize (GENO0 x). *)
(*       split; ss. destruct GENO0 as [GENO IND]. eapply IH in IND; eauto. *)
(*       Unshelve. exact o1. *)
(*     } *)
(*     { eapply pind9_fold. econs 11; eauto. i. apply TR in H; ss. *)
(*       split; ss. destruct GENO0 as [GENO IND]. eapply IH in IND; eauto. *)
(*       Unshelve. exact o1. *)
(*     } *)
(*     { eapply pind9_fold. econs 12; eauto. i. apply TR in H; ss. *)
(*       split; ss. destruct GENO0 as [GENO IND]. eapply IH in IND; eauto. *)
(*       Unshelve. exact o1. *)
(*     } *)
(*     { eapply pind9_fold. econs 13; eauto. i. apply TR in H; ss. *)
(*       split; ss. destruct GENO0 as [GENO IND]. eapply IH in IND; eauto. *)
(*       Unshelve. exact o1. *)
(*     } *)
(*     { eapply pind9_fold. econs 14; eauto. i. apply TR in H; ss. *)
(*       i. specialize (GENO0 _ FAIR). *)
(*       split; ss. destruct GENO0 as [GENO IND]. eapply IH in IND; eauto. *)
(*       Unshelve. exact o1. *)
(*     } *)
(*     { eapply pind9_fold. econs 15; eauto. i. apply TR in H; ss. *)
(*       i. specialize (GENO0 ret). *)
(*       eapply upind9_mon; eauto. ss. *)
(*       Unshelve. exact o2. *)
(*     } *)

(*     { eapply pind9_fold. econs 16; eauto. i. apply TR in H; ss. *)
(*       - i. clear GENOT. specialize (GENOF H _ _ _ _ _ _ _ INV0 VALID0 _ TGT). *)
(*         des. esplits; eauto. *)
(*         split; ss. destruct GENO as [GENO IND]. eapply IH in IND; eauto. *)
(*         apply FL in H. clarify. *)
(*         Unshelve. exact o1. *)
(*       - i. clear GENOF. apply TR in H; ss. *)
(*     } *)

(*     { eapply pind9_fold. econs 17; eauto. i. apply TR in H; ss. *)
(*       des. esplits; eauto. destruct GENO as [GENO IND]. *)
(*       eapply upind9_mon; eauto. ss. *)
(*       Unshelve. exact o1. *)
(*     } *)

(*   Qed. *)

(*   Lemma geno_ord_weak_right *)
(*         tid R0 R1 (LRR: R0 -> R1 -> URA.car -> shared_rel) *)
(*         ps pt r_ctx src tgt (shr: shared) o0 o1 *)
(*         (LT: wf_ot.(lt) o0 o1) *)
(*         (GENO: geno tid LRR ps pt r_ctx (inr o0, src) tgt shr) *)
(*     : *)
(*     geno tid LRR ps pt r_ctx (inr o1, src) tgt shr. *)
(*   Proof. *)
(*     remember (inr o0, src) as osrc. *)
(*     move GENO before tid. revert_until GENO. *)
(*     pattern R0, R1, LRR, ps, pt, r_ctx, osrc, tgt, shr. *)
(*     revert R0 R1 LRR ps pt r_ctx osrc tgt shr GENO. apply pind9_acc. *)
(*     intros rr DEC IH. clear DEC. intros R0 R1 LRR ps pt r_ctx osrc tgt shr GENO. *)
(*     i; clarify. *)
(*     eapply pind9_unfold in GENO; eauto with paco. *)
(*     inv GENO. *)

(*     { eapply pind9_fold. econs 1; eauto. i. apply FL in H; ss. } *)
(*     { eapply pind9_fold. econs 2; eauto. i. apply FL in H; ss. *)
(*       eapply upind9_mon; eauto. ss. *)
(*       Unshelve. exact o2. *)
(*     } *)
(*     { eapply pind9_fold. econs 3; eauto. i. apply FL in H; ss. *)
(*       des. exists x. *)
(*       eapply upind9_mon; eauto. ss. *)
(*       Unshelve. exact o2. *)
(*     } *)
(*     { eapply pind9_fold. econs 4; eauto. i. apply FL in H; ss. *)
(*       eapply upind9_mon; eauto. ss. *)
(*       Unshelve. exact o2. *)
(*     } *)
(*     { eapply pind9_fold. econs 5; eauto. i. apply FL in H; ss. *)
(*       eapply upind9_mon; eauto. ss. *)
(*       Unshelve. exact o2. *)
(*     } *)
(*     { eapply pind9_fold. econs 6; eauto. i. apply FL in H; ss. *)
(*       eapply upind9_mon; eauto. ss. *)
(*       Unshelve. exact o2. *)
(*     } *)
(*     { eapply pind9_fold. econs 7; eauto. i. apply FL in H; ss. *)
(*       Unshelve. exact o0. *)
(*     } *)
(*     { eapply pind9_fold. econs 8; eauto. i. apply FL in H; ss. *)
(*       des. esplits; eauto. *)
(*       eapply upind9_mon; eauto. ss. *)
(*       Unshelve. exact o2. *)
(*     } *)

(*     { eapply pind9_fold. econs 9; eauto. i. apply FL in H; ss. *)
(*       split; ss. destruct GENO0 as [GENO IND]. eapply IH in IND; eauto. *)
(*       Unshelve. exact o1. *)
(*     } *)
(*     { eapply pind9_fold. econs 10; eauto. i. apply FL in H; ss. *)
(*       i. specialize (GENO0 x). *)
(*       split; ss. destruct GENO0 as [GENO IND]. eapply IH in IND; eauto. *)
(*       Unshelve. exact o1. *)
(*     } *)
(*     { eapply pind9_fold. econs 11; eauto. i. apply FL in H; ss. *)
(*       split; ss. destruct GENO0 as [GENO IND]. eapply IH in IND; eauto. *)
(*       Unshelve. exact o1. *)
(*     } *)
(*     { eapply pind9_fold. econs 12; eauto. i. apply FL in H; ss. *)
(*       split; ss. destruct GENO0 as [GENO IND]. eapply IH in IND; eauto. *)
(*       Unshelve. exact o1. *)
(*     } *)
(*     { eapply pind9_fold. econs 13; eauto. i. apply FL in H; ss. *)
(*       split; ss. destruct GENO0 as [GENO IND]. eapply IH in IND; eauto. *)
(*       Unshelve. exact o1. *)
(*     } *)
(*     { eapply pind9_fold. econs 14; eauto. i. apply FL in H; ss. *)
(*       i. specialize (GENO0 _ FAIR). *)
(*       split; ss. destruct GENO0 as [GENO IND]. eapply IH in IND; eauto. *)
(*       Unshelve. exact o1. *)
(*     } *)
(*     { eapply pind9_fold. econs 15; eauto. i. apply FL in H; ss. *)
(*       i. specialize (GENO0 ret). *)
(*       eapply upind9_mon; eauto. ss. *)
(*       Unshelve. exact o2. *)
(*     } *)

(*     { eapply pind9_fold. econs 16; eauto. i. apply FL in H; ss. *)
(*       - i. clear GENOT. apply FL in H; ss. *)
(*       - i. clear GENOF. specialize (GENOT H _ _ _ _ _ _ _ INV0 VALID0 _ TGT). *)
(*         des. esplits; eauto. *)
(*         split; ss. destruct GENO as [GENO IND]. eapply IH in IND; eauto. *)
(*         apply TR in H. clarify. *)
(*         Unshelve. exact o1. *)
(*     } *)

(*     { eapply pind9_fold. econs 17; eauto. i. apply FL in H; ss. *)
(*       des. esplits; eauto. destruct GENO as [GENO IND]. *)
(*       eapply upind9_mon; eauto. ss. *)
(*       Unshelve. exact o1. *)
(*     } *)

(*     { eapply pind9_fold. econs 18; eauto. } *)

(*   Qed. *)

(*   Lemma nosync_geno *)
(*         tid R0 R1 (RR: R0 -> R1 -> URA.car -> shared_rel) *)
(*         ps pt r_ctx src tgt shr *)
(*         (LSIM: ModSimNoSync.lsim I tid RR ps pt r_ctx src tgt shr) *)
(*     : *)
(*     exists o, geno tid RR ps pt r_ctx (o, src) tgt shr. *)
(*   Proof. *)
(*     punfold LSIM. *)
(*     pattern R0, R1, RR, ps, pt, r_ctx, src, tgt, shr. *)
(*     revert R0 R1 RR ps pt r_ctx src tgt shr LSIM. apply pind9_acc. *)
(*     intros rr DEC IH. clear DEC. intros R0 R1 RR ps pt r_ctx src tgt shr LSIM. *)
(*     eapply pind9_unfold in LSIM; eauto with paco. *)
(*     (* specialize (one R0 R1). specialize (@fzero R0 R1). *) *)
(*     set (fzero:= fun _: (A R0 R1) => @ord_tree_base (A R0 R1)). set (one:= ord_tree_cons fzero). *)
(*     inv LSIM. *)

(*     { exists (if ps then (inr one) else (inl one)). *)
(*       eapply pind9_fold. econs 1; eauto. des_ifs. des_ifs. *)
(*       1,2: instantiate (1:=fzero (ps, pt, r_ctx, Ret r_src, Ret r_tgt, (ths, im_src, im_tgt, st_src, st_tgt, r_shared))); ss. *)
(*     } *)

(*     { exists (if ps then (inr one) else (inl one)). *)
(*       destruct LSIM0 as [LSIM IND]. eapply IH in IND. des. *)
(*       destruct o. apply geno_strue_oleft in IND; ss. *)
(*       eapply pind9_fold. econs 2; eauto. 1,2: des_ifs. *)
(*       split; ss. eauto. *)
(*     } *)
(*     { exists (if ps then (inr one) else (inl one)). *)
(*       des. destruct LSIM0 as [LSIM IND]. eapply IH in IND. des. *)
(*       destruct o. apply geno_strue_oleft in IND; ss. *)
(*       eapply pind9_fold. econs 3; eauto. 1,2: des_ifs. *)
(*       eexists; split; ss. eauto. *)
(*     } *)
(*     { exists (if ps then (inr one) else (inl one)). *)
(*       destruct LSIM0 as [LSIM IND]. eapply IH in IND. des. *)
(*       destruct o. apply geno_strue_oleft in IND; ss. *)
(*       eapply pind9_fold. econs 4; eauto. 1,2: des_ifs. *)
(*       split; ss. eauto. *)
(*     } *)
(*     { exists (if ps then (inr one) else (inl one)). *)
(*       destruct LSIM0 as [LSIM IND]. eapply IH in IND. des. *)
(*       destruct o. apply geno_strue_oleft in IND; ss. *)
(*       eapply pind9_fold. econs 5; eauto. 1,2: des_ifs. *)
(*       split; ss. eauto. *)
(*     } *)
(*     { exists (if ps then (inr one) else (inl one)). *)
(*       destruct LSIM0 as [LSIM IND]. eapply IH in IND. des. *)
(*       destruct o. apply geno_strue_oleft in IND; ss. *)
(*       eapply pind9_fold. econs 6; eauto. 1,2: des_ifs. *)
(*       split; ss. eauto. *)
(*     } *)
(*     { exists (if ps then (inr one) else (inl one)). *)
(*       eapply pind9_fold. econs 7; eauto. 1,2: des_ifs. *)
(*     } *)
(*     { exists (if ps then (inr one) else (inl one)). *)
(*       des. destruct LSIM as [LSIM IND]. eapply IH in IND. des. *)
(*       destruct o. apply geno_strue_oleft in IND; ss. *)
(*       eapply pind9_fold. econs 8; eauto. 1,2: des_ifs. *)
(*       esplits; eauto. split; ss. eauto. *)
(*     } *)

(*     { destruct LSIM0 as [LSIM IND]. eapply IH in IND. des. exists o. *)
(*       destruct ps; destruct o. *)
(*       1:{ apply geno_strue_oleft in IND; ss. } *)
(*       3:{ apply geno_sfalse_oright in IND; ss. } *)
(*       - eapply pind9_fold. econs 9; eauto. ss. split; ss; auto. *)
(*       - eapply pind9_fold. econs 9; eauto. ss. split; ss; auto. *)
(*         Unshelve. all: exact t. *)
(*     } *)

(*     { hexploit ord_tree_join. *)
(*       { instantiate (2:=A R0 R1). *)
(*         instantiate (2:= fun '(ps, pt, rs, src, tgt, shr) => @rr R0 R1 RR ps pt rs src tgt shr). *)
(*         i. ss. des_ifs. eapply IH in SAT. *)
(*         instantiate (1:= fun '(ps, pt, rs, src, tgt, shr) o => *)
(*                            geno tid RR ps pt rs (if ps then (inr o) else (inl o), src) tgt shr). *)
(*         des. destruct b; destruct o. *)
(*         1:{ apply geno_strue_oleft in SAT; ss. } *)
(*         3:{ apply geno_sfalse_oright in SAT; ss. } *)
(*         all: eauto. *)
(*       } *)
(*       intro JOIN. des. exists (if ps then (inr o1) else (inl o1)). *)
(*       eapply pind9_fold. econs 10. 1,2: des_ifs. *)
(*       i. specialize (LSIM0 x). destruct LSIM0 as [LSIM IND]. *)
(*       specialize (JOIN (ps, true, r_ctx, src, (ktr_tgt x), (ths, im_src, im_tgt, st_src, st_tgt, r_shared))). *)
(*       destruct JOIN; auto. des. split; ss. des_ifs. *)
(*       eapply geno_ord_weak_right; eauto. *)
(*       eapply geno_ord_weak_left; eauto. *)
(*     } *)

(*     { destruct LSIM0 as [LSIM IND]. eapply IH in IND. des. exists o. *)
(*       destruct ps; destruct o. *)
(*       1:{ apply geno_strue_oleft in IND; ss. } *)
(*       3:{ apply geno_sfalse_oright in IND; ss. } *)
(*       - eapply pind9_fold. econs 11; eauto. ss. split; ss; auto. *)
(*       - eapply pind9_fold. econs 11; eauto. ss. split; ss; auto. *)
(*         Unshelve. all: exact t. *)
(*     } *)
(*     { destruct LSIM0 as [LSIM IND]. eapply IH in IND. des. exists o. *)
(*       destruct ps; destruct o. *)
(*       1:{ apply geno_strue_oleft in IND; ss. } *)
(*       3:{ apply geno_sfalse_oright in IND; ss. } *)
(*       - eapply pind9_fold. econs 12; eauto. ss. split; ss; auto. *)
(*       - eapply pind9_fold. econs 12; eauto. ss. split; ss; auto. *)
(*         Unshelve. all: exact t. *)
(*     } *)
(*     { destruct LSIM0 as [LSIM IND]. eapply IH in IND. des. exists o. *)
(*       destruct ps; destruct o. *)
(*       1:{ apply geno_strue_oleft in IND; ss. } *)
(*       3:{ apply geno_sfalse_oright in IND; ss. } *)
(*       - eapply pind9_fold. econs 13; eauto. ss. split; ss; auto. *)
(*       - eapply pind9_fold. econs 13; eauto. ss. split; ss; auto. *)
(*         Unshelve. all: exact t. *)
(*     } *)

(*     { hexploit ord_tree_join. *)
(*       { instantiate (2:=A R0 R1). *)
(*         instantiate (2:= fun '(ps, pt, rs, src, tgt, shr) => @rr R0 R1 RR ps pt rs src tgt shr). *)
(*         i. ss. des_ifs. eapply IH in SAT. *)
(*         instantiate (1:= fun '(ps, pt, rs, src, tgt, shr) o => *)
(*                            geno tid RR ps pt rs (if ps then (inr o) else (inl o), src) tgt shr). *)
(*         des. destruct b; destruct o. *)
(*         1:{ apply geno_strue_oleft in SAT; ss. } *)
(*         3:{ apply geno_sfalse_oright in SAT; ss. } *)
(*         all: eauto. *)
(*       } *)
(*       intro JOIN. des. exists (if ps then (inr o1) else (inl o1)). *)
(*       eapply pind9_fold. econs 14. 1,2: des_ifs. *)
(*       i. specialize (LSIM0 _ FAIR). destruct LSIM0 as [LSIM IND]. *)
(*       specialize (JOIN (ps, true, r_ctx, src, (ktr_tgt ()), (ths, im_src, im_tgt1, st_src, st_tgt, r_shared))). *)
(*       destruct JOIN; auto. des. split; ss. des_ifs. *)
(*       eapply geno_ord_weak_right; eauto. *)
(*       eapply geno_ord_weak_left; eauto. *)
(*     } *)

(*     { hexploit ord_tree_join. *)
(*       { instantiate (2:=A R0 R1). *)
(*         instantiate (2:= fun '(ps, pt, rs, src, tgt, shr) => @rr R0 R1 RR ps pt rs src tgt shr). *)
(*         i. ss. des_ifs. eapply IH in SAT. *)
(*         instantiate (1:= fun '(ps, pt, rs, src, tgt, shr) o => *)
(*                            geno tid RR ps pt rs (if ps then (inr o) else (inl o), src) tgt shr). *)
(*         des. destruct b; destruct o. *)
(*         1:{ apply geno_strue_oleft in SAT; ss. } *)
(*         3:{ apply geno_sfalse_oright in SAT; ss. } *)
(*         all: eauto. *)
(*       } *)
(*       intro JOIN. des. exists (if ps then (inr o1) else (inl o1)). *)
(*       eapply pind9_fold. econs 15. 1,2: des_ifs. *)
(*       i. specialize (LSIM0 ret). destruct LSIM0 as [LSIM IND]. *)
(*       specialize (JOIN (true, true, r_ctx, ktr_src ret, ktr_tgt ret, (ths, im_src, im_tgt, st_src, st_tgt, r_shared))). *)
(*       destruct JOIN; auto. des. split; ss. *)
(*       eapply geno_ord_weak_right; eauto. *)
(*     } *)

(*     { hexploit ord_tree_join. *)
(*       { instantiate (2:=A R0 R1). *)
(*         instantiate (2:= fun '(ps, pt, rs, src, tgt, shr) => @rr R0 R1 RR ps pt rs src tgt shr). *)
(*         i. ss. des_ifs. eapply IH in SAT. *)
(*         instantiate (1:= fun '(ps, pt, rs, src, tgt, shr) o => *)
(*                            geno tid RR ps pt rs (if ps then (inr o) else (inl o), src) tgt shr). *)
(*         des. destruct b; destruct o. *)
(*         1:{ apply geno_strue_oleft in SAT; ss. } *)
(*         3:{ apply geno_sfalse_oright in SAT; ss. } *)
(*         all: eauto. *)
(*       } *)
(*       intro JOIN. des. exists (if ps then (inr o1) else (inl o1)). *)
(*       eapply pind9_fold. econs 16. 1,2: des_ifs. *)
(*       1,2: eauto. *)
(*       - i. specialize (LSIM0 _ _ _ _ _ _ _ INV0 VALID0 _ TGT). destruct LSIM0 as [LSIM IND]. *)
(*         specialize (JOIN (ps, true, r_ctx1, (x <- trigger Yield;; ktr_src x), ktr_tgt (), (ths1, im_src1, im_tgt2, st_src1, st_tgt1, r_shared1))). *)
(*         destruct JOIN; auto. des. clarify. esplits; eauto. split; ss. *)
(*       - i. specialize (LSIM0 _ _ _ _ _ _ _ INV0 VALID0 _ TGT). destruct LSIM0 as [LSIM IND]. *)
(*         specialize (JOIN (ps, true, r_ctx1, (x <- trigger Yield;; ktr_src x), ktr_tgt (), (ths1, im_src1, im_tgt2, st_src1, st_tgt1, r_shared1))). *)
(*         destruct JOIN; auto. des. clarify. esplits; eauto. split; ss. *)
(*     } *)

(*     { des. destruct LSIM as [LSIM IND]. eapply IH in IND. des. *)
(*       destruct o. apply geno_strue_oleft in IND; ss. *)
(*       exists (if ps then (inr one) else (inl one)). *)
(*       eapply pind9_fold. econs 17; eauto. 1,2: des_ifs. esplits; eauto. *)
(*       split; ss. eauto. *)
(*     } *)

(*     { exists (inr (@ord_tree_base _)). eapply pind9_fold. econs 18. pclearbot. auto. } *)

(*   Qed. *)

(*   (*TODO: reduction lemmas*) *)

(* End GENORDER. *)
(* #[export] Hint Constructors _geno: core. *)
(* #[export] Hint Unfold geno: core. *)
(* #[export] Hint Resolve geno_mon: paco. *)

Section GENORDER.
  Context `{M: URA.t}.

  Variable state_src: Type.
  Variable state_tgt: Type.

  Variable _ident_src: ID.
  Let ident_src := @ident_src _ident_src.
  Variable _ident_tgt: ID.
  Let ident_tgt := @ident_tgt _ident_tgt.

  Variable wf_src: WF.
  Variable wf_tgt: WF.

  Let srcE := ((@eventE _ident_src +' cE) +' sE state_src).
  Let tgtE := ((@eventE _ident_tgt +' cE) +' sE state_tgt).

  Let shared :=
    (TIdSet.t *
       (@imap ident_src wf_src) *
       (@imap ident_tgt wf_tgt) *
       state_src *
       state_tgt *
       URA.car)%type.

  Let shared_rel: Type := shared -> Prop.

  Variable I: shared_rel.

  Let A R0 R1 := (bool * bool * URA.car * (itree srcE R0) * (itree tgtE R1) * shared)%type.
  Let wf_stt {R0 R1} := @ord_tree_WF (A R0 R1).

  Variant _geno
          (tid: thread_id)
          (geno: forall R_src R_tgt (RR: R_src -> R_tgt -> URA.car -> shared_rel), bool -> bool -> URA.car -> ((@wf_stt R_src R_tgt).(T) * itree srcE R_src) -> itree tgtE R_tgt -> shared_rel)
          R_src R_tgt (RR: R_src -> R_tgt -> URA.car -> shared_rel)
    :
    bool -> bool -> URA.car -> ((@wf_stt R_src R_tgt).(T) * itree srcE R_src) -> itree tgtE R_tgt -> shared_rel :=
  | geno_ret
      f_src f_tgt r_ctx o o0
      ths im_src im_tgt st_src st_tgt r_shared
      r_src r_tgt
      (LT: wf_stt.(lt) o0 o)
      (GENO: RR r_src r_tgt r_ctx (ths, im_src, im_tgt, st_src, st_tgt, r_shared))
    :
    _geno tid geno RR f_src f_tgt r_ctx (o, Ret r_src) (Ret r_tgt) (ths, im_src, im_tgt, st_src, st_tgt, r_shared)

  | geno_tauL
      f_src f_tgt r_ctx o
      ths im_src im_tgt st_src st_tgt r_shared
      itr_src itr_tgt
      (GENO: geno _ _ RR true f_tgt r_ctx (o, itr_src) itr_tgt (ths, im_src, im_tgt, st_src, st_tgt, r_shared))
    :
    _geno tid geno RR f_src f_tgt r_ctx (o, Tau itr_src) itr_tgt (ths, im_src, im_tgt, st_src, st_tgt, r_shared)
  | geno_chooseL
      f_src f_tgt r_ctx o
      ths im_src im_tgt st_src st_tgt r_shared
      X ktr_src itr_tgt
      (GENO: exists x, geno _ _ RR true f_tgt r_ctx (o, ktr_src x) itr_tgt (ths, im_src, im_tgt, st_src, st_tgt, r_shared))
    :
    _geno tid geno RR f_src f_tgt r_ctx (o, trigger (Choose X) >>= ktr_src) itr_tgt (ths, im_src, im_tgt, st_src, st_tgt, r_shared)
  | geno_putL
      f_src f_tgt r_ctx o
      ths im_src im_tgt st_src st_tgt r_shared
      st ktr_src itr_tgt
      (GENO: geno _ _ RR true f_tgt r_ctx (o, ktr_src tt) itr_tgt (ths, im_src, im_tgt, st, st_tgt, r_shared))
    :
    _geno tid geno RR f_src f_tgt r_ctx (o, trigger (Put st) >>= ktr_src) itr_tgt (ths, im_src, im_tgt, st_src, st_tgt, r_shared)
  | geno_getL
      f_src f_tgt r_ctx o
      ths im_src im_tgt st_src st_tgt r_shared
      ktr_src itr_tgt
      (GENO: geno _ _ RR true f_tgt r_ctx (o, ktr_src st_src) itr_tgt (ths, im_src, im_tgt, st_src, st_tgt, r_shared))
    :
    _geno tid geno RR f_src f_tgt r_ctx (o, trigger (@Get _) >>= ktr_src) itr_tgt (ths, im_src, im_tgt, st_src, st_tgt, r_shared)
  | geno_tidL
      f_src f_tgt r_ctx o
      ths im_src im_tgt st_src st_tgt r_shared
      ktr_src itr_tgt
      (GENO: geno _ _ RR true f_tgt r_ctx (o, ktr_src tid) itr_tgt (ths, im_src, im_tgt, st_src, st_tgt, r_shared))
    :
    _geno tid geno RR f_src f_tgt r_ctx (o, trigger (GetTid) >>= ktr_src) itr_tgt (ths, im_src, im_tgt, st_src, st_tgt, r_shared)
  | geno_UB
      f_src f_tgt r_ctx o
      ths im_src im_tgt st_src st_tgt r_shared
      ktr_src itr_tgt
    :
    _geno tid geno RR f_src f_tgt r_ctx (o, trigger (Undefined) >>= ktr_src) itr_tgt (ths, im_src, im_tgt, st_src, st_tgt, r_shared)
  | geno_fairL
      f_src f_tgt r_ctx o
      ths im_src0 im_tgt st_src st_tgt r_shared
      f ktr_src itr_tgt
      (GENO: exists im_src1,
             (<<FAIR: fair_update im_src0 im_src1 (sum_fmap_r f)>>) /\
               (<<GENO: geno _ _ RR true f_tgt r_ctx (o, ktr_src tt) itr_tgt (ths, im_src1, im_tgt, st_src, st_tgt, r_shared)>>))
    :
    _geno tid geno RR f_src f_tgt r_ctx (o, trigger (Fair f) >>= ktr_src) itr_tgt (ths, im_src0, im_tgt, st_src, st_tgt, r_shared)

  | geno_tauR
      f_src f_tgt r_ctx o
      ths im_src im_tgt st_src st_tgt r_shared
      itr_src itr_tgt
      (GENO: geno _ _ RR f_src true r_ctx (o, itr_src) itr_tgt (ths, im_src, im_tgt, st_src, st_tgt, r_shared))
    :
    _geno tid geno RR f_src f_tgt r_ctx (o, itr_src) (Tau itr_tgt) (ths, im_src, im_tgt, st_src, st_tgt, r_shared)
  | geno_chooseR
      f_src f_tgt r_ctx o
      ths im_src im_tgt st_src st_tgt r_shared
      X itr_src ktr_tgt
      (GENO: forall x, geno _ _ RR f_src true r_ctx (o, itr_src) (ktr_tgt x) (ths, im_src, im_tgt, st_src, st_tgt, r_shared))
    :
    _geno tid geno RR f_src f_tgt r_ctx (o, itr_src) (trigger (Choose X) >>= ktr_tgt) (ths, im_src, im_tgt, st_src, st_tgt, r_shared)
  | geno_putR
      f_src f_tgt r_ctx o
      ths im_src im_tgt st_src st_tgt r_shared
      st itr_src ktr_tgt
      (GENO: geno _ _ RR f_src true r_ctx (o, itr_src) (ktr_tgt tt) (ths, im_src, im_tgt, st_src, st, r_shared))
    :
    _geno tid geno RR f_src f_tgt r_ctx (o, itr_src) (trigger (Put st) >>= ktr_tgt) (ths, im_src, im_tgt, st_src, st_tgt, r_shared)
  | geno_getR
      f_src f_tgt r_ctx o
      ths im_src im_tgt st_src st_tgt r_shared
      itr_src ktr_tgt
      (GENO: geno _ _ RR f_src true r_ctx (o, itr_src) (ktr_tgt st_tgt) (ths, im_src, im_tgt, st_src, st_tgt, r_shared))
    :
    _geno tid geno RR f_src f_tgt r_ctx (o, itr_src) (trigger (@Get _) >>= ktr_tgt) (ths, im_src, im_tgt, st_src, st_tgt, r_shared)
  | geno_tidR
      f_src f_tgt r_ctx o
      ths im_src im_tgt st_src st_tgt r_shared
      itr_src ktr_tgt
      (GENO: geno _ _ RR f_src true r_ctx (o, itr_src) (ktr_tgt tid) (ths, im_src, im_tgt, st_src, st_tgt, r_shared))
    :
    _geno tid geno RR f_src f_tgt r_ctx (o, itr_src) (trigger (GetTid) >>= ktr_tgt) (ths, im_src, im_tgt, st_src, st_tgt, r_shared)
  | geno_fairR
      f_src f_tgt r_ctx o
      ths im_src im_tgt0 st_src st_tgt r_shared
      f itr_src ktr_tgt
      (GENO: forall im_tgt1
                   (FAIR: fair_update im_tgt0 im_tgt1 (sum_fmap_r f)),
          (<<GENO: geno _ _ RR f_src true r_ctx (o, itr_src) (ktr_tgt tt) (ths, im_src, im_tgt1, st_src, st_tgt, r_shared)>>))
    :
    _geno tid geno RR f_src f_tgt r_ctx (o, itr_src) (trigger (Fair f) >>= ktr_tgt) (ths, im_src, im_tgt0, st_src, st_tgt, r_shared)

  | geno_observe
      f_src f_tgt r_ctx o
      ths im_src im_tgt st_src st_tgt r_shared
      fn args ktr_src ktr_tgt
      (GENO: forall ret,
             geno _ _ RR true true r_ctx (o, ktr_src ret) (ktr_tgt ret) (ths, im_src, im_tgt, st_src, st_tgt, r_shared))
    :
    _geno tid geno RR f_src f_tgt r_ctx (o, trigger (Observe fn args) >>= ktr_src) (trigger (Observe fn args) >>= ktr_tgt) (ths, im_src, im_tgt, st_src, st_tgt, r_shared)

  | geno_yieldR
      f_src f_tgt r_ctx0 o0
      ths0 im_src0 im_tgt0 st_src0 st_tgt0 r_shared0
      r_own r_shared
      ktr_src ktr_tgt
      (INV: I (ths0, im_src0, im_tgt0, st_src0, st_tgt0, r_shared))
      (VALID: URA.wf (r_shared ⋅ r_own ⋅ r_ctx0))
      (GENO: forall ths1 im_src1 im_tgt1 st_src1 st_tgt1 r_shared1 r_ctx1
               (INV: I (ths1, im_src1, im_tgt1, st_src1, st_tgt1, r_shared1))
               (VALID: URA.wf (r_shared1 ⋅ r_own ⋅ r_ctx1))
               im_tgt2
               (TGT: fair_update im_tgt1 im_tgt2 (sum_fmap_l (tids_fmap tid ths1))),
        exists o1,
          (<<GENO: geno _ _ RR f_src true r_ctx1 (o1, trigger (Yield) >>= ktr_src) (ktr_tgt tt) (ths1, im_src1, im_tgt2, st_src1, st_tgt1, r_shared1)>>) /\
            (<<STUTTER: wf_stt.(lt) o1 o0>>))
    :
    _geno tid geno RR f_src f_tgt r_ctx0 (o0, trigger (Yield) >>= ktr_src) (trigger (Yield) >>= ktr_tgt) (ths0, im_src0, im_tgt0, st_src0, st_tgt0, r_shared0)

  | geno_yieldL
      f_src f_tgt r_ctx o0
      ths im_src0 im_tgt st_src st_tgt r_shared
      ktr_src itr_tgt
      (GENO: exists im_src1 o1,
          (<<FAIR: fair_update im_src0 im_src1 (sum_fmap_l (tids_fmap tid ths))>>) /\
            (<<GENO: geno _ _ RR true f_tgt r_ctx (o1, ktr_src tt) itr_tgt (ths, im_src1, im_tgt, st_src, st_tgt, r_shared)>>))
    :
    _geno tid geno RR f_src f_tgt r_ctx (o0, trigger (Yield) >>= ktr_src) itr_tgt (ths, im_src0, im_tgt, st_src, st_tgt, r_shared)

  | geno_progress
      r_ctx o
      ths im_src im_tgt st_src st_tgt r_shared
      itr_src itr_tgt
      (GENO: ModSimNoSync.lsim I tid RR false false r_ctx itr_src itr_tgt (ths, im_src, im_tgt, st_src, st_tgt, r_shared))
    :
    _geno tid geno RR true true r_ctx (o, itr_src) itr_tgt (ths, im_src, im_tgt, st_src, st_tgt, r_shared)
  .

  Definition geno (tid: thread_id)
             R_src R_tgt (RR: R_src -> R_tgt -> URA.car -> shared_rel):
    bool -> bool -> URA.car -> (wf_stt.(T) * itree srcE R_src) -> itree tgtE R_tgt -> shared_rel :=
    pind9 (_geno tid) top9 R_src R_tgt RR.

  Lemma geno_mon tid: monotone9 (_geno tid).
  Proof.
    ii. inv IN; try (econs; eauto; fail).
    { des. econs; eauto. }
    { des. econs; eauto. }
    { econs; eauto. i. eapply LE. eapply GENO. eauto. }
    { econs; eauto. i. specialize (GENO _ _ _ _ _ _ _ INV0 VALID0 _ TGT). des. esplits; eauto. }
    { des. econs; esplits; eauto. }
  Qed.

  Local Hint Constructors _geno: core.
  Local Hint Unfold geno: core.
  Local Hint Resolve geno_mon: paco.

  Lemma geno_ord_weak
        tid R0 R1 (LRR: R0 -> R1 -> URA.car -> shared_rel)
        ps pt r_ctx src tgt (shr: shared) o0 o1
        (LT: wf_stt.(lt) o0 o1)
        (GENO: geno tid LRR ps pt r_ctx (o0, src) tgt shr)
    :
    geno tid LRR ps pt r_ctx (o1, src) tgt shr.
  Proof.
    remember (o0, src) as osrc.
    move GENO before tid. revert_until GENO.
    pattern R0, R1, LRR, ps, pt, r_ctx, osrc, tgt, shr.
    revert R0 R1 LRR ps pt r_ctx osrc tgt shr GENO. apply pind9_acc.
    intros rr DEC IH. clear DEC. intros R0 R1 LRR ps pt r_ctx osrc tgt shr GENO.
    i; clarify.
    eapply pind9_unfold in GENO; eauto with paco.
    inv GENO.

    { eapply pind9_fold. econs 1; eauto. }
    { eapply pind9_fold. econs 2; eauto.
      destruct GENO0 as [GENO IND]. eapply IH in IND; eauto. split; ss.
    }
    { eapply pind9_fold. econs 3; eauto.
      des. destruct GENO0 as [GENO IND]. eapply IH in IND; eauto. esplits; eauto.
      split; ss; eauto.
    }
    { eapply pind9_fold. econs 4; eauto.
      destruct GENO0 as [GENO IND]. eapply IH in IND; eauto. split; ss.
    }
    { eapply pind9_fold. econs 5; eauto.
      destruct GENO0 as [GENO IND]. eapply IH in IND; eauto. split; ss.
    }
    { eapply pind9_fold. econs 6; eauto.
      destruct GENO0 as [GENO IND]. eapply IH in IND; eauto. split; ss.
    }
    { eapply pind9_fold. econs 7; eauto. }
    { eapply pind9_fold. econs 8; eauto.
      des. destruct GENO as [GENO IND]. eapply IH in IND; eauto. esplits; eauto.
      split; ss; eauto.
    }

    { eapply pind9_fold. econs 9; eauto.
      destruct GENO0 as [GENO IND]. eapply IH in IND; eauto. split; ss.
    }
    { eapply pind9_fold. econs 10; eauto.
      i. specialize (GENO0 x).
      destruct GENO0 as [GENO IND]. eapply IH in IND; eauto. split; ss.
    }
    { eapply pind9_fold. econs 11; eauto.
      destruct GENO0 as [GENO IND]. eapply IH in IND; eauto. split; ss.
    }
    { eapply pind9_fold. econs 12; eauto.
      destruct GENO0 as [GENO IND]. eapply IH in IND; eauto. split; ss.
    }
    { eapply pind9_fold. econs 13; eauto.
      destruct GENO0 as [GENO IND]. eapply IH in IND; eauto. split; ss.
    }
    { eapply pind9_fold. econs 14; eauto.
      i. specialize (GENO0 _ FAIR).
      destruct GENO0 as [GENO IND]. eapply IH in IND; eauto. split; ss.
    }
    { eapply pind9_fold. econs 15; eauto.
      i. specialize (GENO0 ret).
      destruct GENO0 as [GENO IND]. eapply IH in IND; eauto. split; ss.
    }

    { eapply pind9_fold. econs 16; eauto.
      i. specialize (GENO0 _ _ _ _ _ _ _ INV0 VALID0 _ TGT). des. esplits; eauto.
      destruct GENO as [GENO IND]. eapply IH in IND; eauto. split; ss.
    }

    { eapply pind9_fold. econs 17; eauto.
      des. esplits; eauto.
      eapply upind9_mon; eauto. ss.
    }

    { eapply pind9_fold. econs 18; eauto. }

  Qed.

  Lemma nosync_geno
        tid R0 R1 (RR: R0 -> R1 -> URA.car -> shared_rel)
        ps pt r_ctx src tgt shr
        (LSIM: ModSimNoSync.lsim I tid RR ps pt r_ctx src tgt shr)
    :
    exists o, geno tid RR ps pt r_ctx (o, src) tgt shr.
  Proof.
    punfold LSIM.
    pattern R0, R1, RR, ps, pt, r_ctx, src, tgt, shr.
    revert R0 R1 RR ps pt r_ctx src tgt shr LSIM. apply pind9_acc.
    intros rr DEC IH. clear DEC. intros R0 R1 RR ps pt r_ctx src tgt shr LSIM.
    eapply pind9_unfold in LSIM; eauto with paco.
    set (fzero:= fun _: (A R0 R1) => @ord_tree_base (A R0 R1)). set (one:= ord_tree_cons fzero).
    inv LSIM.

    { exists one. eapply pind9_fold. econs 1; eauto.
      instantiate (1:=fzero (ps, pt, r_ctx, Ret r_src, Ret r_tgt, (ths, im_src, im_tgt, st_src, st_tgt, r_shared))); ss.
    }

    { destruct LSIM0 as [LSIM IND]. eapply IH in IND. des.
      exists o. eapply pind9_fold. econs 2; eauto. split; ss.
    }
    { des. destruct LSIM0 as [LSIM IND]. eapply IH in IND. des.
      exists o. eapply pind9_fold. econs 3; eauto. eexists. split; ss. eauto.
    }
    { destruct LSIM0 as [LSIM IND]. eapply IH in IND. des.
      exists o. eapply pind9_fold. econs 4; eauto. split; ss.
    }
    { destruct LSIM0 as [LSIM IND]. eapply IH in IND. des.
      exists o. eapply pind9_fold. econs 5; auto. split; ss.
    }
    { destruct LSIM0 as [LSIM IND]. eapply IH in IND. des.
      exists o. eapply pind9_fold. econs 6; auto. split; ss.
    }
    { exists one. eapply pind9_fold. econs 7; eauto. }
    { des. destruct LSIM as [LSIM IND]. eapply IH in IND. des.
      exists o. eapply pind9_fold. econs 8; eauto. esplits; eauto. split; ss.
    }

    { destruct LSIM0 as [LSIM IND]. eapply IH in IND. des. exists o.
      eapply pind9_fold. econs 9; eauto. ss.
    }

    { hexploit ord_tree_join.
      { instantiate (2:=A R0 R1).
        instantiate (2:= fun '(ps, pt, rs, src, tgt, shr) => @rr R0 R1 RR ps pt rs src tgt shr).
        i. ss. des_ifs. eapply IH in SAT.
        instantiate (1:= fun '(ps, pt, rs, src, tgt, shr) o =>
                           geno tid RR ps pt rs (o, src) tgt shr).
        eauto.
      }
      intro JOIN. des. exists o1.
      eapply pind9_fold. econs 10.
      i. specialize (LSIM0 x). destruct LSIM0 as [LSIM IND].
      specialize (JOIN (ps, true, r_ctx, src, (ktr_tgt x), (ths, im_src, im_tgt, st_src, st_tgt, r_shared))).
      destruct JOIN; auto. des. split; ss.
      eapply geno_ord_weak; eauto.
    }

    { destruct LSIM0 as [LSIM IND]. eapply IH in IND. des. exists o.
      eapply pind9_fold. econs 11; eauto. ss.
    }
    { destruct LSIM0 as [LSIM IND]. eapply IH in IND. des. exists o.
      eapply pind9_fold. econs 12; eauto. ss.
    }
    { destruct LSIM0 as [LSIM IND]. eapply IH in IND. des. exists o.
      eapply pind9_fold. econs 13; eauto. ss.
    }

    { hexploit ord_tree_join.
      { instantiate (2:=A R0 R1).
        instantiate (2:= fun '(ps, pt, rs, src, tgt, shr) => @rr R0 R1 RR ps pt rs src tgt shr).
        i. ss. des_ifs. eapply IH in SAT.
        instantiate (1:= fun '(ps, pt, rs, src, tgt, shr) o =>
                           geno tid RR ps pt rs (o, src) tgt shr).
        eauto.
      }
      intro JOIN. des. exists o1.
      eapply pind9_fold. econs 14.
      i. specialize (LSIM0 _ FAIR). destruct LSIM0 as [LSIM IND].
      specialize (JOIN (ps, true, r_ctx, src, (ktr_tgt ()), (ths, im_src, im_tgt1, st_src, st_tgt, r_shared))).
      destruct JOIN; auto. des. split; ss.
      eapply geno_ord_weak; eauto.
    }

    { hexploit ord_tree_join.
      { instantiate (2:=A R0 R1).
        instantiate (2:= fun '(ps, pt, rs, src, tgt, shr) => @rr R0 R1 RR ps pt rs src tgt shr).
        i. ss. des_ifs. eapply IH in SAT.
        instantiate (1:= fun '(ps, pt, rs, src, tgt, shr) o =>
                           geno tid RR ps pt rs (o, src) tgt shr).
        eauto.
      }
      intro JOIN. des. exists o1.
      eapply pind9_fold. econs 15.
      i. specialize (LSIM0 ret). destruct LSIM0 as [LSIM IND].
      specialize (JOIN (true, true, r_ctx, ktr_src ret, ktr_tgt ret, (ths, im_src, im_tgt, st_src, st_tgt, r_shared))).
      destruct JOIN; auto. des. split; ss.
      eapply geno_ord_weak; eauto.
    }

    { hexploit ord_tree_join.
      { instantiate (2:=A R0 R1).
        instantiate (2:= fun '(ps, pt, rs, src, tgt, shr) => @rr R0 R1 RR ps pt rs src tgt shr).
        i. ss. des_ifs. eapply IH in SAT.
        instantiate (1:= fun '(ps, pt, rs, src, tgt, shr) o =>
                           geno tid RR ps pt rs (o, src) tgt shr).
        eauto.
      }
      intro JOIN. des. exists o1.
      eapply pind9_fold. econs 16.
      1,2: eauto.
      i. specialize (LSIM0 _ _ _ _ _ _ _ INV0 VALID0 _ TGT). destruct LSIM0 as [LSIM IND].
      specialize (JOIN (ps, true, r_ctx1, (x <- trigger Yield;; ktr_src x), ktr_tgt (), (ths1, im_src1, im_tgt2, st_src1, st_tgt1, r_shared1))).
      destruct JOIN; auto. des. esplits; eauto. split; ss.
    }

    { des. destruct LSIM as [LSIM IND]. eapply IH in IND. des. exists o.
      eapply pind9_fold. econs 17; eauto. esplits; eauto.
      split; ss. eauto.
    }

    { exists one. eapply pind9_fold. econs 18. pclearbot. auto. }

  Qed.

End GENORDER.
#[export] Hint Constructors _geno: core.
#[export] Hint Unfold geno: core.
#[export] Hint Resolve geno_mon: paco.

Section PROOF.

  Context `{M: URA.t}.

  Variable state_src: Type.
  Variable state_tgt: Type.

  Variable _ident_src: ID.
  Let ident_src := @ident_src _ident_src.
  Variable _ident_tgt: ID.
  Let ident_tgt := @ident_tgt _ident_tgt.

  Variable wf_src: WF.
  Variable wf_tgt: WF.

  Let srcE := ((@eventE _ident_src +' cE) +' sE state_src).
  Let tgtE := ((@eventE _ident_tgt +' cE) +' sE state_tgt).

  Let shared :=
    (TIdSet.t *
       (@imap ident_src wf_src) *
       (@imap ident_tgt wf_tgt) *
       state_src *
       state_tgt *
       URA.car)%type.

  Let shared_rel: Type := shared -> Prop.

  Variable I: shared_rel.

  Lemma stutter_ord_weak
          wf_stt tid
          R0 R1 (LRR: R0 -> R1 -> URA.car -> shared_rel)
          ps pt r_ctx src tgt (shr: shared) o0 o1
          (LE: wf_stt.(le) o0 o1)
          (LSIM: ModSimStutter.lsim wf_stt I tid LRR ps pt r_ctx (o0, src) tgt shr)
    :
    ModSimStutter.lsim wf_stt I tid LRR ps pt r_ctx (o1, src) tgt shr.
  Proof.
    destruct LE as [EQ | LT].
    { clarify. }
    revert_until tid. pcofix CIH; i.
    remember (o0, src) as osrc.
    move LSIM before CIH. revert_until LSIM.
    punfold LSIM.
    pattern R0, R1, LRR, ps, pt, r_ctx, osrc, tgt, shr.
    revert R0 R1 LRR ps pt r_ctx osrc tgt shr LSIM. apply pind9_acc.
    intros rr DEC IH. clear DEC. intros R0 R1 LRR ps pt r_ctx osrc tgt shr LSIM.
    i; clarify.
    eapply pind9_unfold in LSIM.
    2:{ eapply ModSimStutter._lsim_mon. }
    inv LSIM.

    { pfold. eapply pind9_fold. econs 1; eauto. }
    { pfold. eapply pind9_fold. econs 2; eauto.
      split; ss. destruct LSIM0 as [LSIM IND]. eapply IH in IND; eauto. punfold IND.
    }
    { pfold. eapply pind9_fold. econs 3; eauto.
      des. exists x.
      split; ss. destruct LSIM0 as [LSIM IND]. eapply IH in IND; eauto. punfold IND.
    }
    { pfold. eapply pind9_fold. econs 4; eauto.
      split; ss. destruct LSIM0 as [LSIM IND]. eapply IH in IND; eauto. punfold IND.
    }
    { pfold. eapply pind9_fold. econs 5; eauto.
      split; ss. destruct LSIM0 as [LSIM IND]. eapply IH in IND; eauto. punfold IND.
    }
    { pfold. eapply pind9_fold. econs 6; eauto.
      split; ss. destruct LSIM0 as [LSIM IND]. eapply IH in IND; eauto. punfold IND.
    }
    { pfold. eapply pind9_fold. econs 7; eauto. }
    { pfold. eapply pind9_fold. econs 8; eauto.
      des. esplits; eauto.
      split; ss. destruct LSIM as [LSIM IND]. eapply IH in IND; eauto. punfold IND.
    }
    { pfold. eapply pind9_fold. econs 9; eauto.
      split; ss. destruct LSIM0 as [LSIM IND]. eapply IH in IND; eauto. punfold IND.
    }
    { pfold. eapply pind9_fold. econs 10; eauto.
      i. specialize (LSIM0 x).
      split; ss. destruct LSIM0 as [LSIM IND]. eapply IH in IND; eauto. punfold IND.
    }
    { pfold. eapply pind9_fold. econs 11; eauto.
      split; ss. destruct LSIM0 as [LSIM IND]. eapply IH in IND; eauto. punfold IND.
    }
    { pfold. eapply pind9_fold. econs 12; eauto.
      split; ss. destruct LSIM0 as [LSIM IND]. eapply IH in IND; eauto. punfold IND.
    }
    { pfold. eapply pind9_fold. econs 13; eauto.
      split; ss. destruct LSIM0 as [LSIM IND]. eapply IH in IND; eauto. punfold IND.
    }
    { pfold. eapply pind9_fold. econs 14; eauto.
      i. specialize (LSIM0 _ FAIR).
      split; ss. destruct LSIM0 as [LSIM IND]. eapply IH in IND; eauto. punfold IND.
    }
    { pfold. eapply pind9_fold. econs 15; eauto.
      i. specialize (LSIM0 ret). pclearbot.
      right. eapply CIH; eauto.
    }

    { pfold. eapply pind9_fold. eapply ModSimStutter.lsim_yieldR; eauto.
      i. hexploit LSIM0; clear LSIM0; eauto; intro LSIM. des. esplits; eauto.
      pclearbot. right. eapply CIH; eauto.
    }

    { pfold. eapply pind9_fold. eapply ModSimStutter.lsim_yieldL; eauto.
      des. esplits; eauto. destruct LSIM as [LSIM IND].
      split; ss. eapply pind9_mon_gen. eapply LSIM.
      - i. eapply __lsim_mon. 2: eapply PR. i. eapply upaco9_mon_bot; eauto.
      - ss.
    }

    { pfold. eapply pind9_fold. eapply ModSimStutter.lsim_progress.
      pclearbot. right. eapply CIH; eauto.
    }

  Qed.

  Definition lift_wf (wf: WF): WF := sum_WF (sum_WF wf wf) wf.

  Definition mk_o (wf: WF) (w: wf.(T)) R (o: wf.(T)) (ps: bool) (itr_src: itree srcE R):
    (lift_wf wf).(T) :=
    if ps
    then match (observe itr_src) with
         | VisF ((|Yield)|)%sum _ => (inl (inr o))
         | _ => (inr w)
         end
    else match (observe itr_src) with
         | VisF ((|Yield)|)%sum _ => (inl (inl o))
         | _ => (inr w)
         end.

  Let A R0 R1 := (bool * bool * URA.car * (itree srcE R0) * (itree tgtE R1) * shared)%type.
  Let wf_ot R0 R1 := @ord_tree_WF (A R0 R1).
  Let wf_stt R0 R1 := lift_wf (@wf_ot R0 R1).

  Lemma nosync_implies_stutter
        tid
        R0 R1 (LRR: R0 -> R1 -> URA.car -> shared_rel)
        ps pt r_ctx src tgt
        (shr: shared)
        (LSIM: ModSimNoSync.lsim I tid LRR ps pt r_ctx src tgt shr)
    :
    exists (o: (@wf_stt R0 R1).(T)),
      ModSimStutter.lsim (@wf_stt R0 R1) I tid LRR ps pt r_ctx (o, src) tgt shr.
  Proof.
    eapply nosync_geno in LSIM. des.
    exists (mk_o (@wf_ot R0 R1) (@ord_tree_base _) o ps src).
    revert_until R1. ginit. gcofix CIH; i.
    remember (o, src) as osrc.
    remember R0 as _R0. remember R1 as _R1.
    move R0 after CIH. move R1 after CIH. move CIH before tid.
    remember src as _src. remember tgt as _tgt. remember o as _o.
    assert (__src: itree srcE R0).
    { rewrite <- Heq_R0. exact src. }
    assert (Heq_src_: __src = src).

    rewrite Heq_R0 in src.
    setoid_rewrite HeqR_src in src.
    revert_until HeqR_src. rewrite !HeqR_tgt.
    pattern R_src, R_tgt, LRR, ps, pt, r_ctx, osrc, tgt, shr.
    move LSIM before CIH. revert_until LSIM.
    pattern R_src, R_tgt, LRR, ps, pt, r_ctx, osrc, tgt, shr.
    revert R0 R1 LRR ps pt r_ctx osrc tgt shr LSIM. apply pind9_acc.
    intros rr DEC IH. clear DEC. intros R0 R1 LRR ps pt r_ctx osrc tgt shr LSIM.
    intros src o Eosrc. clarify.
    eapply pind9_unfold in LSIM; eauto with paco.
    inv LSIM.

    remember (o, src) as osrc. ss.
    move LSIM before tid. revert_until LSIM.
    pattern R0, R1, LRR, ps, pt, r_ctx, osrc, tgt, shr.
    revert R0 R1 LRR ps pt r_ctx osrc tgt shr LSIM. apply pind9_acc.
    intros rr DEC IH. clear DEC. intros R0 R1 LRR ps pt r_ctx osrc tgt shr LSIM.
    intros src o Eosrc. clarify.
    eapply pind9_unfold in LSIM; eauto with paco.
    inv LSIM.

    { unfold mk_o. des_ifs.
      - pfold. eapply pind9_fold. econs 1; eauto.
        instantiate (1:=inl (inl o1)). ss. econs 3.
      - pfold. eapply pind9_fold. econs 1; eauto.
        instantiate (1:=inl (inl o1)). ss. econs 3.
    }

    { destruct GENO as [GENO IND]. eapply IH in IND; eauto.
      pfold. eapply pind9_fold. econs 2; eauto.
      split; ss.
      eapply stutter_ord_weak in IND. punfold IND.
      unfold mk_o. des_ifs; try reflexivity.
      - right. ss. econs 3.
      - right. ss. econs 3.
    }
    { des. destruct GENO as [GENO IND]. eapply IH in IND; eauto.
      pfold. eapply pind9_fold. econs 3; eauto. exists x.
      split; ss.
      eapply stutter_ord_weak in IND. punfold IND.
      unfold mk_o. des_ifs; try reflexivity.
      - right. ss. econs 3.
      - right. ss. econs 3.
    }
    { destruct GENO as [GENO IND]. eapply IH in IND; eauto.
      pfold. eapply pind9_fold. econs 4; eauto.
      split; ss.
      eapply stutter_ord_weak in IND. punfold IND.
      unfold mk_o. des_ifs; try reflexivity.
      - right. ss. econs 3.
      - right. ss. econs 3.
    }
    { destruct GENO as [GENO IND]. eapply IH in IND; eauto.
      pfold. eapply pind9_fold. econs 5; eauto.
      split; ss.
      eapply stutter_ord_weak in IND. punfold IND.
      unfold mk_o. des_ifs; try reflexivity.
      - right. ss. econs 3.
      - right. ss. econs 3.
    }
    { destruct GENO as [GENO IND]. eapply IH in IND; eauto.
      pfold. eapply pind9_fold. econs 6; eauto.
      split; ss.
      eapply stutter_ord_weak in IND. punfold IND.
      unfold mk_o. des_ifs; try reflexivity.
      - right. ss. econs 3.
      - right. ss. econs 3.
    }
    { pfold. eapply pind9_fold. econs 7; eauto. }
    { des. destruct GENO0 as [GENO IND]. eapply IH in IND; eauto.
      pfold. eapply pind9_fold. econs 8; eauto. esplits; eauto.
      split; ss.
      eapply stutter_ord_weak in IND. punfold IND.
      unfold mk_o. des_ifs; try reflexivity.
      - right. ss. econs 3.
      - right. ss. econs 3.
    }

    { destruct GENO as [GENO IND]. eapply IH in IND; eauto.
      pfold. eapply pind9_fold. econs 9; eauto.
      split; ss.
      eapply stutter_ord_weak in IND. punfold IND.
      left; auto.
    }
    { pfold. eapply pind9_fold. econs 10; eauto. i. specialize (GENO x).
      destruct GENO as [GENO IND]. eapply IH in IND; eauto.
      split; ss.
      eapply stutter_ord_weak in IND. punfold IND.
      left; auto.
    }
    { destruct GENO as [GENO IND]. eapply IH in IND; eauto.
      pfold. eapply pind9_fold. econs 11; eauto.
      split; ss.
      eapply stutter_ord_weak in IND. punfold IND.
      left; auto.
    }
    { destruct GENO as [GENO IND]. eapply IH in IND; eauto.
      pfold. eapply pind9_fold. econs 12; eauto.
      split; ss.
      eapply stutter_ord_weak in IND. punfold IND.
      left; auto.
    }
    { destruct GENO as [GENO IND]. eapply IH in IND; eauto.
      pfold. eapply pind9_fold. econs 13; eauto.
      split; ss.
      eapply stutter_ord_weak in IND. punfold IND.
      left; auto.
    }
    { pfold. eapply pind9_fold. econs 14; eauto. i. specialize (GENO _ FAIR).
      destruct GENO as [GENO IND]. eapply IH in IND; eauto.
      split; ss.
      eapply stutter_ord_weak in IND. punfold IND.
      left; auto.
    }

    { pfold. eapply pind9_fold. econs 15; eauto. i. specialize (GENO ret).
      destruct GENO as [GENO IND]. eapply IH in IND; eauto.
      eapply stutter_ord_weak in IND. punfold IND.
      unfold mk_o. ss. des_ifs; try reflexivity.
      - right. ss. econs 3.
      - right. ss. econs 3.
    }

    { pfold. eapply pind9_fold. econs 16; eauto. i.
      specialize (GENO _ _ _ _ _ _ _ INV0 VALID0 _ TGT). des.
      destruct GENO0 as [GENO IND]. eapply IH in IND; eauto.
      esplits. left. eapply ModSimStutter.lsim_reset_prog. eauto. 1,2: ss.
      unfold mk_o; ss. rewrite !bind_trigger. ss.
      des_ifs.
      - econs 1. econs 2. auto.
      - econs 1. econs 1. auto.
    }

    { des. destruct GENO0 as [GENO IND]. eapply IH in IND; eauto.
      pfold. eapply pind9_fold. econs 17; eauto. esplits; eauto.
      split; ss. punfold IND.
    }

    { eapply nosync_geno in GENO. des.
      eapply stutter_ord_weak. instantiate (1:=mk_o o0 false src).
      { ss. des_ifs; try reflexivity. right. ss. econs 1. econs 3. }
      pfold. eapply pind9_fold. econs 18.
      right.
      (*TODO*)
      eapply geno_ord_weak in GENO. instantiate (1:=mk_o o true src) in GENO.

      pclearbot. auto. }

  Qed.

End PROOF.

