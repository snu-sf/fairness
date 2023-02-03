Unset Universe Checking.
From sflib Require Import sflib.
From Paco Require Import paco.
Require Import Coq.Classes.RelationClasses Lia Program.
From Fairness Require Export ITreeLib WFLib FairBeh NatStructs Mod pind.
From PromisingLib Require Import Loc Event.
From PromisingSEQ Require Import Time View TView Cell Memory Local.

Set Implicit Arguments.

Module WMem.
  Record t :=
    mk
      {
        memory:> Memory.t;
        sc: TimeMap.t;
      }.

  Definition init: t := mk Memory.init TimeMap.bot.

  Let ident := (Loc.t * Time.t)%type.

  Definition missed (m: Memory.t) (loc: Loc.t) (ts: Time.t): fmap ident :=
    fun '(loc', ts') =>
      if (Loc.eq_dec loc' loc)
      then
        if (Time.le_lt_dec ts' ts)
        then Flag.emp
        else match Memory.get loc' ts' m with
             | Some (_, Message.concrete _ (Some _)) => Flag.fail
             | _ => Flag.emp
             end
      else Flag.emp.

  Definition load_fun:
    ktree (((@eventE ident) +' cE) +' sE t) (TView.t * Loc.t * Ordering.t) (TView.t * Const.t) :=
    fun '(tvw0, loc, ord) =>
      msc <- trigger (@Get _);;
      '(exist _ (lc1, val, to) _) <- trigger (Choose (sig (fun '(lc1, val, to) =>
                                                             exists released,
                                                               Local.read_step
                                                                 (Local.mk tvw0 Memory.bot)
                                                                 (msc.(memory))
                                                                 loc
                                                                 to
                                                                 val
                                                                 released
                                                                 ord
                                                                 lc1)));;
      _ <- trigger (Fair (missed msc loc to));;
      Ret (lc1.(Local.tview), val)
  .

  Definition store_fun:
    ktree (((@eventE ident) +' cE) +' sE t) (TView.t * Loc.t * Const.t * Ordering.t) (TView.t) :=
    fun '(tvw0, loc, val, ord) =>
      msc <- trigger (@Get _);;
      '(exist _ (lc1, to, sc1, mem1) _) <- trigger (Choose (sig (fun '(lc1, to, sc1, mem1) =>
                                                                   exists from released kind,
                                                                     Local.write_step
                                                                       (Local.mk tvw0 Memory.bot)
                                                                       (msc.(sc))
                                                                       (msc.(memory))
                                                                       loc
                                                                       from
                                                                       to
                                                                       val
                                                                       None
                                                                       released
                                                                       ord
                                                                       lc1
                                                                       sc1
                                                                       mem1
                                                                       kind)));;
      _ <- trigger (Fair (missed msc loc to));;
      _ <- trigger (Put (mk mem1 sc1));;
      Ret (lc1.(Local.tview))
  .

  Definition faa_fun:
    ktree (((@eventE ident) +' cE) +' sE t) (TView.t * Loc.t * Const.t * Ordering.t * Ordering.t) (TView.t * Const.t) :=
    fun '(tvw0, loc, addendum, ordr, ordw) =>
      msc <- trigger (@Get _);;
      '(exist _ (lc1, to, val, sc1, mem1) _) <- trigger (Choose (sig (fun '(lc2, from, val, sc1, mem1) =>
                                                                   exists lc1 to releasedr releasedw kind,


                                                                     (Local.read_step
                                                                        (Local.mk tvw0 Memory.bot)
                                                                        (msc.(memory))
                                                                        loc
                                                                        from
                                                                        val
                                                                        releasedr
                                                                        ordr
                                                                        lc1) /\
                                                                       (Local.write_step
                                                                          lc1
                                                                          (msc.(sc))
                                                                          (msc.(memory))
                                                                          loc
                                                                          from
                                                                          to
                                                                          (Const.add val addendum)
                                                                          releasedr
                                                                          releasedw
                                                                          ordw
                                                                          lc1
                                                                          sc1
                                                                          mem1
                                                                          kind))));;
      _ <- trigger (Fair (missed msc loc to));;
      _ <- trigger (Put (mk mem1 sc1));;
      Ret (lc1.(Local.tview), val)
  .

  Definition mod: Mod.t :=
    Mod.mk
      init
      (Mod.get_funs [("store", Mod.wrap_fun store_fun);
                     ("load", Mod.wrap_fun load_fun);
                     ("faa", Mod.wrap_fun faa_fun)
      ]).
End WMem.

From Fairness Require Import PCM IProp IPM StateRA MonotonePCM.

Section MEMRA.
  Definition wmemRA: URA.t.
  Admitted.

  Context `{WMEMRA: @GRA.inG wmemRA Σ}.

  Definition wmemory_black (m: WMem.t): iProp.
  Admitted.

  Definition wpoints_to (l: Loc.t) (v: Const.t) (vw: TView.t): iProp.
  Admitted.

  Lemma wpoints_to_view_mon l v vw0 vw1
        (LE: TView.le vw0 vw1)
    :
    (wpoints_to l v vw0)
      ⊢
      (wpoints_to l v vw1).
  Proof.
  Admitted.

  Lemma wmemory_ra_load
        m l v0 v1 vw0 vw1
        ord lc1 to released
        (READ: Local.read_step (Local.mk vw0 Memory.bot) m.(WMem.memory) l to v1 released ord lc1)
        (VIEW: vw1 = lc1.(Local.tview))
        (ORD: ord = Ordering.plain)
    :
    (wmemory_black m)
      -∗
      (wpoints_to l v0 vw0)
      -∗
      ((wmemory_black m) ∗ (⌜(TView.le vw0 vw1) /\ (v0 = v1)⌝) ∗ #=>(wpoints_to l v0 vw1)).
  Proof.
  Admitted.

  Lemma wmemory_ra_store
        m0 l v0 vw0 m1 v1 vw1
        lc1 to sc1 mem1 ord from released kind
        (WRITE: Local.write_step (Local.mk vw0 Memory.bot) m0.(WMem.sc) m0.(WMem.memory) l from to v1 None released ord lc1 sc1 mem1 kind)
        (VIEW: vw1 = lc1.(Local.tview))
        (MEM: m1 = WMem.mk mem1 sc1)
        (ORD: ord = Ordering.plain)
    :
    (wmemory_black m0)
      -∗
      (wpoints_to l v0 vw0)
      -∗
      ((⌜TView.le vw0 vw1⌝) ∗ #=>((wmemory_black m1) ∗ (wpoints_to l v1 vw1))).
  Proof.
  Admitted.

End MEMRA.

Global Opaque wpoints_to wmemory_black.
