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
    ktree (programE ident t) (TView.t * Loc.t * Ordering.t) (TView.t * Const.t) :=
    fun '(tvw0, loc, ord) =>
      msc <- trigger (Get id);;
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
    ktree (programE ident t) (TView.t * Loc.t * Const.t * Ordering.t) (TView.t) :=
    fun '(tvw0, loc, val, ord) =>
      msc <- trigger (Get id);;
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
    ktree (programE ident t) (TView.t * Loc.t * Const.t * Ordering.t * Ordering.t) (TView.t * Const.t) :=
    fun '(tvw0, loc, addendum, ordr, ordw) =>
      msc <- trigger (Get id);;
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
