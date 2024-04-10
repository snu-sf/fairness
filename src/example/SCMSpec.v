From sflib Require Import sflib.
From Paco Require Import paco.
From stdpp Require namespaces.
Require Import Coq.Classes.RelationClasses Lia Program.
From Fairness Require Export ITreeLib
     PCM IProp IPM
     Mod Linking SCM Red Weakest FancyUpdate.

Section SPEC.

  Variable ident_src: ID.
  Variable state_src: Type.

  Variable gvars : list nat.
  Variable tgt_mod : Mod.t.

  Context `{Σ: GRA.t}.
  Variable Invs : @InvSet Σ.

  Context `{MONORA: @GRA.inG monoRA Σ}.
  Context `{THDRA: @GRA.inG ThreadRA Σ}.

  Context `{STATESRC: @GRA.inG (stateSrcRA state_src) Σ}.
  Context `{IDENTSRC: @GRA.inG (identSrcRA ident_src) Σ}.

  Context `{STATETGT: @GRA.inG (stateTgtRA (OMod.closed_state tgt_mod (SCMem.mod gvars))) Σ}.
  Context `{IDENTTGT: @GRA.inG (identTgtRA (OMod.closed_ident tgt_mod (SCMem.mod gvars))) Σ}.

  Context `{OBLGRA: @GRA.inG ObligationRA.t Σ}.
  Context `{ARROWRA: @GRA.inG (ArrowRA (OMod.closed_ident tgt_mod (SCMem.mod gvars))) Σ}.
  Context `{EDGERA: @GRA.inG EdgeRA Σ}.
  Context `{ONESHOTRA: @GRA.inG (@FiniteMap.t (OneShot.t unit)) Σ}.

  Context `{MEMRA: @GRA.inG memRA Σ}.

  Context `{COPSETRA : @GRA.inG CoPset.t Σ}.
  Context `{GSETRA : @GRA.inG Gset.t Σ}.
  Context `{INVSETRA : @GRA.inG (InvSetRA Var) Σ}.

(* memory_ra_alloc: *)
(*   ∀ (Σ : GRA.t) (MEMRA : GRA.inG memRA Σ) (m0 : SCMem.t) (sz : nat) (m1 : SCMem.t)  *)
(*     (p : SCMem.val), *)
(*     SCMem.alloc m0 sz = (m1, p) *)
(*     → memory_black m0 ⊢ #=> (memory_black m1 ** points_tos p (repeat (SCMem.val_nat 0) sz)) *)
  Lemma alloc_fun_spec
        sz
        tid E R_src R_tgt (Q : R_src -> R_tgt -> iProp)
        r g ps pt
        itr_src ktr_tgt
        st0 (mem : SCMem.t)
    :
    ((St_tgt (st0, mem))
       -∗
       (∀ l, stsim tid E r g Q ps true itr_src (ktr_tgt l)))
      ⊢
      (stsim tid E r g Q ps pt
             itr_src
             (map_event (OMod.emb_callee tgt_mod (SCMem.mod gvars)) (SCMem.alloc_fun sz) >>= ktr_tgt)).
  Proof.
    (* TODO : Write the spec and prove *)
  Abort.

  Lemma store_fun_spec : True.
    (* TODO : Write the spec and prove *)
  Abort.

  Lemma load_fun_spec
        l v
        tid E R_src R_tgt (Q : R_src -> R_tgt -> iProp)
        r g ps pt
        itr_src ktr_tgt
        st0 mem
    :
    (St_tgt (st0, mem))
      -∗
      (points_to l v)
      -∗
      (St_tgt (st0, mem) -∗ points_to l v -∗ stsim tid E r g Q ps true itr_src (ktr_tgt v))
      -∗
      (stsim tid E r g Q ps pt
             itr_src
             (map_event (OMod.emb_callee tgt_mod (SCMem.mod gvars)) (SCMem.load_fun l) >>= ktr_tgt)).
  Proof.
    (* TODO : prove *)
  Abort.

  Lemma faa_fun_spec : True.
  Abort.

  Lemma cas_fun_spec : True.
  Abort.

  Lemma cas_weak_fun_spec : True.
  Abort.

  Lemma compare_fun_spec : True.
  Abort.

End SPEC.
