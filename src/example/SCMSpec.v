From sflib Require Import sflib.
From Paco Require Import paco.
From stdpp Require namespaces.
Require Import Coq.Classes.RelationClasses Lia Program.
From Fairness Require Export ITreeLib
     PCM IProp IPM
     Mod Linking SCM Red TRed IRed2 LinkingRed Weakest FancyUpdate.


Section SPEC.
  Variable ident_src: ID.
  Variable ident_tgt: ID.
  Variable state_src: Type.
  Variable state_tgt: Type.

  Context `{Σ: GRA.t}.
  Variable Invs : @InvSet Σ.

  Context `{MONORA: @GRA.inG monoRA Σ}.
  Context `{THDRA: @GRA.inG ThreadRA Σ}.
  Context `{STATESRC: @GRA.inG (stateSrcRA state_src) Σ}.
  Context `{STATETGT: @GRA.inG (stateTgtRA state_tgt) Σ}.
  Context `{IDENTSRC: @GRA.inG (identSrcRA ident_src) Σ}.
  Context `{IDENTTGT: @GRA.inG (identTgtRA ident_tgt) Σ}.
  Context `{OBLGRA: @GRA.inG ObligationRA.t Σ}.
  Context `{ARROWRA: @GRA.inG (ArrowRA ident_tgt) Σ}.
  Context `{EDGERA: @GRA.inG EdgeRA Σ}.
  Context `{ONESHOTRA: @GRA.inG (@FiniteMap.t (OneShot.t unit)) Σ}.
  Context `{COPSETRA : @GRA.inG CoPset.t Σ}.
  Context `{GSETRA : @GRA.inG Gset.t Σ}.
  Context `{INVSETRA : @GRA.inG (InvSetRA Var) Σ}.

  Context `{MEMRA: @GRA.inG memRA Σ}.


  Variable p_mem : Prism.t ident_tgt SCMem.val.
  Variable l_mem : Lens.t state_tgt SCMem.t.
  Let emb_mem := plmap p_mem l_mem.

  Ltac lred2 := repeat (prw ltac:(red_tac itree_class) 1 2 0).
  Ltac rred2 := repeat (prw ltac:(red_tac itree_class) 1 1 0).

  Lemma alloc_fun_spec
        sz
        tid E R_src R_tgt (Q : R_src -> R_tgt -> iProp)
        r g ps pt
        itr_src ktr_tgt
    :
    (tgt_interp_as l_mem memory_black)
    -∗
    (∀ l, points_tos l (repeat (SCMem.val_nat 0) sz) -∗ stsim tid E r g Q ps true itr_src (ktr_tgt l))
      -∗
      (stsim tid E r g Q ps pt
             itr_src
             (map_event emb_mem (SCMem.alloc_fun sz) >>= ktr_tgt)).
  Proof.
    unfold SCMem.alloc_fun. iIntros "H K".
    rred2.

  Admitted.

  Lemma store_fun_spec : True.
  Admitted.

  Lemma load_fun_spec
        l v
        tid E R_src R_tgt (Q : R_src -> R_tgt -> iProp)
        r g ps pt
        itr_src ktr_tgt
    :
    (points_to l v ∧ stsim tid E r g Q ps true itr_src (ktr_tgt v))
      -∗
      stsim tid E r g Q ps pt
      itr_src
      (x <- map_event emb_mem (SCMem.load_fun l);; ktr_tgt x).
  Proof.
  Admitted.

  Lemma faa_fun_spec : True.
  Admitted.

  Lemma cas_fun_spec : True.
  Admitted.

  Lemma cas_weak_fun_spec : True.
  Admitted.

  Lemma compare_fun_spec : True.
  Admitted.

End SPEC.
