From sflib Require Import sflib.
From Fairness Require Import PCM IProp IPM SCM Weakest.

Section SPEC.

  Context `{Σ: GRA.t}.

  Variable ident_src: ID.
  Variable ident_tgt: ID.
  Variable state_src: Type.
  Variable state_tgt: Type.

  Variable p_mem : Prism.t ident_tgt SCMem.val.
  Variable l_mem : Lens.t state_tgt SCMem.t.
  Let emb_mem := plmap p_mem l_mem.

  Variable Invs: list iProp.

  Context `{MONORA: @GRA.inG monoRA Σ}.
  Context `{THDRA: @GRA.inG ThreadRA Σ}.
  Context `{IDENTSRC: @GRA.inG (identSrcRA ident_src) Σ}.
  Context `{IDENTTGT: @GRA.inG (identTgtRA ident_tgt) Σ}.
  Context `{OBLGRA: @GRA.inG ObligationRA.t Σ}.
  Context `{ARROWRA: @GRA.inG (ArrowRA ident_tgt) Σ}.
  Context `{EDGERA: @GRA.inG EdgeRA Σ}.
  Context `{ONESHOTRA: @GRA.inG (@FiniteMap.t (OneShot.t unit)) Σ}.
  Context `{MEMRA: @GRA.inG memRA Σ}.

  Variable SI_src : state_src -> iProp.
  Variable SI_tgt : state_tgt -> iProp.

  Context `{MEM_VI : @ViewInterp Σ _ _ l_mem SI_tgt memory_black}.

  Lemma alloc_fun_spec
    sz
    tid E r g R_src R_tgt (Q : R_src -> R_tgt -> iProp)
    itr_src ktr_tgt
    :
    (∀ ℓ, points_tos ℓ (repeat (SCMem.val_nat 0) sz) -∗ stsim Invs SI_src SI_tgt tid E r g Q itr_src (ktr_tgt ℓ))
    ⊢
    stsim Invs SI_src SI_tgt tid E r g Q
      itr_src
      (ℓ <- map_event emb_mem (SCMem.alloc_fun sz);; ktr_tgt ℓ).
  Proof.
    unfold SCMem.alloc_fun. rewrite map_event_trigger. grind.
    iIntros "H". iApply stsim_view_getR. iSplit.
    { instantiate (1 := fun _ => True%I). iIntros. ss. }
    iIntros (m0 _). destruct (SCMem.alloc m0 sz) as [m1 ℓ] eqn: Heq.
    rewrite map_event_trigger. rewrite map_event_ret. rewrite put_rmw. grind.
    iApply stsim_view_rmwR. iIntros (m_) "M".
    iPoseProof (memory_ra_alloc Heq) as "MM".
  Admitted.

  Lemma store_fun_spec : True.
  Admitted.

  Lemma load_fun_spec
    ℓ v
    tid E r g R_src R_tgt (Q : R_src -> R_tgt -> iProp)
    itr_src ktr_tgt
    :
    points_to ℓ v ∧ stsim Invs SI_src SI_tgt tid E r g Q itr_src (ktr_tgt v)
    ⊢
    stsim Invs SI_src SI_tgt tid E r g Q
      itr_src
      (x <- map_event emb_mem (SCMem.load_fun ℓ);; ktr_tgt x).
  Proof.
    unfold SCMem.load_fun. rewrite map_event_trigger. grind.
    iIntros "H". iApply stsim_view_getR. iSplit.
    - instantiate (1 := fun m => ⌜SCMem.load m ℓ = Some v⌝%I).
      iDestruct "H" as "[H _]". iIntros (?) "M".
      iPoseProof (memory_ra_load with "M H") as "[G _]".
      iFrame.
    - iDestruct "H" as "[_ H]". iIntros. rewrite H. grind.
      rewrite map_event_ret. grind.
  Qed.

  Lemma faa_fun_spec : True.
  Admitted.

  Lemma cas_fun_spec : True.
  Admitted.

  Lemma cas_weak_fun_spec : True.
  Admitted.

  Lemma compare_fun_spec : True.
  Admitted.

End SPEC.
