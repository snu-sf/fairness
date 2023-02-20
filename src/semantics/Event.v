From sflib Require Import sflib.
From Fairness Require Export ITreeLib Any Optics EventCategory.
From Coq Require Import Classes.RelationClasses Program.
From Coq Require Export Strings.String.

Set Implicit Arguments.

Module Flag.

  Variant t: Type :=
  | fail
  | emp
  | success
  .

  Definition le: t -> t -> Prop :=
    fun f0 f1 =>
      match f0, f1 with
      | fail, _ => True
      | _, fail => False
      | emp, _ => True
      | _, emp => False
      | success, _ => True
      end.

  Global Program Instance le_PreOrder: PreOrder le.
  Next Obligation.
    ii. destruct x; ss.
  Qed.
  Next Obligation.
    ii. destruct x, y, z; ss.
  Qed.

End Flag.

Notation ID := (Type) (only parsing).
Notation id_prod A B := (prod A B) (only parsing).
Notation id_sum A B := (sum A B) (only parsing).

Section EVENT.

  (* Context {Ident: ID}. *)

  Definition fmap (id: ID) := id -> Flag.t.

  Variant eventE {id: ID}: Type -> Type :=
    | Choose (X: Type): eventE X
    | Fair (m: @fmap id): eventE unit
    | Observe (fn: nat) (args: list nat): eventE nat
    | Undefined: eventE void
  .

  Definition UB {id: ID} {E} `{@eventE id -< E} {R}:
    itree E R :=
    f <- trigger Undefined;;
    match (f: void) with end.

  Definition unwrap {id: ID} {E} `{@eventE id -< E} {R}
             (r: option R): itree E R :=
    match r with
    | Some r => Ret r
    | None => UB
    end.

End EVENT.

Notation fname := string (only parsing).
Notation thread_id := nat (only parsing).

Section EVENTS.

  Variant cE: Type -> Type :=
  | Yield: cE unit
  | GetTid: cE thread_id
  (* | Spawn (fn: fname) (args: list Val): cE unit *)
  .

  (* sE is just state monad *)
  Variant sE (S : Type) (X : Type) : Type :=
  | State (run : S -> S * X) : sE S X
  .

  Variant callE: Type -> Type :=
  | Call (fn: fname) (arg: Any.t): callE Any.t
  .

  Definition Get {S} {X} (p : S -> X) : sE S X := State (fun x => (x, p x)).
  Definition Modify {S} (f : S -> S) : sE S () := State (fun x => (f x, tt)).

  Lemma Get_State {S X} (p : S -> X) : Get p = State (fun x => (x, p x)).
  Proof. reflexivity. Qed.

  Lemma Modify_State {S} (f : S -> S) : Modify f = State (fun x => (f x, tt)).
  Proof. reflexivity. Qed.

End EVENTS.

Global Opaque Get.
Global Opaque Modify.
Notation Put x := (Modify (fun _ => x)).

Notation programE ident state :=
  ((((@eventE ident) +' cE) +' callE) +' sE state).

Section LENS.

  Variable S: Type.
  Variable V: Type.

  Variable l : Lens.t S V.

  Definition lens_state X : (V -> V * X) -> (S -> S * X) :=
    fun run s =>
      (Lens.set l (fst (run (Lens.view l s))) s, snd (run (Lens.view l s))).

  Definition map_lens X (se : sE V X) : sE S X :=
    match se with
    | State run => State (lens_state run)
    end.

End LENS.

Section PRISM.

  Variable S : Type.
  Variable A : Type.

  Variable p : Prism.t S A.

  Definition prism_fmap : fmap A -> fmap S :=
    fun fm i =>
      match Prism.preview p i with
      | None => Flag.emp
      | Some j => fm j
      end.

  Definition map_prism X : @eventE A X -> @eventE S X :=
    fun e =>
      match e with
      | Choose X => Choose X
      | Fair fm => Fair (prism_fmap fm)
      | Observe fn args => Observe fn args
      | Undefined => Undefined
      end.

End PRISM.

Section PROGRAM_EVENT.

  Variable ident ident' : Type.
  Variable state state' : Type.

  Variable p : Prism.t ident' ident.
  Variable l : Lens.t state' state.

  Definition plmap X : programE ident state X -> programE ident' state' X.
  Proof.
    intro e. destruct e as [[[e|e]|e]|e].
    - exact ((((map_prism p e)|)|)|)%sum.
    - exact (((|e)|)|)%sum.
    - exact ((|e)|)%sum.
    - exact (|map_lens l e)%sum.
  Defined.

End PROGRAM_EVENT.

Section OPTICS_PROPERTIES.

  Lemma map_lens_State S V (l : Lens.t S V) X (run : V -> V * X) :
    map_lens l (State run) = State (lens_state l run).
  Proof. ss. Qed.

  Lemma map_lens_Get S V (l : Lens.t S V) X (p : V -> X) :
    map_lens l (Get p) = Get (p ∘ Lens.view l).
  Proof.
    rewrite ! Get_State; ss. f_equal. extensionalities s.
    unfold lens_state; ss. rewrite Lens.set_view. ss.
  Qed.

  Lemma map_lens_Modify S V (l : Lens.t S V) (f : V -> V) :
    map_lens l (Modify f) = Modify (Lens.modify l f).
  Proof.
    rewrite ! Modify_State; ss.
  Qed.

  Lemma lens_state_compose A B C (l1 : Lens.t A B) (l2 : Lens.t B C) X (run : C -> C * X) :
    lens_state (l1 ⋅ l2)%lens run = lens_state l1 (lens_state l2 run).
  Proof. ss. Qed.

  Lemma prism_fmap_compose A B C (p1 : Prism.t A B) (p2 : Prism.t B C) fm :
      prism_fmap (p1 ⋅ p2)%prism fm = prism_fmap p1 (prism_fmap p2 fm).
  Proof.
    extensionalities i. unfold prism_fmap, Prism.preview at 1; ss.
    des_ifs.
  Qed.

  Lemma map_lens_compose A B C (l1 : Lens.t A B) (l2 : Lens.t B C) :
    map_lens (l1 ⋅ l2)%lens = (map_lens l1 ∘ map_lens l2)%event.
  Proof. extensionalities X e. destruct e; ss. Qed.

  Lemma map_prism_compose A B C (p1 : Prism.t A B) (p2 : Prism.t B C) :
    map_prism (p1 ⋅ p2)%prism = (map_prism p1 ∘ map_prism p2)%event.
  Proof. extensionalities X e. destruct e; ss. rewrite prism_fmap_compose. ss. Qed.

  Lemma plmap_compose
    I J K A B C (p1 : Prism.t I J) (p2 : Prism.t J K) (l1 : Lens.t A B) (l2 : Lens.t B C)
    : plmap (p1 ⋅ p2)%prism (l1 ⋅ l2)%lens = (plmap p1 l1 ∘ plmap p2 l2)%event.
  Proof.
    extensionalities X e. destruct e as [[[e|e]|e]|e]; ss.
    - rewrite map_prism_compose. ss.
    - rewrite map_lens_compose. ss.
  Qed.

End OPTICS_PROPERTIES.
