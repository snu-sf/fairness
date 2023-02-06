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

Section IDENT.

  Definition ID := Type.

  Definition id_prod (A B: ID): ID := (prod A B).
  Definition id_sum (A B: ID): ID := (sum A B).

  (* Class ID : Type := mk_id { id: Type }. *)

  (* Definition id_prod (A B: ID): ID := mk_id (prod A.(id) B.(id)). *)
  (* Definition id_sum (A B: ID): ID := mk_id (sum A.(id) B.(id)). *)

End IDENT.

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
  | Rmw (rmw : S -> S * X) : sE S X
  .

  Variant callE: Type -> Type :=
  | Call (fn: fname) (arg: Any.t): callE Any.t
  .

  Definition Get {S} {X} (p : S -> X) : sE S X := Rmw (fun x => (x, p x)).
  Definition Put {S} (x' : S) : sE S () := Rmw (fun x => (x', tt)).
  Definition Modify {S} (f : S -> S) : sE S () := Rmw (fun x => (f x, tt)).

  Lemma get_rmw {S X} (p : S -> X) : Get p = Rmw (fun x => (x, p x)).
  Proof. reflexivity. Qed.

  Lemma put_rmw {S} (x' : S) : Put x' = Rmw (fun x => (x', tt)).
  Proof. reflexivity. Qed.

  Lemma modify_rmw {S} (f : S -> S) : Modify f = Rmw (fun x => (f x, tt)).
  Proof. reflexivity. Qed.

End EVENTS.

Global Opaque Get.
Global Opaque Put.
Global Opaque Modify.

Notation programE ident State :=
  ((((@eventE ident) +' cE) +' callE) +' sE State).

Section LENS.

  Variable S: Type.
  Variable V: Type.

  Variable l : Lens.t S V.

  Definition lens_rmw X : (V -> V * X) -> (S -> S * X) :=
    fun rmw s =>
      (Lens.set l (fst (rmw (Lens.view l s))) s, snd (rmw (Lens.view l s))).

  Definition map_lens X (se : sE V X) : sE S X :=
    match se with
    | Rmw rmw => Rmw (lens_rmw rmw)
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

  Lemma lens_rmw_compose A B C (l1 : Lens.t A B) (l2 : Lens.t B C) X (rmw : C -> C * X) :
    lens_rmw (l1 ⋅ l2)%lens rmw = lens_rmw l1 (lens_rmw l2 rmw).
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
