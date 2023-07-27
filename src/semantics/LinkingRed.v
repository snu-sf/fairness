From Fairness Require Export Linking.
From Fairness Require Export Red IRed2.

(* close_itree *)



#[export] Instance red_close_itree_ext omd md R (itr: itree (threadE (Mod.ident omd) (Mod.state omd)) R)
  : red_db itree_unfold (OMod.close_itree omd md itr) :=
  mk_red_db _ _ (@close_itree_ext omd md R itr) itr (inr itree_unfold).

#[export] Instance red_close_itree_bind omd md A B
 (itr : itree (threadE (Mod.ident omd) (Mod.state omd)) A)
 (ktr : A -> itree (threadE (Mod.ident omd) (Mod.state omd)) B)
  : red_db itree_unfold (OMod.close_itree omd md (itr >>= ktr)) :=
  mk_red_db _ _ (@close_itree_bind omd md A B itr ktr) tt (inl _continue).

#[export] Instance red_close_itree_tau omd md R
 (itr : itree (threadE (Mod.ident omd) (Mod.state omd)) R)
  : red_db itree_unfold (OMod.close_itree omd md (tau;;itr)) :=
  mk_red_db _ _ close_itree_tau tt (inl _break).

#[export] Instance red_close_itree_ret omd md R (r: R)
  : red_db itree_unfold (OMod.close_itree omd md (Ret r)) :=
  mk_red_db _ _ (@close_itree_ret omd md R r) tt (inl _continue).

#[export] Instance red_close_itree_trigger_eventE2 omd md X (ee: eventE X)
  : red_db itree_unfold (OMod.close_itree omd md (trigger ee)) :=
  mk_red_db _ _ (@close_itree_trigger_eventE2 omd md X ee) tt (inl _break).

#[export] Instance red_close_itree_trigger_cE2 omd md X (ce: cE X)
  : red_db itree_unfold (OMod.close_itree omd md (trigger ce)) :=
  mk_red_db _ _ (@close_itree_trigger_cE2 omd md X ce) tt (inl _break).

#[export] Instance red_close_itree_trigger_state omd md R X
 (run : Mod.state omd -> Mod.state omd * X)
 (ktr : X -> itree (threadE (Mod.ident omd) (Mod.state omd)) R)
  : red_db itree_unfold (OMod.close_itree omd md (trigger (State run) >>= ktr)) :=
  mk_red_db _ _ (@close_itree_trigger_state omd md R X run ktr) tt (inl _break).

#[export] Instance red_close_itree_trigger_get omd md R X
 (p : Mod.state omd -> X)
 (ktr : X -> itree (threadE (Mod.ident omd) (Mod.state omd)) R)
  : red_db itree_unfold (OMod.close_itree omd md (trigger (Get p) >>= ktr)) :=
  mk_red_db _ _ (@close_itree_trigger_get omd md R X p ktr) tt (inl _break).

#[export] Instance red_close_itree_UB omd md R
  : red_db itree_unfold (OMod.close_itree omd md (UB: itree _ R)) :=
  mk_red_db _ _ (@close_itree_UB omd md R) tt (inl _break).

#[export] Instance red_close_itree_unwrap omd md X (x: option X)
  : red_db itree_unfold (OMod.close_itree omd md (unwrap x)) :=
  mk_red_db _ _ (@close_itree_unwrap omd md X x) tt (inl _continue).


(* map_event *)

#[export] Instance red_map_event_ext ident ident' state state'
 (p: Prism.t ident' ident)
 (l : Lens.t state' state)
 R (itr: itree _ R)
  : red_db itree_unfold (map_event (plmap p l) itr) :=
  mk_red_db _ _ (@map_event_plmap_ext ident ident' state state' p l R itr) itr (inr itree_unfold).

#[export] Instance red_map_event_bind E1 E2 (embed: forall X, E1 X -> E2 X)
 A B
 (itr : itree E1 A)
 (ktr : A -> itree E1 B)
  : red_db itree_unfold (map_event embed (itr >>= ktr)) :=
  mk_red_db _ _ (@map_event_bind E1 E2 embed A B itr ktr) tt (inl _continue).

#[export] Instance red_map_event_tau E1 E2 (embed: forall X, E1 X -> E2 X) R
 (itr : itree E1 R)
  : red_db itree_unfold (map_event embed (tau;;itr)) :=
  mk_red_db _ _ (@map_event_tau E1 E2 embed R itr) tt (inl _break).

#[export] Instance red_map_event_ret E1 E2 (embed: forall X, E1 X -> E2 X) R (r: R)
  : red_db itree_unfold (map_event embed (Ret r)) :=
  mk_red_db _ _ (@map_event_ret E1 E2 embed R r) tt (inl _continue).

#[export] Instance red_map_event_UB ident ident' state state'
 (p: Prism.t ident' ident)
 (l : Lens.t state' state)
 R
  : red_db itree_unfold (map_event (plmap p l) (UB: itree _ R)) :=
  mk_red_db _ _ (@map_event_plmap_UB ident ident' state state' p l R) tt (inl _break).

#[export] Instance red_map_event_unwrap ident ident' state state'
 (p: Prism.t ident' ident)
 (l : Lens.t state' state)
 R (x: option R)
  : red_db itree_unfold (map_event (plmap p l) (unwrap x)) :=
  mk_red_db _ _ (@map_event_plmap_unwrap ident ident' state state' p l R x) tt (inl _continue).

#[export] Instance red_map_event_plmap_eventE_nocont ident ident' state state'
 (p: Prism.t ident' ident)
 (l : Lens.t state' state)
 X (e: eventE X)
  : red_db itree_unfold (map_event (plmap p l) (trigger e)) :=
  mk_red_db _ _ (@map_event_plmap_eventE_nocont ident ident' state state' p l X e) tt (inl _break).

#[export] Instance red_map_event_plmap_cE_nocont ident ident' state state'
 (p: Prism.t ident' ident)
 (l : Lens.t state' state)
 X (e: cE X)
  : red_db itree_unfold (map_event (plmap p l) (trigger e)) :=
  mk_red_db _ _ (@map_event_plmap_cE_nocont ident ident' state state' p l X e) tt (inl _break).

#[export] Instance red_map_event_plmap_state_nocont ident ident' state state'
 (p: Prism.t ident' ident)
 (l : Lens.t state' state)
 X (run: state -> state * X)
  : red_db itree_unfold (map_event (plmap p l) (trigger (State run))) :=
  mk_red_db _ _ (@map_event_plmap_state_nocont ident ident' state state' p l X run) tt (inl _break).

#[export] Instance red_map_event_plmap_get_nocont ident ident' state state'
 (p: Prism.t ident' ident)
 (l : Lens.t state' state)
 X (pr: state -> X)
  : red_db itree_unfold (map_event (plmap p l) (trigger (Get pr))) :=
  mk_red_db _ _ (@map_event_plmap_get_nocont ident ident' state state' p l X pr) tt (inl _break).

#[export] Instance red_map_event_plmap_modify_nocont ident ident' state state'
 (p: Prism.t ident' ident)
 (l : Lens.t state' state)
 (f: state -> state)
  : red_db itree_unfold (map_event (plmap p l) (trigger (Modify f))) :=
  mk_red_db _ _ (@map_event_plmap_modify_nocont ident ident' state state' p l f) tt (inl _break).
