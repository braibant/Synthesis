Require TRS. 
Require ATS. 



Require Import TRS. 
Require Import Common. 

Variable mem env1 env2 : list type2. 
Variable lhs : pattern2_vector mem env1. 
Variable w : where_clause env1 env2. 


(* Fixpoint var_lift t G (x : var G t)  : member t (insertAt t' G n) := *)
(*     match x with *)
(*       | HFirst G' => match n return member t (insertAt t' (t :: G') n) with *)
(*                        | O => HNext HFirst *)
(*                        | _ => HFirst *)
(*                      end *)
(*       | HNext t'' G' x' => match n return member t (insertAt t' (t'' :: G') n) with *)
(*                              | O => HNext (HNext x') *)
(*                              | S n' => HNext (liftVar x' t' n') *)
(*                            end *)
(*     end. *)

(* Arguments expr1 : clear implicits.  *)
(* Arguments expr1 E t.  *)

(* Section test.  *)

(*   Definition lift_expr1 t q t' : expr1 q t' -> expr1 (t::q) t'. Admitted.  *)

(*   Definition replacement E t := match t with  *)
(*                                   | Treg t => expr1 E t *)
(*                                   | _ => var E t *)
(*                                 end.  *)

(*   Definition subst E F := dlist (replacement E)          F.  *)
  
(*   Definition apply_subst E F t (s : subst E F) (e : expr1 E t) : expr1 F t.  *)
(*   induction e.  *)
(*   eapply Eprim; eauto.  *)
(*   eapply dlist_map.  *)

(*   refine (let f := fix f t : expr1 F t :=  *)

(*               match t with  *)
                      
                  
(* match e with *)
(*                     | Eprim args res f x => _ *)
(*                     | Econstant c => _ *)
(*                     | Eunion id fl case => _ *)
(*                     | Etuple l v => _ *)
                                     
(*                     | Eget t v => _ *)
(*                     | Eget_regfile size t v n x => _ *)
(*                     | Efirst n t v => _ *)
(*                     | Eisfull n t v => _ *)
(*                     | Eisempty n t v => _ *)
                                         
(*               end *)
(*           in f t e *)
(*          ). *)
(*   Focus 2.  *)
(*   apply Econstant.  *)
(*         induction e.  *)
  
(*   Definition replacement_fst E a : replacement (a :: E) a.  *)
(*   destruct a; try apply var_0.  apply Eget. apply var_0.   *)
(*   Defined.  *)

(*   Definition replacement_lift a E t : replacement E t -> replacement (a::E) t. *)
(*   intros. unfold replacement in *. destruct t.  *)
(*   apply lift_expr1.  *)
(*   apply X.  *)
(*   apply var_S; auto.   *)
(*   apply var_S; auto.  *)
(*   Defined.  *)

  
(*   Definition subst_id E : subst E E.  *)
(*   induction E.   *)
(*   constructor.  *)
(*   constructor.  *)
(*     apply replacement_fst.  *)
(*   unfold subst in IHE.  *)
(*   eapply dlist_map. 2: apply IHE.  *)
(*   apply replacement_lift.  *)
(*   Defined.  *)

(*   Definition build_subst t E F :  *)
(*     pattern1 F t -> @expr1 E t ->  *)
(*     subst E F.  *)
(*   Proof. *)
(*     intros p e.  *)
(*     unfold subst.  *)
(*     inversion p; subst.  *)
(*     constructor. apply e.  *)
(*     constructor.  *)
(*     constructor.  *)
(*     constructor.  *)
(*     admit.  *)
(*     induction X.  *)
(*     constructor. *)
(*     admit.  *)
(*   Defined.  *)

(*   Definition build_subst_where  E F (W : where_clause E F) : subst E F.  *)
(*   Proof.  *)
(*     induction W. *)
(*     apply subst_id.  *)

(*     assert (T := build_subst _ _ _ p e).  *)

(*     Definition subst_combine E F G :  *)
(*       subst (E ++ F) G ->  *)
(*       subst E F ->  *)
(*       subst E G.  *)
(*     intros.  *)
(*     eapply dlist_map in X. apply X.  *)
(*     intros. clear - X1 X0.   *)
(*     unfold replacement in *.  *)
(*     destruct x.  *)
(*     Definition apply_subst :  *)
      
(* Definition t :  dlist (fun t => match t with  *)
(*                                  | Treg t => @expr1 mem t *)
(*                                  | _ => var mem t *)
(*                                end *)
(*                       ) env1.  *)
(* induction lhs. *)
(* apply dlist_nil. *)
(* Definition zob E t : pattern2 E t ->  *)
(*                      dlist (fun t => match t with  *)
(*                                       | Treg t => @expr1 mem t  *)
(*                                       | _ => var mem t *)
(*                                     end) E. *)
(* Admitted.   *)
(* apply zob in p.  *)
(* induction E.  *)
(* simpl.  *)

(* eapply dlist_map.  intros. 2:apply IHp.  *)
(* simpl in *.  *)
(* destruct x; auto using var_S, lift_expr1.  *)
(* simpl.  *)

(* constructor. 2: apply IHE.  *)

(* simpl.  *)
(* apply  *)
(* simpl.  *)
(* Definition t : forall t, var env1 (Treg t) -> @expr1 mem t.  *)
(* (* compute the part that depend on the pattern_vector *) *)
(* induction lhs. *)
(* intros.  inversion X. *)
(* intros t' v.  *)

(* Definition test : forall T P E F (t : T),  *)
(*                     (var E t -> P t) ->  *)
(*                     (var F t -> P t) ->  *)
(*                     (var (E ++ F) t -> P t).  *)
(* induction E.  simpl. tauto.  *)
(* simpl. intros. *)
(* induction X1.   *)
(*  tauto. destruct X1.  *)
(* induction  *)

(* simpl.  *)
(* Inductive pattern : list type2 -> list type0 -> Type := *)
(*     Pvar1 : forall t , pattern [Treg (T01 t)] [t]  *)
(*   | Phole1 : forall t, pattern [] [t] *)
(*   | Pconstant : forall c : Common.constant, *)
(*                 pattern [] ([(Common.cst_ty c)]) *)
(*   | Ptuple : forall (E : list type2) (l : list type1), *)
(*                pattern_vector E l -> pattern E (Ttuple l) *)
(*   with pattern_disjunct : list type2 -> type1_id_list -> Type := *)
(*     pattern_disjunct_hd : forall (E : list type2)  *)
(*                              (id : Common.ident) (t : type1) *)
(*                              (q : type1_id_list), *)
(*                            pattern E t -> pattern_disjunct E (id of t :: q) *)
(*   | pattern_disjunct_tl : forall (E : list type2)  *)
(*                              (id : Common.ident) (t : type1) *)
(*                              (q : type1_id_list), *)
(*                            pattern_disjunct E q -> *)
(*                            pattern_disjunct E (id of t :: q) *)
(*   with pattern_vector : list type2 -> list type1 -> Type := *)
(*     pattern_vector_nil : pattern_vector [] [] *)
(*   | pattern_vector_cons : forall (E F : list type2)  *)
(*                             (t : type1) (q : list type1), *)
(*                           pattern E t -> *)
(*                           pattern_vector F q -> *)
(*                           pattern_vector (E ++ F) (t :: q).  *)

(* Inductive type1 : Type := *)
(*     T01 : Common.type0 -> type1 *)
(*   | Ttuple : list type1 -> type1 *)
(*   with type1_id_list : Type := *)
(*     type1_id_list_nil : type1_id_list *)
(*   | type1_id_list_cons : Common.ident -> *)
(*                          type1 -> type1_id_list -> type1_id_list *)

(* Definition V : ATS.transition  *)
